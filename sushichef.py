#!/usr/bin/env python

from bs4 import BeautifulSoup
import codecs
from collections import defaultdict, OrderedDict
import copy
import glob
from le_utils.constants import licenses, content_kinds, file_formats
import hashlib
import json
import logging
import ntpath
import os
from pathlib import Path
import re
import requests
from ricecooker.classes.licenses import get_license
from ricecooker.chefs import JsonTreeChef
from ricecooker.utils import downloader, html_writer
from ricecooker.utils.caching import CacheForeverHeuristic, FileCache, CacheControlAdapter
from ricecooker.utils.jsontrees import write_tree_to_json_tree, SUBTITLES_FILE
import time
from urllib.error import URLError
from urllib.parse import urljoin
from utils import if_dir_exists, get_name_from_url, clone_repo, build_path
from utils import if_file_exists, get_video_resolution_format, remove_links
from utils import get_name_from_url_no_ext, get_node_from_channel, get_level_map
from utils import remove_iframes, get_confirm_token, save_response_content
import youtube_dl


BASE_URL = "https://www.youtube.com/user/kkudl/playlists"

DATA_DIR = "chefdata"
COPYRIGHT_HOLDER = "Ahmad Al-Hout"
LICENSE = get_license(licenses.CC_BY, 
        copyright_holder=COPYRIGHT_HOLDER).as_dict()
AUTHOR = "Ahmad Al-Hout"

LOGGER = logging.getLogger()
__logging_handler = logging.StreamHandler()
LOGGER.addHandler(__logging_handler)
LOGGER.setLevel(logging.INFO)

DOWNLOAD_VIDEOS = True
LOAD_VIDEO_LIST = False

sess = requests.Session()
cache = FileCache('.webcache')
basic_adapter = CacheControlAdapter(cache=cache)
forever_adapter = CacheControlAdapter(heuristic=CacheForeverHeuristic(), cache=cache)
sess.mount('http://', basic_adapter)
sess.mount(BASE_URL, forever_adapter)

# Run constants
################################################################################
#CHANNEL_NAME = ""              # Name of channel
#CHANNEL_SOURCE_ID = ""    # Channel's unique id
CHANNEL_DOMAIN = "https://www.youtube.com/channel/UC-2crZOz_UDuwEF-K_nVkOw/playlists" # Who is providing the content
CHANNEL_LANGUAGE = "ar"      # Language of channel
CHANNEL_DESCRIPTION = None                                  # Description of the channel (optional)
CHANNEL_THUMBNAIL = "https://yt3.ggpht.com/a-/AN66SAyssjwwB4_RZHwCrkOd4hHtZYf9pDsXMMrDSg=s288-mo-c-c0xffffffff-rj-k-no"                                    # Local path or url to image file (optional)

# Additional constants
################################################################################

def title_has_numeration(title):
    unit_name_ar = ["الوحده", "الوحدة"]
    for unit_name in unit_name_ar:
        if unit_name in title:
            index = title.find(unit_name)
            match = re.search("(?P<int>\d+)", title)
            if match:
                num = int(match.group("int"))
                return title[index: index+len(unit_name)] + " " + str(num), num
            else:
                return title[index: index+len(unit_name)], None 
    
    numbers = list(map(str, [1,2,3,4,5,6,7,8,9]))
    arab_nums = ["١", "٢", "٣", "٤", "٥"]
    title = title.replace("-", " ")
    for elem in title.split(" "):
        elem = elem.strip()
        for num in numbers:
            if elem == num:
                return title.replace(elem, "").strip(), int(num)
    
    for arab_num in title:
        index = title.find(arab_num)
        if index != -1 and index >= len(title) - 1:
            return title.replace(arab_num, "").strip(), 1
    
    return False, None


def title_patterns(title):
    title = re.sub(' +', ' ' , title)
    pattern01 = r"\d+\-\d+"
    match = re.search(pattern01, title)
    if match:
        index = match.span()
        numbers = title[index[0]:index[1]]
        number_unit = numbers.split("-")[0].strip()
        return "Unit {}".format(number_unit), int(number_unit)
    
    pattern02 = r"\d+\s+\d+"
    match = re.search(pattern02, title)
    if match:
        index = match.span()
        numbers = title[index[0]:index[1]]
        number_unit = int(title[index[1]:].strip())
        return "Unit {}".format(number), number_unit
    
    title_unit, unit_num = title_has_numeration(title)
    if title_unit is not False and unit_num is not None:
        return title_unit, unit_num
    elif title_unit is not False and unit_num is None:
        return title_unit, 1
    else:
        return title, 1


def remove_units_number(title):
    match = re.search(r'\|.*\|', title)
    if match:
        index = match.span()
        new_title = "{} | {}".format(title[:index[0]].strip(), title[index[1]:].strip())
        return new_title.strip()
    return title


def remove_special_case(title):
    title = title.replace("مهارات في علم الرياضيات", "")
    title = title.replace("-", "")
    return title.strip()


class Node(object):
    def __init__(self, title=None, source_id=None, lang="en"):
        self.title = title
        self.source_id = source_id
        self.tree_nodes = OrderedDict()
        self.lang = lang
        self.description = None

    def add_node(self, obj):
        node = obj.to_node()
        if node is not None:
            self.tree_nodes[node["source_id"]] = node

    def to_node(self):
        return dict(
            kind=content_kinds.TOPIC,
            source_id=self.source_id,
            title=self.title,
            description=self.description,
            language=self.lang,
            author=AUTHOR,
            license=LICENSE,
            children=list(self.tree_nodes.values())
        )
    

class Grades(object):
    def __init__(self, *args, **kwargs):
        self.grades = []

    def load(self, filename, auto_parse=False):
        with open(filename, "r") as f:
            grades = json.load(f)
            for grade in grades:
                grade_obj = Grade(grade["title"], grade["source_id"]) 
                for subject in grade["subjects"]:
                    subject_obj = Subject(title=subject["title"], 
                                          source_id=subject["source_id"], 
                                          lang=subject["lang"])
                    subject_obj.auto_generate_lessons(subject["lessons"])
                    grade_obj.add_subject(subject_obj)
                self.grades.append(grade_obj)

    def __iter__(self):
        return iter(self.grades)


class Grade(Node):
    def __init__(self, *args, **kwargs):
        super(Grade, self).__init__(*args, **kwargs)
        self.subjects = []

    def add_subject(self, subject):
        self.subjects.append(subject)


class Subject(Node):
    def __init__(self, *args, **kwargs):
        super(Subject, self).__init__(*args, **kwargs)
        self.lessons = []

    def auto_generate_lessons(self, urls):
        for url in urls:
            youtube = YouTubeResource(url)
            for title, url in youtube.playlist_name_links():
                lesson = Lesson(title=title, source_id=url, lang=self.lang)
                self.lessons.append(lesson)


class Lesson(Node):

    def download(self, download=True, base_path=None):
        youtube = YouTubeResource(self.source_id, lang=self.lang)
        youtube.download(download, base_path)
        #youtube.title = remove_special_case(remove_units_number(youtube.title))
        self.add_node(youtube)

    def to_node(self):
        children = list(self.tree_nodes.values())
        if len(children) == 1:
            return children[0]
        else:
            return dict(
                kind=content_kinds.TOPIC,
                source_id=self.source_id,
                title=self.title,
                description=self.description,
                language=self.lang,
                author=AUTHOR,
                license=LICENSE,
                children=children
            )


class YouTubeResource(object):
    def __init__(self, source_id, name=None, type_name="Youtube", lang="ar", 
            embeded=False, section_title=None):
        LOGGER.info("    + Resource Type: {}".format(type_name))
        LOGGER.info("    - URL: {}".format(source_id))
        self.filename = None
        self.type_name = type_name
        self.filepath = None
        self.name = name
        self.section_title = section_title
        if embeded is True:
            self.source_id = YouTubeResource.transform_embed(source_id)
        else:
            self.source_id = self.clean_url(source_id)
        self.file_format = file_formats.MP4
        self.lang = lang
        self.is_valid = False

    def clean_url(self, url):
        if url[-1] == "/":
            url = url[:-1]
        return url.strip()

    @property
    def title(self):
        return self.name if self.name is not None else self.filename

    @title.setter
    def title(self, v):
        if self.name is not None:
            self.name = v
        else:
            self.filename = v

    @classmethod
    def is_youtube(self, url, get_channel=False):
        youtube = url.find("youtube") != -1 or url.find("youtu.be") != -1
        if get_channel is False:
            youtube = youtube and url.find("user") == -1 and url.find("/c/") == -1
        return youtube

    @classmethod
    def transform_embed(self, url):
        url = "".join(url.split("?")[:1])
        return url.replace("embed/", "watch?v=").strip()

    def playlist_links(self):
        ydl_options = {
                'no_warnings': True,
                'restrictfilenames':True,
                'continuedl': True,
                'quiet': False,
                'format': "bestvideo[height<={maxheight}][ext=mp4]+bestaudio[ext=m4a]/best[height<={maxheight}][ext=mp4]".format(maxheight='480'),
                'noplaylist': False
            }

        playlist_videos_url = []
        with youtube_dl.YoutubeDL(ydl_options) as ydl:
            try:
                ydl.add_default_info_extractors()
                info = ydl.extract_info(self.source_id, download=False)
                for entry in info["entries"]:
                    playlist_videos_url.append(entry["webpage_url"])
            except(youtube_dl.utils.DownloadError, youtube_dl.utils.ContentTooShortError,
                    youtube_dl.utils.ExtractorError) as e:
                LOGGER.info('An error occured ' + str(e))
                LOGGER.info(self.source_id)
            except KeyError as e:
                LOGGER.info(str(e))
        return playlist_videos_url

    def playlist_name_links(self):
        name_url = []
        source_id_hash = hashlib.sha1(self.source_id.encode("utf-8")).hexdigest()
        base_path = build_path([DATA_DIR, CHANNEL_SOURCE_ID])
        videos_url_path = os.path.join(base_path, "{}.json".format(source_id_hash))

        if if_file_exists(videos_url_path) and LOAD_VIDEO_LIST is True:
            with open(videos_url_path, "r") as f:
                name_url = json.load(f)
        else:
            for url in self.playlist_links():
                youtube = YouTubeResource(url)
                info = youtube.get_video_info(None, False)
                name_url.append((info["title"], url))
            with open(videos_url_path, "w") as f:
                json.dump(name_url, f)
        return name_url

    def get_video_info(self, download_to=None, subtitles=True):
        ydl_options = {
                'writesubtitles': subtitles,
                'allsubtitles': subtitles,
                'no_warnings': True,
                'restrictfilenames':True,
                'continuedl': True,
                'quiet': False,
                'format': "bestvideo[height<={maxheight}][ext=mp4]+bestaudio[ext=m4a]/best[height<={maxheight}][ext=mp4]".format(maxheight='480'),
                'outtmpl': '{}/%(id)s'.format(download_to),
                'noplaylist': True
            }

        with youtube_dl.YoutubeDL(ydl_options) as ydl:
            try:
                ydl.add_default_info_extractors()
                info = ydl.extract_info(self.source_id, download=(download_to is not None))
                return info
            except(youtube_dl.utils.DownloadError, youtube_dl.utils.ContentTooShortError,
                    youtube_dl.utils.ExtractorError) as e:
                LOGGER.info('An error occured ' + str(e))
                LOGGER.info(self.source_id)
            except KeyError as e:
                LOGGER.info(str(e))

    def subtitles_dict(self):
        subs = []
        video_info = self.get_video_info()
        if video_info is not None:
            video_id = video_info["id"]
            if 'subtitles' in video_info:
                subtitles_info = video_info["subtitles"]
                for language in subtitles_info.keys():
                    subs.append(dict(file_type=SUBTITLES_FILE, youtube_id=video_id, language=language))
        return subs

    def download(self, download=True, base_path=None):
        if not "watch?" in self.source_id or "/user/" in self.source_id or\
            download is False:
            return

        download_to = build_path([base_path, 'videos'])
        for i in range(4):
            try:
                info = self.get_video_info(download_to=download_to, subtitles=False)
                if info is not None:
                    LOGGER.info("    + Video resolution: {}x{}".format(info.get("width", ""), info.get("height", "")))
                    self.filepath = os.path.join(download_to, "{}.mp4".format(info["id"]))
                    self.filename = info["title"]
                    if self.filepath is not None and os.stat(self.filepath).st_size == 0:
                        LOGGER.info("    + Empty file")
                        self.filepath = None
            except (ValueError, IOError, OSError, URLError, ConnectionResetError) as e:
                LOGGER.info(e)
                LOGGER.info("Download retry")
                time.sleep(.8)
            except (youtube_dl.utils.DownloadError, youtube_dl.utils.ContentTooShortError,
                    youtube_dl.utils.ExtractorError, OSError) as e:
                LOGGER.info("     + An error ocurred, may be the video is not available.")
                return
            except OSError:
                return
            else:
                return

    def to_node(self):
        if self.filepath is not None:
            files = [dict(file_type=content_kinds.VIDEO, path=self.filepath)]
            files += self.subtitles_dict()
            node = dict(
                kind=content_kinds.VIDEO,
                source_id=self.source_id,
                title=self.title,
                description='',
                author=AUTHOR,
                files=files,
                language=self.lang,
                license=LICENSE
            )
            return node


# The chef subclass
################################################################################
class ScienceAhmedChef(JsonTreeChef):
    HOSTNAME = BASE_URL
    TREES_DATA_DIR = os.path.join(DATA_DIR, 'trees')

    def __init__(self):
        build_path([ScienceAhmedChef.TREES_DATA_DIR])
        super(ScienceAhmedChef, self).__init__()

    def pre_run(self, args, options):
        channel_tree = self.scrape(args, options)
        self.write_tree_to_json(channel_tree)

    def lessons(self):
        global CHANNEL_SOURCE_ID
        self.RICECOOKER_JSON_TREE = 'ricecooker_json_tree_professional.json'
        CHANNEL_NAME = "Sciences for Middle School Learners with Mr. Ahmad Al-Hoot (العربيّة)"
        CHANNEL_SOURCE_ID = "sushi-chef-science-ahmed-al-hoot-ar"
        channel_tree = dict(
                source_domain=ScienceAhmedChef.HOSTNAME,
                source_id=CHANNEL_SOURCE_ID,
                title=CHANNEL_NAME,
                description="""Mr. Ahmad Al-Hoot from Egypt provides 13-16 year old learners with video lessons covered in several national curricula across the region in chemistry, biology and geology."""
[:400], #400 UPPER LIMIT characters allowed 
                thumbnail=CHANNEL_THUMBNAIL,
                author=AUTHOR,
                language=CHANNEL_LANGUAGE,
                children=[],
                license=LICENSE,
            )

        grades = Grades()
        grades.load("resources_ar.json", auto_parse=True)
        return channel_tree, grades

    def scrape(self, args, options):
        download_video = options.get('--download-video', "1")
        load_video_list = options.get('--load-video-list', "0")

        if int(download_video) == 0:
            global DOWNLOAD_VIDEOS
            DOWNLOAD_VIDEOS = False

        if int(load_video_list) == 1:
            global LOAD_VIDEO_LIST
            LOAD_VIDEO_LIST = True

        global channel_tree
        channel_tree, grades = self.lessons()

        base_path = [DATA_DIR]
        base_path = build_path(base_path)

        for grade in grades:
            for subject in grade.subjects:
                for lesson in subject.lessons:
                    lesson.download(download=DOWNLOAD_VIDEOS, base_path=base_path)
                    subject.add_node(lesson)
                grade.add_node(subject)
            channel_tree["children"].append(grade.to_node())
        
        return channel_tree

    def write_tree_to_json(self, channel_tree):
        scrape_stage = os.path.join(ScienceAhmedChef.TREES_DATA_DIR, 
                                self.RICECOOKER_JSON_TREE)
        write_tree_to_json_tree(scrape_stage, channel_tree)


# CLI
################################################################################
if __name__ == '__main__':
    chef = ScienceAhmedChef()
    chef.main()
