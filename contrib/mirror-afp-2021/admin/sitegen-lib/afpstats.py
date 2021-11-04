from datetime import datetime
import os.path
import re

import pytz

#TODO: script relies on checking paths, can this be broken?

def normpath(path, *paths):
    try:
        return os.path.abspath(os.path.join(path, *paths))
    # only happens in python version < 3, non ascii cant be part of a path
    except UnicodeDecodeError:
        return None

class afp_author(object):
    """An AFP author has a name and a web or mail address"""
    def __init__(self, name, address):
        self.name = name
        self.address = address
        self.articles = set()

    def __eq__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

class afp_entry(object):
    """An AFP entry consists of metadata (date, authors, etc), used imports,
       used library imports, paths to thys files and which AFP entries import
       it.
       Not all of this data is present after initialization. See also class
       afp_dict.
       It still relies on information created by the entries-dict in sitegen.py.
       """
    def __init__(self, name, entry_dict, afp_dict, no_index=False):
        self.name = name
        self.afp_dict = afp_dict
        self.path = os.path.join(self.afp_dict.path, self.name)
        self.title = entry_dict['title']
        #TODO: fix author generation, Contributors???
        self.authors = []
        for name, _address in entry_dict['author']:
            self.authors.append(afp_dict.authors[name])
            if not no_index:
                afp_dict.authors[name].articles.add(self)
        self.publish_date = datetime.strptime(entry_dict['date'], "%Y-%m-%d")
        #add UTC timezone to date
        self.publish_date = self.publish_date.replace(tzinfo=pytz.UTC)
        self.abstract = entry_dict['abstract']
        self.license = entry_dict['license']
        self.releases = list(entry_dict['releases'].items())
        self.contributors = (entry_dict['contributors']
                             if entry_dict['contributors'][0][0] else [])
        self.extra = entry_dict['extra']
        self.thys = set()
        self.status = None
        for root, _dirnames, filenames in os.walk(self.path):
            for f in filenames:
                if f.endswith(".thy"):
                    self.thys.add(os.path.join(self.path, root, f))

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def add_loc(self):
        """Count non empty lines in thy-files"""
        self.loc = 0
        for t in self.thys:
            with open(t, 'r') as f:
                for l in f:
                    if l.strip():
                        self.loc += 1

    def add_number_of_lemmas(self):
        """Count number of lemmas, theorems and corollarys"""
        self.lemmas = 0
        for t in self.thys:
            with open(t, 'r') as f:
                for l in f:
                    if l.startswith("lemma") or l.startswith("corollary") or \
                       l.startswith("theorem"):
                        self.lemmas += 1


class afp_dict(dict):
    """The afp_dict contains all afp_entry(s) and a list of afp_author(s).
       To create import/export data for all afp_entrys call build_stats().
    """
    def __init__(self, entries, afp_thys_path, deps_dict, *args):
        dict.__init__(self, *args)
        self.path = normpath(afp_thys_path)
        self.authors = dict()
        # Extra dict for entries which don't show up in index and statistics
        #TODO: document how it works, improve how it works
        self.no_index = dict()
        for entry in entries.values():
            for name, address in entry['author']:
                self.authors[name] = afp_author(name, address)
        for name, entry in entries.items():
            if 'extra' in entry and 'no-index' in entry['extra']:
                self.no_index[name] = afp_entry(name, entry, self,
                                                no_index=True)
            else:
                self[name] = afp_entry(name, entry, self)
        for name in self.no_index:
            del entries[name]
        # all_thys is a dict which maps a thy file to its corresponding AFP
        # entry
        self.all_thys = dict()
        for a in self:
            for t in self[a].thys:
                self.all_thys[t] = self[a]
        for k, a in self.items():
            a.imports = set([self[e] for e in deps_dict[k]['afp_deps']])
            a.lib_imports = set(deps_dict[k]['distrib_deps'])

    def build_stats(self):
        for _k, a in self.items():
            a.add_loc()
            a.add_number_of_lemmas()
            a.used = set()
        for _k, a in self.items():
            for i in a.imports:
                i.used.add(a)
