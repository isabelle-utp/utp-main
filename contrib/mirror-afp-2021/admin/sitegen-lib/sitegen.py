#!/usr/bin/env python

## Dependencies: Python 2.7 or Python 3.5
##
## This script reads a metadata file and generates the topics.html,
## index.html and the entry pages on isa-afp.org.
##
## For meta data documentation see `metadata/README`
## For adding new entries see `doc/editors/new-entry-checkin.html`
##

# Cross-python compatibility
from __future__ import print_function
try:
    import configparser
except ImportError:
    from six.moves import configparser

from collections import OrderedDict
import argparse
from sys import stderr
from functools import partial
from operator import itemgetter
import codecs
import os
import re
import json

from termcolor import colored

# modules
from config import options, release_pattern
import metadata
from terminal import warn, error
import templates
import afpstats

# performs a 'diff' between metadata and the actual filesystem contents
def check_fs(meta_entries, directory):
    def is_fs_entry(e):
        root = os.path.join(directory, e)
        return os.path.isdir(root) and not os.path.exists(os.path.join(root, ".sitegen-ignore"))
    fs_entries = set(e for e in os.listdir(directory) if is_fs_entry(e))
    meta_entries = set(k for k, _ in meta_entries.items())
    # check for entries not existing in filesystem
    for fs_missing in meta_entries - fs_entries:
        print(colored(u"Check: In metadata: entry {0} doesn't exist in filesystem".format(fs_missing),
                      'yellow', attrs=['bold']), file=stderr)
    for meta_missing in fs_entries - meta_entries:
        print(colored(u"Check: In filesystem: entry {0} doesn't exist in metadata".format(meta_missing),
                      'yellow', attrs=['bold']), file=stderr)
    return len(fs_entries ^ meta_entries)

# takes the 'raw' data from metadata file as input and performs:
# * checking of data against attribute_schema
# * defaults for missing keys
# * elimination of extraneous keys
# * splitting at ',' if an array is requested
def validate(entry, attributes):
    sane_attributes = {}
    missing_keys = []
    processed_keys = set()
    for key, (split, processor, default) in metadata.attribute_schema.items():
        if processor is None:
            processor = lambda str, **kwargs: str
        if key.endswith("*"):
            shortkey = key[:len(key)-1]
            result = OrderedDict()
            process = partial(processor, entry=entry, shortkey=shortkey)
            for appkey, str in attributes.items():
                if appkey.startswith(shortkey + "-"):
                    processed_keys.add(appkey)
                    app = appkey[len(shortkey) + 1:]
                    if not split:
                        result[app] = process(str.strip(), appendix=app)
                    else:
                        result[app] = [process(s.strip(), appendix=app) for s in str.split(',')]
            sane_attributes[shortkey] = result
        else:
            process = partial(processor, entry=entry, key=key)
            if default is None and key not in attributes:
                missing_keys.append(key)
                sane_attributes[key] = process("") if not split else []
            else:
                value = attributes[key] if key in attributes else default
                processed_keys.add(key)
                if not split:
                    sane_attributes[key] = process(value)
                else:
                    sane_attributes[key] = [process(s.strip()) for s in value.split(',')]
    if missing_keys:
        error(u"In entry {0}: missing key(s) {1!s}".format(entry, missing_keys), abort = True)

    extraneous_keys = set(attributes.keys()) - processed_keys
    if extraneous_keys:
        warn(u"In entry {0}: unknown key(s) {1!s}. Have you misspelled them?".format(entry, list(extraneous_keys)))

    return sane_attributes

# reads the metadata file and returns a dict mapping each entry to the attributes
# specified. one can rely upon that they conform to the attribute_schema
def parse(filename):
    parser = configparser.RawConfigParser(dict_type=OrderedDict)
    try:
        parser.readfp(codecs.open(filename, encoding='UTF-8', errors='strict'))
        return OrderedDict((sec, validate(sec, dict(parser.items(sec))))
                           for sec in parser.sections())
    except UnicodeDecodeError as ex:
        error(u"In file {0}: invalid UTF-8 character".format(filename), exception=ex, abort=True)

# reads the version file, composed of pairs of version number and release date
def read_versions(filename):
    versions = []
    try:
        with open(filename) as input:
            for line in input:
                try:
                    version, release_date = line.split(" = ")
                except ValueError as ex:
                    error(u"In file {0}: Malformed association {1}".format(filename, line), exception=ex)
                    error("Not processing releases")
                    return []
                else:
                    versions.append((version, release_date.strip()))
    except Exception as ex:
        error(u"In file {0}: error".format(filename), exception=ex)
        error("Not processing releases")
        return []
    else:
        versions.sort(key=itemgetter(1), reverse=True)
        return versions

# reads the list of entry releases (metadata/releases)
def associate_releases(entries, versions, filename):
    for _, attributes in entries.items():
        attributes['releases'] = OrderedDict()
    prog = re.compile(release_pattern)
    warnings = {}
    try:
        with open(filename) as input:
            lines = []
            for line in input:
                line = line.strip()
                result = prog.match(line)
                try:
                    entry, date = result.groups()
                except ValueError as ex:
                    error(u"In file {0}: Malformed release {1}".format(filename, line.replace), exception=ex)
                else:
                    if not entry in entries:
                        if not entry in warnings:
                            warnings[entry] = [line]
                        else:
                            warnings[entry].append(line)
                    else:
                        lines.append((entry, date))
        for entry, releases in warnings.items():
            warn(u"In file {0}: In release(s) {1!s}: Unknown entry {2}".format(filename, releases, entry))
        lines.sort(reverse=True)
        for line in lines:
            found = False
            entry, date = line
            for version_number, version_date in versions:
                if version_date <= date:
                    entry_releases = entries[entry]['releases']
                    if version_number not in entry_releases:
                        entry_releases[version_number] = []
                    entry_releases[version_number].append(date)
                    found = True
                    break
            if not found:
                warn(u"In file {0}: In release {1}: Release date {2} has no matching version".format(filename, line, date))
    except Exception as ex:
        error(u"In file {0}: error".format(filename), exception=ex)
        error("Not processing releases")

def parse_status(filename):
    with open(filename) as input:
        data = json.load(input)

        build_data = data['build_data']
        status = dict()
        for entry in data['entries']:
            status[entry['entry']] = entry['status']

        return build_data, status

def main():
    usage = "sitegen.py [-h] [--templates TEMPLATES_DIR --dest DEST_DIR] [--status STATUS_FILE] [--deps DEPS_FILE] METADATA_DIR THYS_DIR"
    parser = argparse.ArgumentParser(usage=usage)
    parser.add_argument("metadata_dir", metavar="METADATA_DIR", action="store",
                        help="metadata location")
    parser.add_argument("thys_dir", metavar="THYS_DIR", action="store",
                        help="directory with afp entries")
    parser.add_argument("--templates", action="store", dest="templates_dir",
                        help="directory with Jinja2 templates")
    parser.add_argument("--dest", action="store", dest="dest_dir",
                        help="destination dir for generated html files")
    parser.add_argument("--status", action="store", dest="status_file",
                        help="status file location (devel)")
    parser.add_argument("--deps", action="store", dest="deps_file",
                        help="dependencies file location")

    parser.parse_args(namespace=options)
    options.is_devel = options.status_file is not None

    if options.dest_dir and not options.templates_dir:
        error("Please specify templates dir", abort=True)

    # parse metadata
    entries = parse(os.path.join(options.metadata_dir, "metadata"))
    versions = read_versions(os.path.join(options.metadata_dir, "release-dates"))
    associate_releases(entries, versions, os.path.join(options.metadata_dir, "releases"))
    if len(entries) == 0:
        warn("In metadata: No entries found")

    # generate depends-on, used-by entries, lines of code and number of lemmas
    # by using an afp_dict object
    # TODO: error instead of warn
    deps_dict = metadata.empty_deps(entries)
    if options.deps_file:
        with open(options.deps_file, 'r') as df:
            deps_dict = metadata.read_deps(df)
    else:
        warn("No dependencies file specified")

    afp_dict = afpstats.afp_dict(entries, options.thys_dir, deps_dict)
    afp_dict.build_stats()
    for e in entries:
        entries[e]['depends-on'] = list(map(str, afp_dict[e].imports))
        entries[e]['used-by'] = list(map(str, afp_dict[e].used))

    # perform check
    count = check_fs(entries, options.thys_dir)
    output = "Checked directory {0}. Found {1} warnings.".format(options.thys_dir, count)
    color = 'yellow' if count > 0 else 'green'
    print(colored(output, color, attrs=['bold']))

    # perform generation
    if options.dest_dir:
        if options.status_file is not None:
            (build_data, status) = parse_status(options.status_file)
            for a in afp_dict:
                if a in status:
                    afp_dict[a].status = status[a]
                else:
                    afp_dict[a].status = "skipped"
        else:
            build_data = dict()

        builder = templates.Builder(options, entries, afp_dict)
        builder.generate_topics()
        builder.generate_index()
        builder.generate_entries()
        builder.generate_statistics()
        builder.generate_download()
        for s in ["about", "citing", "updating", "search", "submitting",
                  "using"]:
            builder.generate_standard(s + ".html", s + ".tpl")
        builder.generate_rss(30)
        #TODO: look over it one more time
        if options.is_devel:
            builder.generate_status(build_data)

if __name__ == "__main__":
    main()
