import json
import terminal
from config import licenses

def parse_extra(extra, **kwargs):
    k, v = extra.split(":", 1)
    return k.strip(), v.strip()

# extracts name and URL from 'name <URL>' as a pair
def parse_name_url(name, entry, key):
    if name.find(" and ") != -1:
        terminal.warn(u"In entry {0}: {1} field contains 'and'. Use ',' to separate names.".format(entry, key))
    url_start = name.find('<')
    url_end = name.find('>')
    if url_start != -1 and url_end != -1:
        url = name[url_start+1:url_end].strip()
        if url.startswith("mailto:"):
            url = url.replace("@", " /at/ ").replace(".", " /dot/ ")
        elif "@" in url:
            terminal.warn(u"In entry {0}: Found mail address without 'mailto:': {1}".format(entry, url))
            url = "mailto:" + url
            url = url.replace("@", " /at/ ").replace(".", " /dot/ ")
        return name[:url_start].strip(), url
    else:
        terminal.warn(u"In entry {0}: no URL specified for {1} {2} ".format(entry, key, name))
        return name, ""

def parse_author(author, entry, key):
    return parse_name_url(author, entry, key)

def parse_contributors(contributor, entry, key):
    if contributor == "":
        return "", None
    else:
        return parse_name_url(contributor, entry, key)

def parse_license(name, **kwargs):
    if name not in licenses:
        raise ValueError(u"Unknown license {0}".format(name))
    return licenses[name]

def parse_email(email, entry, key):
    stripped = email.strip()
    if ' ' in stripped:
        terminal.warn(u"In entry {0}: possibly malformed email in field {1}: '{2}'".format(entry, key, email))
    return stripped

def empty_deps(entries):
    d = {}
    for e in entries:
        d[e] = {}
        d[e]["afp_deps"] = {}
        d[e]["distrib_deps"] = {}
    return d

def read_deps(f):
    #TODO: make code fail safe
    j = json.load(f)
    d = {}
    for entry in j:
        for e in entry:
            d[e] = entry[e]
    return d

# key : (split, processor, default)
#   'key' denotes the key of the key-value pair in the metadata file
#     if it ends with a '*', e. g. 'extra*' and you have two keys 'extra-foo'
#     and 'extra-bar' in your metadata file, you will get:
#       attributes['extra'] == { 'foo': <data>, 'bar': <data> }
#   'split' if False, the value will be treated as a simple string, otherwise
#     it will be split at ','
#   'processor' if defined, the callable will be invoked with each string (or
#     substring if split is 'True') and the result is used
#   'default' is optional and specifies a default value, which will be treated
#     as if it has been read from the file, i. e. is subject to splitting and
#     processing
attribute_schema = {
    'topic': (True, None, None),
    'date': (False, None, None),
    'author': (True, parse_author, None),
    'contributors': (True, parse_contributors, ""),
    'title': (False, None, None),
    'abstract': (False, None, None),
    'license': (False, parse_license, "BSD"),
    'extra*': (False, parse_extra, None),
    'notify': (True, parse_email, "")
}
