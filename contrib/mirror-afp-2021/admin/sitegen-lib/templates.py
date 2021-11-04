from collections import OrderedDict
from itertools import groupby
import os
import datetime
from jinja2 import Environment, FileSystemLoader

import terminal

### topics

class Tree(object):
    def __init__(self):
        self.subtopics = OrderedDict()
        self.entries = []

    def add_topic(self, topic):
        if len(topic) > 0:
            if topic[0] not in self.subtopics:
                tree = Tree()
                self.subtopics[topic[0]] = tree
            else:
                tree = self.subtopics[topic[0]]
            tree.add_topic(topic[1:])

    def add_to_topic(self, topic, entry):
        if len(topic) > 0:
            if topic[0] not in self.subtopics:
                terminal.error(u"In entry {0}: unknown (sub)topic {1}".format(entry, topic), abort=True)
            else:
                self.subtopics[topic[0]].add_to_topic(topic[1:], entry)
        else:
            self.entries.append(entry)

    def __str__(self):
        return self._to_str()

    def _to_str(self, indent=0):
        indent_str = ' ' * indent
        result = indent_str + str(self.entries) + "\n"
        for subtopic, tree in self.subtopics.items():
            result += indent_str
            result += subtopic
            result += "\n"
            result += tree._to_str(indent + 2)
        return result

def read_topics(filename):
    tree = Tree()
    stack = []
    with open(filename) as f:
        for line in f:
            count = 0
            while line[count] == ' ':
                count += 1
            if count % 2:
                raise Exception(u"Illegal indentation at line '{0}'".format(line))
            level = count // 2
            if level <= len(stack):
                stack = stack[0:level]
            else:
                raise Exception(u"Illegal indentation at line '{0}'".format(line))
            stack.append(line[count:len(line)-1])
            tree.add_topic(stack)
    return tree

# for topics page: group entries by topic
def collect_topics(entries, metadata_dir):
    tree = read_topics(os.path.join(metadata_dir, "topics"))
    for entry, attributes in entries.items():
        for topic in attributes['topic']:
            tree.add_to_topic([s.strip() for s in topic.split('/')], entry)
    return tree


class Builder():
    """Contains environment for building webpages from templates"""

    def __init__(self, options, entries, afp_entries):
        self.j2_env = Environment(loader=FileSystemLoader(options.templates_dir),
                                  trim_blocks=True)
        # pass functions to environment for use in templates
        self.prepare_env()
        self.options = options
        #TODO: use only afp_entries
        self.entries = entries
        self.afp_entries = afp_entries

    def prepare_env(self):
        def startswith(value, beginning):
            return value.startswith(beginning)
        def datetimeformat(value, format_str='%Y-%m-%d'):
            return value.strftime(format_str)
        def rfc822(value):
            # Locale could be something different than english, to prevent printing
            # non english months, we use this fix
            month = "Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec".split(" ")[value.month - 1]
            return value.strftime("%d " + month + " %Y %T %z")
        def split(value):
            return value.split()
        def short_month(value):
            return "jan feb mar apr may jun jul aug sep oct nov dec".split(" ")[value - 1]
        self.j2_env.filters['startswith'] = startswith
        self.j2_env.filters['datetimeformat'] = datetimeformat
        self.j2_env.filters['rfc822'] = rfc822
        self.j2_env.filters['split'] = split
        self.j2_env.filters['short_month'] = short_month

    def write_file(self, filename, template, values):
        # UTF-8 hack because of different string handling in python 2 vs 3
        with open(os.path.join(self.options.dest_dir, filename), 'wb') as f:
            f.write(template.render(values).encode('utf8'))

    def generate_standard(self, filename, template_name):
        template = self.j2_env.get_template(template_name)
        self.write_file(filename, template, {})
        terminal.success("Generated {}".format(filename))

    def generate_topics(self):
        tree = collect_topics(self.entries, self.options.metadata_dir)
        template = self.j2_env.get_template("topics.tpl")
        self.write_file("topics.html", template, {'tree': tree})
        terminal.success("Generated topics.html")

    def generate_index(self):
        data = {'is_devel': self.options.is_devel}
        by_year = groupby(sorted(self.afp_entries.values(),
                                 key=lambda e: (e.publish_date, e.name),
                                 reverse=True),
                          key=lambda e: e.publish_date.year)
        data['by_year'] = [(year, list(entries)) for year, entries in by_year]
        template = self.j2_env.get_template("index.tpl")
        self.write_file("index.html", template, data)
        terminal.success("Generated index.html")

    def generate_entries(self):
        counter = 0
        template = self.j2_env.get_template("entry.tpl")
        for name, entry in self.afp_entries.items():
            self.write_file(os.path.join("entries", name + ".html"), template,
                            {'entry': entry, 'is_devel': self.options.is_devel,
                             'ROOT_PATH': '../'})
            counter += 1
        for name, entry in self.afp_entries.no_index.items():
            self.write_file(os.path.join("entries", name + ".html"), template,
                            {'entry': entry, 'is_devel': self.options.is_devel,
                             'ROOT_PATH': '../'})
            counter += 1
        terminal.success("Generated html files for {:d} entries".format(counter))

    def generate_download(self):
        template = self.j2_env.get_template("download.tpl")
        self.write_file("download.html", template,
                        {'is_devel': self.options.is_devel})
        terminal.success("Generated download.html")

    def generate_statistics(self):
        #TODO: simplify with itertools
        # Count loc and articles per year
        articles_years = dict()
        loc_years = dict()
        for article in self.afp_entries.values():
            try:
                articles_years[article.publish_date.year] += 1
                loc_years[article.publish_date.year] += article.loc
            except KeyError:
                articles_years[article.publish_date.year] = 1
                loc_years[article.publish_date.year] = article.loc
        # Count new authors per year
        author_years = dict.fromkeys(articles_years.keys(), 0)
        for author in self.afp_entries.authors.values():
            first_year = min([e.publish_date.year for e in author.articles])
            try:
                author_years[first_year] += 1
            except KeyError:
                author_years[first_year] = 1
        # Build cumulative values
        author_years_cumulative = author_years.copy()
        for y in sorted(articles_years)[1:]:
            articles_years[y] += articles_years[y - 1]
            loc_years[y] += loc_years[y - 1]
            author_years_cumulative[y] += author_years_cumulative[y - 1]
        data = {'entries': self.afp_entries}
        data['num_lemmas'] = sum([a.lemmas for a in self.afp_entries.values()])
        data['num_loc'] = sum([a.loc for a in self.afp_entries.values()])
        data['years'] = sorted(articles_years)
        data['articles_year'] = [articles_years[y] for y
                                 in sorted(articles_years)]
        data['loc_years'] = [round(loc_years[y], -2) for y in sorted(loc_years)]
        data['author_years'] = [author_years[y] for y in sorted(author_years)]
        data['author_years_cumulative'] = [author_years_cumulative[y] for y in
                                           sorted(author_years_cumulative)]
        # Find 10 most imported entries, entries with the same number of
        # imports share one place.
        most_used = sorted([a for a in self.afp_entries.values()],
                           key=lambda x: (-len(x.used), x.name))
        # Show more than 10 articles but not more than necessary
        i = 0
        while (i < 10 or (i + 1 < len(most_used) and
          len(most_used[i].used) == len(most_used[i + 1].used))):
            i += 1
        # Groupby iterators trigger some obscure bug in jinja2
        # https://github.com/pallets/jinja/issues/555
        # So don't use groupby iterator directly and convert to list of lists
        data['most_used'] = [(len_used, list(articles)) for (len_used, articles)
                             in groupby(most_used[:i + 1],
                                        key=lambda x: len(x.used))]
        data['articles_by_time'] = sorted(self.afp_entries.values(),
                                          key=lambda x: x.publish_date)
        data['articles_per_year'] = [(year, list(articles)) for (year, articles)
                                     in groupby(data['articles_by_time'],
                                                key=lambda x: x.publish_date.year)]
        template = self.j2_env.get_template("statistics.tpl")
        self.write_file("statistics.html", template, data)
        terminal.success("Generated statistics.html")

    def generate_status(self, build_data):
        template = self.j2_env.get_template("status.tpl")
        self.write_file("status.html", template,
                        {'entries': [self.afp_entries[e] for e
                                     in sorted(self.afp_entries)],
                         'build_data': build_data})
        terminal.success("Generated status.html")

    def generate_rss(self, num_entries):
        entries = sorted(self.afp_entries.values(),
                         key=lambda e: (e.publish_date, e.name),
                         reverse=True)
        template = self.j2_env.get_template("rss.tpl")
        self.write_file("rss.xml", template, {'entries': entries[:num_entries]})
        terminal.success("Generated rss.xml")
