# pattern for release tarball filename
release_pattern = r"""^afp-(.*)-([0-9\-]{10}).tar.gz$"""

### licenses

# key : (title, url)
#   'key' denotes the short name of the license (e. g. 'LGPL')
#   'title' denotes the display title of the license
#           (e. g. 'GNU Lesser General Public License (LGPL)')
#   'url' contains the url of the license text

licenses = {
    'LGPL': ("GNU Lesser General Public License (LGPL)",
             "http://isa-afp.org/LICENSE.LGPL"),
    'BSD': ("BSD License", "http://isa-afp.org/LICENSE"),
}



### options

class Options(object):
    def __init__(self):
        self.dest_dir = None
        self.metadata_dir = None
        self.thys_dir = None
        self.templates_dir = None
        self.status_file = None
        self.build_download = False
        self.is_devel = False

options = Options()
