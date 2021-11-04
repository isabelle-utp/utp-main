New Submissions (editors only)
------------------------------

**Mercurial Setup**

As editor you have at least two working copies of the repository:
current release branch and development version.

-   Start by making a directory `~/afp` where the different branches
    will go.
-   To set up the release version, in that directory do (fill in 20XX)

        hg clone ssh://hg@foss.heptapod.net/isa-afp/afp-20XX release

-   for development

        hg clone ssh://hg@foss.heptapod.net/isa-afp/afp-devel devel

You might need to set up ssh keys on Heptapod for this to work. This can
be done under "[Settings/SSH Keys][keys]".

New submissions, changes to the web site and to admin scripts go into
afp/release. About once a week, one of the editors should merge afp-release
into afp-devel, ideally making sure after the merge that the entry works in
the devel version, although that sometimes may be too much and be left for
the authors to fix themselves.

Maintenance and changes on existing submissions all occur in afp/devel
and go properly public with the next Isabelle release (they are only
available as (public) development tar.gz's)

[keys]: https://foss.heptapod.net/profile/keys

**New Submissions**

Everything happens in the release branch `afp/release`.

1.  unpack tar file and move new entry to `afp/release/thys`
2.  make sure there is a `thys/entryname/ROOT` file and add `entryname`
    to `thys/ROOTS`. For the former see the template in
    `thys/Example-Submission/ROOT`. In particular the entry should be in
    chapter AFP, and group `(AFP)`, i.e.

            chapter AFP

            session foo (AFP) = bar +


3.  to check, run in `afp/release/thys`

         ../admin/testall -c <name>

     (be sure to have `ISABELLE_RELEASES` set to the path where Isabelle
    releases are kept, e.g. `/home/proj/isabelle/`)
4.  check license headers: if the authors want the code released under
    LGPL instead of BSD, each file should mention "License: LGPL" in the
    header. We only accept the BSD 3-Clause and LPGPL version 2.1 licenses
    as they are printed in `thys/LICENSE` and `thys/LICENSE.LGPL`.
5.  `hg add` and `hg commit` the new submission
6.  Enter data for author/abstract/index/etc in the file
    `metadata/metadata`. Make sure that your editor uses UTF-8 encoding
    for this file to preserve special characters. If the entry uses a
    new topic or category, add it to metadata/topics (make sure there is
    an empty line at the end of the file).
7.  Generate the new web site by running `../admin/sitegen` .
8.  Use `hg st` and `hg diff` to make sure the generated html makes
    sense. The diff should be small and concern the new entry only.
9. `hg add` and `hg commit` the web site updates.
10. finally, when you are happy with everything, `hg push` all changes
    to Heptapod. The publish script will refuse to publish if the
    changes aren't pushed.
11. to publish the changes to the web, run

         ../admin/publish <name>

    This will check out the Isabelle202X (=release) version of the
    archive from Heptapod, will run the session `name` to generate
    HTML, produce a `.tar.gz` for the archive and for the entry, and
    will update the web pages on the server. The script will ask before
    it copies, so you can check locally if everything is as you want it.

12. That's it. Changes should show up at <http://isa-afp.org>

**New submission in devel**

Although it is a condition of submission that the entry works with the
current stable Isabelle version, occasionally it happens that a
submission does not work with the stable version and cannot be
backported, but is important/good enough to include anyway. In this
case, we can't release the submission on the main web site yet, but we
can add it to the development version of the archive, such that it is at
least available to those who are working with the current Isabelle
development snapshot.

The check-in procedure is the same as for a normal release entry, apart
from the fact that everything happens in the devel instead of release
directory and that the last step (publish) is omitted.

The authors of the entry should be notified that the entry will only
show up on the front page when the next Isabelle version is released.
