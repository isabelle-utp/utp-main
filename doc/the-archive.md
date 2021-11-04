How the Archive Works
---------------------

Submission is by email to afp-submit@in.tum.de which is distributed to the
archive committee (currently GK, TN, LCP, RT, and ME). One member will assume
responsibility. This includes refereeing the submission, communicating
with the authors, and installing it in the archive. Once it has been
installed, it will be announced on isabelle-users.

**Contents of submission:**

1.  Title, authors, abstract, keywords in plain text (maybe html).
2.  A short name, will become the directory name.
3.  URL or email address of author to display on the web page
4.  A tar file with the theory files, ROOT file, and README or
    document/. The theories should work with the current release.
5.  A notice whether submission is LGPL

**Submission procedure:**

1.  Referee for content and form
2.  Check if submission works with current released version of Isabelle.
3.  Make sure submitter agrees to BSD or LGPL and potentially
    maintenance.
4.  Check submission into repository (as release and development, the editors do this, not the submitters)
5.  Make available on web page
6.  Give out maintenance access to submitter on development version
7.  Announce on isabelle-users

**The archive:** Will initially contain an unstructured collection of
submissions. For each submission there is a page with title, authors,
abstract, keywords, tar.file, and link to the generated html-files for
browsing. It is encouraged and possible to build on other contributions
in the archive. The current released archive should work with the
current released Isabelle version. For later: older archive versions
should remain accessible (but maybe not on the main page).

**Roles:**

-   PC / archive admins (TN, GK, LCP, RT, ME, more)
    -   responsibility: refereeing and initial setup of submissions,
        releases
    -   access: everything
-   submitters (everybody)
    -   responsibility: new submissions, become maintainer if accepted
    -   access: email only
-   maintainers (former submitters, Isabelle team)
    -   responsibility: keep development branch up to date with Isabelle
    -   access: repository read/write
-   user (everybody)
    -   responsibility: use archive
    -   access: download via web page, anonymous hg read only of devel
        version available

**Maintenance:** Usually only on development version of archive (in
mercurial default branch). Released version of existing submissions
should be stable.

**Maintenance responsibility:** Mixed. Simple fixes by the Isabelle team,
anything else by the maintainer of the contribution. The editors will give the
maintainers advanced warning of a new release (after feature freeze) so they
have time to update their contributions.

-   there should be an automated build. Important libraries nightly,
    larger developments less often (weekly?). Maintainers should be able
    to opt in to get email when Isabelle development version breaks
    archive development version.
-   there should be a simple build script so we can test if something
    breaks when we change Isabelle (before we check in)

**Sync between Isabelle and archive:**

-   there is a current release version of the archive (eg. for
    Isabelle2003, it lives from release of Isabelle2003 until
    Isabelle2004)
-   the current release version of the archive will be updated multiple
    times in its life: for each submission and each time a maintainer
    fixes a broken submission (broken e.g. because they did not make the
    Isabelle release deadline).
-   submissions that do not work at release time are dropped from the
    archive (only temporarily until fixed, but things that don't work
    are never visible on the web page).
-   there is a development version of the archive that is not visible on
    the web (or only in the form of a development snapshot). It is in
    the repository and this is where the maintainers work. It becomes
    the release version when a new Isabelle version is released. How
    closely it is in sync with the Isabelle development version is the
    choice of each maintainer in a spectrum from very loose (only fix
    archive submission after Isabelle feature freeze) to very close
    (always fix archive submission after each Isabelle change). Very
    close should be the case for widely used base libraries, very loose
    is ok for standalone developments.

