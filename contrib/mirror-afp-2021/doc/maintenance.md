Maintaining an Entry in the AFP
-------------------------------

To maintain an entry, you must have write access to the mercurial repository
of the archive at [Heptapod][hepta]. To get access, [sign up at
Heptapod][hepta], and ask one of the [editors][editors] to add you to the AFP
project.

[hepta]: https://foss.heptapod.net
[editors]: http://isa-afp.org/about.html#editors

**Setup:**

 Check out the archive from the mercurial repository with:

    hg clone ssh://hg@foss.heptapod.net/isa-afp/afp-devel

The command above will create a directory `afp-devel` where theories and
additional files are located. You can register an ssh key for your
account at Heptapod under "[Settings/SSH keys][keys]" from the avatar
icon on the top right of the Heptapod interface.

[keys]: https://foss.heptapod.net/profile/keys

**Maintenance:**

Maintaining an entry means making sure that this entry works with the current
Isabelle development version. Maintainers are not supposed to check in and
push new entries. New entries must be reviewed and formally accepted. They
are created on the release branch by the editors.

Depending on the type of the entry, you might want to work in close lock
step with Isabelle development, i.e. fix the entry immediately each time
it breaks, or loosely, i.e. only shortly before a new Isabelle release.
The former is useful for libraries and base entries that are used by
others, the latter is Ok for larger developments and leaf entries.

Small changes might be done by the Isabelle development team for you as
the change is introduced to Isabelle (don't be surprised when your entry
changes slightly over time). You will be notified when an Isabelle
release nears and your entry is broken. You can also choose to receive
an automatic email notification each time your entry breaks (see below).

**Technicalities:**

-   To get the current Isabelle development version, use

        hg clone http://isabelle.in.tum.de/repos/isabelle

    to clone the hg repository. See the README file inside for further
    instructions.

-   Set up your AFP repository as a component by adding
    `init_component "/path_to/afp-devel"` to your
    `~/.isabelle/etc/settings` (or use any other of the component adding
    mechanisms). You need this to get access to the AFP settings and the
    `afp_build` tool.
-   To check if entry `x` works, execute `isabelle afp_build x`. This
    assumes that the command `isabelle` would start up the current
    Isabelle development version.
-   To test all entries, run `isabelle afp_build -A`. (Running the
    script with `-?` will show options and usage information)
-   The changes you make to the mercurial repository will not show up on
    the AFP web pages immediately. This only happens when a new version
    of the archive is released (usually together with Isabelle). Please
    contact one of the editors if you feel there is something that
    should be made available immediately. The changes will show up with
    about 24h delay in the web development snapshot of the AFP.
-   If you make a change that is more than maintenance and that you
    think may be interesting to users of your entry, please add a manual
    change log in the file `afp-devel/metadata/metadata` by adding an
    `[extra-history]` section to your entry. If possible and sensible,
    this log should link to the relevant hg change set(s). See existing
    change logs like the one for JinjaThreads for examples.

**Email Notification:**

 You can receive an automatic email notification if entry `x` breaks by
editing the file `afp-devel/metadata/metadata`:

-   To switch on: find the your entry by searching for its short name, add your email address to `notify = <email addresses>`, hg commit, and hg push the file. Do not change meta data of other entries.
    `notify` is a comma-separated list of email addresses. If the
    entry is not in group `slow` or `very_slow` in the `ROOT` file, the test will run on every push to the repository.
-   To switch off: remove your email address from `notify` and hg
    commit + push the file.
