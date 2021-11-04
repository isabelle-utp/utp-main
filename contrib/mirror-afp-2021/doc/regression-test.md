Running the regression test
---------------------------

With the AFP set up as a component, run

`isabelle afp_build -A`

to test all entries of the archive with the current Isabelle version
(using the isabelle tool found in your PATH environment variable).

To build large sessions, you will need a 64 bit system and enable 64 bit polyML for instance by adding 

`ML_system_64 = true`

to `$ISABELLE_HOME_USER/etc/preferences`.

To exclude particularly slow sessions, we provide the tags `slow` and
`very_slow`, i.e. if completeness is not required, you could run

`isabelle build -d '$AFP' -a -X slow -j4`

or

`isabelle build -d '$AFP' -a -X very_slow -j4`
