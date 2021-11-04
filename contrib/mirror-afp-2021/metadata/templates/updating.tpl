{% extends "base.tpl" %}

{% block headline %}
<font class="first">U</font>pdating
<font class="first">E</font>ntries
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>

<h2>Change</h2>
<p>
The Archive of Formal Proofs is an online resource and therefore
more dynamic than a normal scientific journal. Existing entries
can and do evolve and can also be updated significantly by their
authors.
</p>
<p>
This conflicts with the purpose of archiving and preserving
entries as they have been submitted and with the purpose of
providing a clear and simple interface to readers.
</p>
<p>
The AFP deals with this by synchronizing such updates with
Isabelle releases:
</p>
<ul>
<li>
The entries released and visible on the main site are always
working with the most recent stable Isabelle version and do not
change.
</li>
<li>
In the background, the archive maintainers evolve all entries to
be up to date with the current Isabelle development
version. Authors can contribute changes to this version which is
available as a <a
href="https://foss.heptapod.net/isa-afp/afp-devel/">Heptapod
mercurial repository</a> or as tar.gz package on the <a href="download.html">
download page</a>.
</li>
<li>
When a new Isabelle version is released, the above mentioned
development version of AFP is frozen and turns into the main
version displayed on the front page. Older versions (including the
original submission) of all entries are archived and remain
accessible.
</li>
</ul>

<p>
Significant changes of an entry should be recorded in the metadata of the
entry using the keyword "extra-history". The resulting web page should look
<a href="https://www.isa-afp.org/entries/JinjaThreads.html">something like this</a>.
</p>

<h2>Monotonicity</h2>

<p>
Updating an entry should be mostly monotone: you add new material, but you do
not modify existing material in a major way. Ideally, entries (by other
people) that build on yours should not be affected. Otherwise you have to
liaise with them first. If you intend to carry out major non-monotone
changes, you will need to submit a completely new entry (with a description
of how it relates to the old one). This should be required only very rarely:
AFP entries should be mature enough not to require major changes to their
interface (i.e. the main functions and theorems provided).
</p>

<p>
Major monotone changes, e.g. adding a new concept rather than more results on
existing concepts, may also call for a new entry, but one that builds on the
existing one. This depends on how you would like to organize your entries.
</p>

<h2>If you are an author</h2>

<p>
The above means that if you are an author and would like to
provide a new, better version of your AFP entry, you can do so.
</p>
<p>
To achieve this, you should base your changes on the <a
href="https://foss.heptapod.net/isa-afp/afp-devel/">mercurial
development version</a>
of your AFP entry and test it against the current <a
href="https://isabelle-dev.sketis.net/">Isabelle development
version</a>.
</p>
<p>
If you would like to get write access to your entry in the
mercurial repository or if you need
assistance, please contact the <a href="about.html#editors">editors</a>.
</p>

    </td></tr>
  </tbody>
</table>
{% endblock %}

