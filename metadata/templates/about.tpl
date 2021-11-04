{% extends "base.tpl" %}

{% block headline %}
<font class="first">A</font>rchive of
<font class="first">F</font>ormal
<font class="first">P</font>roofs</h1>
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>

<h2>About</h2>
<p>The Archive of Formal Proofs is a collection of proof libraries, examples,
and larger scientific developments, mechanically checked in the theorem prover
<a href="http://isabelle.in.tum.de/">Isabelle</a>. It is organized in the way
of a scientific journal. <a href="submitting.html">Submissions</a> are
refereed.</p>

<p>The archive repository is hosted on <a href="https://foss.heptapod.net/isa-afp/">Heptapod</a> to
provide easy free access to archive entries. The entries are
tested and maintained continuously against the current stable release of
Isabelle. Older versions of archive entries will remain available.</p>

<h2>Editors</h2>
<p><a name="editors">The editors of the archive are</a></p>
<ul>
<li><a href="http://www.in.tum.de/~eberlm/">Manuel Eberl</a>,
    <a href="http://www.tum.de/">Technische Universit&auml;t M&uuml;nchen</a></li>
<li><a href="http://www.cse.unsw.edu.au/~kleing/">Gerwin Klein</a>,
    <a href="https://proofcraft.systems">Proofcraft</a> &amp; <a href="https://unsw.edu.au">UNSW</a></li>
<li><a href="http://www.andreas-lochbihler.de">Andreas Lochbihler</a>,
    <a href="https://www.digitalasset.com">Digital Asset</a></li>
<li><a href="http://www.in.tum.de/~nipkow/">Tobias Nipkow</a>,
    <a href="http://www.tum.de/">Technische Universit&auml;t M&uuml;nchen</a></li>
<li><a href="http://www.cl.cam.ac.uk/users/lcp/">Larry Paulson</a>,
    <a href="http://www.cam.ac.uk/">University of Cambridge</a></li>
<li><a href="http://cl-informatik.uibk.ac.at/users/thiemann/">René Thiemann</a>,
    <a href="https://www.uibk.ac.at/">University of Innsbruck</a></li>
</ul>

<h2>Why</h2>
<p>We aim to strengthen the community and to foster the development of formal
proofs.</p>

<p>We hope that the archive will provide</p>
<ul>
<li>a resource of knowledge, examples, and libraries for users,</li>
<li>a large and relevant test bed of theories for Isabelle developers, and</li>
<li>a central, citable place for authors to publish their theories</li>
</ul>

<p>We encourage authors of publications that contain Isabelle developments
to make their theories available in the Archive of Formal Proofs and to refer
to the archive entry in their publication. It makes it easier for referees to
check the validity of theorems (all entries in the archive are
mechanically checked), it makes it easier for readers of the publication to
understand details of your development, and it makes it easier to use and
build on your work.</p>

<h2>License</h2>
<p>All entries in the Archive of Formal Proofs are licensed under
a <a href="LICENSE">BSD-style License</a> or
the <a href="http://www.gnu.org/copyleft/lesser.html">GNU LGPL</a>.
This means they are free to download, free to use, free to change, and
free to redistribute with minimal restrictions.</p>

<p>The authors retain their full copyright on their original work,
including their right to make the development available under another,
additional license in the future.</p>


    </td></tr>
  </tbody>
</table>
{% endblock %}

