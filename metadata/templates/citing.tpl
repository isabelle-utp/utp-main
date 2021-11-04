{% extends "base.tpl" %}

{% block headline %}
<font class="first">C</font>iting
<font class="first">E</font>ntries
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>

<p>The following gives an example of the preferred way for citing
entries in the AFP:</p>

<div class="cite">
M. Jaskelioff and S. Merz, Proving the Correctness of Disk
Paxos. <em>Archive of Formal Proofs</em>, June 2005, <a
href="http://isa-afp.org/entries/DiskPaxos.html"><tt>http://isa-afp.org/entries/DiskPaxos.html</tt></a>, Formal proof development.
</div>

<p>
The bibtext entry for this would be:
</p>

<pre class="bibtext">
@article{Jaskelioff-Merz-AFP05,
  author =   {Mauro Jaskelioff and Stephan Merz},
  title =    {Proving the Correctness of Disk Paxos},
  journal =  {Archive of Formal Proofs},
  month =    Jun,
  year =     2005,
  note =     {\url{http://isa-afp.org/entries/DiskPaxos.html}, Formal proof development},
  ISSN =     {2150-914x}
}
</pre>


    </td></tr>
  </tbody>
</table>
{% endblock %}

