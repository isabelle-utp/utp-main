{% extends "base.tpl" %}

{% block headline %}
<font class="first">D</font>ownload the <font class="first">A</font>rchive</h1>
{% endblock %}

{% block content %}
<table width="80%" class="descr">
<tbody>
{% if not is_devel %}
<tr><td class="head">
  <b>Current stable version</b> (for current Isabelle release):
</td></tr>
<tr></tr><td class="entry">
    <a href="release/afp-current.tar.gz">afp-current.tar.gz</a>
</td></tr>
{% endif %}

<tr><td class="head">Older stable versions:</td></tr>
<tr><td class="entry">
  Please use the <a href="http://sourceforge.net/projects/afp/files/">
    sourceforge download system</a>
  to access older versions of the archive.
</td></tr>

<tr><td class="head">Mercurial access:</td></tr>

<tr><td class="entry">
  At <a href="https://foss.heptapod.net/isa-afp/afp-devel/">Heptapod</a>
  (development version of the Archive, for the development version of Isabelle)
</td></tr>

<tr><td class="head">How to refer to AFP entries:</td></tr>
<tr><td class="entry">
  You can refer to AFP entries by using the <a href="using.html">AFP as an Isabelle component</a>.</td></tr>

</tbody></table>

<div style="margin-top: 5ex;">
<p>
The AFP repository is hosted on <a href="https://foss.heptapod.net/">Heptapod</a>, a friendly fork of GitLab for Mercurial
provided by <a href="https://octobus.net">Octobus</a> and
<a href="https://www.clever-cloud.com/en/">Clever Cloud</a>.
</p>
<div>
  <img width=400 src="images/octobus+clever.png" alt="Octobus and Clever Cloud logos" />
</div>
</div>
{% endblock %}

