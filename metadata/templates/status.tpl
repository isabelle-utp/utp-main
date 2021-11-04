{% extends "base.tpl" %}

{% block headline %}
<font class="first">A</font>rchive of
<font class="first">F</font>ormal
<font class="first">P</font>roofs
{% endblock %}

{% block content %}
<table width="80%" class="entries">
  <tbody>
    <tr><td>

<h3>Test status of entries in the AFP development version</h3>
<p>
<table style="margin-left: 30pt;">
<tbody>
  <tr>
    <td>Isabelle revision:</td>
    <td>
      <a href="http://isabelle.in.tum.de/repos/isabelle/rev/{{ build_data.isabelle_id }}">
        {{ build_data.isabelle_id }}
      </a>
    </td>
  </tr>
  <tr>
    <td>AFP revision:</td>
    <td>
      <a href="https://foss.heptapod.net/isa-afp/afp-devel/-/commit/{{ build_data.afp_id }}">
        {{ build_data.afp_id }}
      </a>
    </td>
  </tr>
  <tr><td>Build time:</td><td>{{ build_data.time }}</td></tr>
  <tr><td>Build URL:</td><td><a href="{{ build_data.url }}">Jenkins</a></td></tr>
  <tr><td>Job name:</td><td>{{ build_data.job }}</td></tr>
</tbody>
</table>
</p>

    </td></tr>
  </tbody>
</table>

<p>&nbsp;</p>

<table width="80%" class="entries">
  <tbody>

{% for entry in entries %}
<tr>
  <td class="status-{{entry.status}}">[{{entry.status}}]</td>
  <td class="entry">
    <a href="entries/{{entry.name}}.html">{{entry.name}}</a>
  </td>
</tr>
{% endfor %}

  </tbody>
</table>
{% endblock %}

