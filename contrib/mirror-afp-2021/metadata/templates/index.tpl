{% extends "base.tpl" %}

{# MACROS #}
{%- macro print_addr(author) -%}
  {%- if author.address|startswith('http') %}
    <a href="{{ author.address }}">{{ author.name }}</a>
  {%- else %}
    {{ author.name }}
  {%- endif %}
{%- endmacro %}


{% block headline %}
<font class="first">A</font>rchive of
<font class="first">F</font>ormal
<font class="first">P</font>roofs</h1>
{% endblock %}

{% block content %}
<table width="80%" class="entries">
<tbody>
  <tr>
    <td>
The Archive of Formal Proofs is a collection of proof libraries, examples, and larger scientific developments,
mechanically checked in the theorem prover <a href="http://isabelle.in.tum.de/">Isabelle</a>. It is organized in the way
of a scientific journal, is indexed by <a href="http://dblp.uni-trier.de/db/journals/afp/">dblp</a> and has an ISSN:
2150-914x. Submissions are refereed. The preferred citation style is available <a href="citing.html">[here]</a>. We encourage companion AFP submissions to conference and journal publications.
<br><br>
{%- if not is_devel %}
A <a href="http://devel.isa-afp.org">development version</a> of the archive is available as well.
{%- else %}
<strong>
  This is the development version of the archive, referring to a recent
  Isabelle development version. Some entries may not be in a working state, see
  the <a href="status.html">status page</a> for more information.
  The main archive is available from the <a href="http://www.isa-afp.org">front page</a>.
</strong>
{%- endif %}
    </td>
  </tr>
</tbody>
</table>

<p>&nbsp;</p>

{% for year, entries in by_year %}
<p>&nbsp;</p>

<table width="80%" class="entries">
<tbody>
  <tr>
    <td class="head">{{ year }}</td>
  </tr>
  {% for e in entries %}
    <tr>
      <td class="entry">
        {{ e.publish_date|datetimeformat }}: <a href="entries/{{ e.name }}.html">{{ e.title }}</a>
        <br>
        {% if e.authors|length > 1 %}
          Authors:
          {% for a in e.authors[:-2] %}
            {{ print_addr(a) }},
          {% endfor %}
          {{ print_addr(e.authors[-2]) }}
          and {{ print_addr(e.authors[-1]) }}
        {% else %}
          Author:
          {% for a in e.authors %}
          {{ print_addr(a) }}
          {% endfor %}
        {% endif %}
      </td>
    </tr>
  {% endfor %}
</tbody>
</table>
{% endfor %}

{% endblock %}

