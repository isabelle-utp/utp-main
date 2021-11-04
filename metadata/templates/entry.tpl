{% extends "base.tpl" %}

{# Print first letter bigger if uppercase #}
{% macro first_bigger(text) %}
  {# jinja way to check if a letter is uppercase #}
  {% if text[0]|upper == text[0] %}
    <font class="first">{{ text[0] }}</font>{{ text[1:] }}
  {% else %}
    {{ text }}
  {% endif %}
{% endmacro %}

{% block title %}
{{ entry.title }} - Archive of Formal Proofs
{% endblock %}

{% block extrahead %}
{% include 'mathjax.tpl' with context %}
{% endblock %}

{% block headline %}
{% for s in entry.title|split %}
  {{ first_bigger(s) }}
{% endfor %}
{% endblock %}

{% block content %}
<table width="80%" class="data">
<tbody>
<tr>
  <td class="datahead" width="20%">Title:</td>
  <td class="data" width="80%">{{ entry.title }}</td>
</tr>

{# Authors #}
{%- macro print_author(author) %}
  {%- if author.address|startswith("mailto:") %}
    {{author.name}} ({{author.address[7:]}})
  {%- elif author.address|startswith("http") %}
    <a href="{{author.address}}">{{author.name}}</a>
  {%- else %}
    {{author.name}}
  {%- endif %}
{%- endmacro %}
<tr>
  <td class="datahead">
    {% if entry.authors|length == 1 %}
      Author:
    {% else %}
      Authors:
    {% endif %}
  </td>
  <td class="data">
    {% if entry.authors|length == 1 %}
      {{ print_author(entry.authors[0]) }}
    {% else %}
      {% for author in entry.authors[:-2] %}
        {{ print_author(author) }},
      {% endfor %}
      {{ print_author(entry.authors[-2]) }} and
      {{ print_author(entry.authors[-1]) }}
    {% endif %}
  </td>
</tr>

{# Contributors #}
{#TODO: merge author and contributor printing #}
{%- macro print_contributor(contri) %}
  {%- if not contri[1] %}
    {{contri[0]}}
  {%- elif contri[1]|startswith("mailto:") %}
    {{contri[0]}} ({{contri[1][7:]}})
  {%- else %}
    <a href="{{contri[1]}}">{{contri[0]}}</a>
  {%- endif %}
{%- endmacro %}
{% if entry.contributors %}
  <tr>
    <td class="datahead">
      {% if entry.contributors|length == 1 %}
        Contributor:
      {% else %}
        Contributors:
      {% endif %}
    </td>
    <td class="data">
      {% if entry.contributors|length == 1 %}
        {{ print_contributor(entry.contributors[0]) }}
      {% else %}
        {% for contri in entry.contributors[:-2] %}
          {{ print_contributor(contri) }},
        {% endfor %}
        {{ print_contributor(entry.contributors[-2]) }} and
        {{ print_contributor(entry.contributors[-1])}}
       {% endif %}
     </td>
  </tr>
{% endif %}


<tr>
  <td class="datahead">Submission date:</td>
  <td class="data">{{ entry.publish_date|datetimeformat }}</td>
</tr>

<tr>
  <td class="datahead" valign="top">Abstract:</td>
  <td class="abstract mathjax_process">{{ entry.abstract }}</td>
</tr>

{# Extra datafields #}
{% for key, value in entry.extra.items() %}
  <tr>
    <td class="datahead" valign="top">{{ value[0] }}:</td>
    <td class="abstract">{{ value[1] }}</td>
  </tr>
{% endfor %}

{# BibTeX #}
<tr>
  <td class="datahead" valign="top">BibTeX:</td>
  <td class="formatted">
    {# Hack to display { directly before {{ jinja command #}
    {# TODO: Add base url functionality #}
<pre>@article{{ "{" }}{{ entry.name }}-AFP,
  author  = {{ "{" }}{%- for a in entry.authors[:-1] %}{{ a.name }} and {% endfor %}{{ entry.authors[-1].name}}},
  title   = {{ "{" }}{{ entry.title}}},
  journal = {Archive of Formal Proofs},
  month   = {{ entry.publish_date.month|short_month }},
  year    = {{ entry.publish_date.year }},
  note    = {\url{https://isa-afp.org/entries/{{ entry.name }}.html},
            Formal proof development},
  ISSN    = {2150-914x},
}</pre>
  </td>
</tr>

    <tr><td class="datahead">License:</td>
        <td class="data"><a href="{{ entry.license[1] }}">{{ entry.license[0] }}</a></td></tr>

    {% macro print_dep(entries, title) %}
      {% set comma = joiner(", ") %}
      {% if entries|sort(attribute='title') %}
      <tr><td class="datahead">{{title}}:</td>
          <td class="data">
      {%- for article in entries|sort(attribute='name') %}
      {{- comma() }}<a href="{{ article.name }}.html">{{ article.name }}</a>
      {%- endfor %}
      </td></tr>
      {% endif %}
    {% endmacro %}

    {{ print_dep(entry.imports, "Depends on") }}
    {{ print_dep(entry.used, "Used by") }}

    {#TODO: or check for None? #}
    {% if is_devel %}
      <tr>
        <td class="status-{{entry.status}}">Status: [{{ entry.status }}]</td>
        <td class="data">
          This is a development version of this entry. It might change over time
          and is not stable. Please refer to release versions for citations.
        </td>
      </tr>
    {% endif %}

  </tbody>
</table>

<p></p>

<table class="links">
  <tbody>
    <tr>
    <td class="links">
      <a href="{{ ROOT_PATH }}browser_info/current/AFP/{{ entry.name }}/outline.pdf">Proof outline</a><br>
      <a href="{{ ROOT_PATH }}browser_info/current/AFP/{{ entry.name }}/document.pdf">Proof document</a>
    </td>
    </tr>
    <tr>
    <td class="links">
      <a href="{{ ROOT_PATH }}browser_info/current/AFP/{{ entry.name }}/index.html">Browse theories</a>
      </td></tr>
    <tr>
    <td class="links">
      <a href="{{ ROOT_PATH }}release/afp-{{ entry.name }}-current.tar.gz">Download this entry</a>
    </td>
    </tr>


    {% if not is_devel %}
      <tr><td class="links">Older releases:
      {% if entry.releases|length > 1 %}
        <ul>
        {% for release, listdate in entry.releases[1:] %}
          {% for tar in listdate %}
            <li>Isabelle {{ release }}:
            <a href="{{ ROOT_PATH }}release/afp-{{ entry.name }}-{{ tar }}.tar.gz">
              afp-{{ entry.name }}-{{ tar }}.tar.gz
            </a>
            </li>
          {% endfor %}
        {% endfor %}
        </ul>
      {% else %}
      None
      {% endif %}
      </td></tr>
    {% endif %}

  </tbody>
</table>
{% endblock %}

{% block footer %}
<script src="{{ ROOT_PATH }}jquery.min.js"></script>
<script src="{{ ROOT_PATH }}script.js"></script>
{% endblock %}

