{% extends "base.tpl" %}

{#TODO * use ul instead of div
 #TODO * better formatting with CSS #}

{% block headline %}
<font class="first">I</font>ndex by <font class="first">T</font>opic
{% endblock %}

{% block content %}
<table width="80%" class="descr">
<tbody>
<tr>
<td>
{# For every topic, we iterate through the entries then through the subtopics.
   We go down three levels. For more levels the template needs to be modified #}
{# TOPIC LEVEL 1 #}
{% for topic_name, topic in tree.subtopics.items() %}
  <h2>{{ topic_name }}</h2>
  <div class="list">
  {% for e in topic.entries %}
    <a href="entries/{{ e }}.html">{{ e }}</a> &nbsp;
  {% endfor %}
  </div>
  {# TOPIC LEVEL 2 #}
  {% for topic_name, topic in topic.subtopics.items() %}
    <h3>{{ topic_name }}</h3>
    <div class="list">
    {% for e in topic.entries %}
      <a href="entries/{{ e }}.html">{{ e }}</a> &nbsp;
    {% endfor %}
    {# TOPIC LEVEL 3 #}
    {% for topic_name, topic in topic.subtopics.items() %}
      <strong>{{ topic_name }}:</strong>
      {% for e in topic.entries %}
        <a href="entries/{{ e }}.html">{{ e }}</a> &nbsp;
      {% endfor %}
    {% endfor %}
    </div>
  {% endfor %}
{% endfor %}
</td>
</tr>
</tbody>
</table>
{% endblock %}

