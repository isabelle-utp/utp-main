<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{% block title %}Archive of Formal Proofs{% endblock %}</title>
<link rel="stylesheet" type="text/css" href="{{ ROOT_PATH }}front.css">
<link rel="icon" href="{{ ROOT_PATH }}images/favicon.ico" type="image/icon">
<link rel="alternate" type="application/rss+xml" title="RSS" href="{{ ROOT_PATH }}rss.xml">
{% block extrahead %} {% endblock %}
</head>

<body class="mathjax_ignore">
{#TODO remove width tags #}
{#TODO remove p blocks #}

<table width="100%">
<tbody>
<tr>

<!-- Navigation -->
<td width="20%" align="center" valign="top">
  <p>&nbsp;</p>
  <a href="https://www.isa-afp.org/">
    <img src="{{ ROOT_PATH }}images/isabelle.png" width="100" height="88" border=0>
  </a>
  <p>&nbsp;</p>
  <p>&nbsp;</p>
  <table class="nav" width="80%">
    <tr>
      <td class="nav" width="100%"><a href="{{ ROOT_PATH }}index.html">Home</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}about.html">About</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}submitting.html">Submission</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}updating.html">Updating Entries</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}using.html">Using Entries</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}search.html">Search</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}statistics.html">Statistics</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}topics.html">Index</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}download.html">Download</a></td>
    </tr>
  </table>
  <p>&nbsp;</p>
  <p>&nbsp;</p>
</td>


<!-- Content -->
<td width="80%" valign="top">
<div align="center">
  <p>&nbsp;</p>
  <h1>{% block headline %}{% endblock %}</h1>
  <p>&nbsp;</p>

{% block content %}
{% endblock %}

</div>
</td>

</tr>
</tbody>
</table>

{% block footer %}
{% endblock %}

</body>
</html>
