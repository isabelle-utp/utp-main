<?xml version="1.0" encoding="UTF-8" ?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom" xmlns:dc="http://purl.org/dc/elements/1.1/">
  <channel>
    <atom:link href="https://www.isa-afp.org/rss.xml" rel="self" type="application/rss+xml" />
    <title>Archive of Formal Proofs</title>
    <link>https://www.isa-afp.org</link>
    <description>
      The Archive of Formal Proofs is a collection of proof libraries, examples,
      and larger scientific developments, mechanically checked
      in the theorem prover Isabelle.
    </description>
    <pubDate>{{ entries[0].publish_date|rfc822 }}</pubDate>
{% for entry in entries %}
    <item>
       <title>{{ entry.title }}</title>
       {#TODO: put base link in config #}
       <link>https://www.isa-afp.org/entries/{{ entry.name }}.html</link>
       <guid>https://www.isa-afp.org/entries/{{ entry.name }}.html</guid>
       <dc:creator>
       {%- set comma = joiner(",") %}
       {%- for author in entry.authors %}{{ comma() }} {{ author.name }}{%- endfor %}
       </dc:creator>
       <pubDate>{{ entry.publish_date|rfc822 }}</pubDate>
       <description>{{ entry.abstract|e }}</description>
    </item>
{% endfor %}
  </channel>
</rss>

