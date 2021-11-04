{% extends "base.tpl" %}

{% block headline %}
<font class="first">R</font>eferring to
<font class="first">A</font>FP
<font class="first">E</font>ntries
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>

<p>
Once you have downloaded the AFP, you can include its articles and theories in
your own developments. If you would like to make your work available to others
<i>without</i> having to include the AFP articles you depend on, here is how to do it.
</p>
<p>
From Isabelle2021 on, the recommended method for making the whole AFP available to Isabelle
is the <code>isabelle components -u</code> command.
</p>

<h2>Linux/Mac</h2>
<p>
Assuming you have downloaded and unzipped the afp to <code>/home/myself/afp</code>, run
</p>
<pre class="code">
    isabelle components -u /home/myself/afp/thys
</pre>

<h2>Windows</h2>
<p>
If the AFP is in <code>C:\afp</code>, run the following command in a Cygwin terminal:
<pre class="code">
  isabelle components -u /cygdrive/c/afp/thys
</pre>
</p>

<h2>Use</h2>
<p>
You can now refer to article <code>ABC</code> from the AFP in another theory via</p>

<pre class="code">
    imports "ABC.Some_ABC_Theory"
</pre>

<p>This allows you to distribute your material separately from any AFP
theories. Users of your distribution also need to install the AFP in the above
manner.</p>

<p>&nbsp;</p>

    </td></tr>
  </tbody>
</table>
{% endblock %}

