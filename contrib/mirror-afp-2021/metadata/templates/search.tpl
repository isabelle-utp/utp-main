{% extends "base.tpl" %}

{% block headline %}
<font class="first">S</font>earch the <font class="first">A</font>rchive
{% endblock %}

{% block content %}
<div align="center"><!-- SiteSearch Google -->
<p>Use Google to search the archive. It will look in entry descriptions 
as well as in the Isabelle theories and PDF proof documents.</p>
<p>&nbsp;</p>
<FORM method=GET action="https://www.google.com/search">
<TABLE bgcolor="#FFFFFF"><tr><td>
<A HREF="https://www.google.com/">
<IMG SRC="https://www.google.com/logos/Logo_40wht.gif" 
border="0" ALT="Google"></A>
</td>
<td>
<INPUT TYPE=text name=q size=31 maxlength=255 value="">
<INPUT type=submit name=btnG VALUE="Google Search">
<font size=-1>
<input type=hidden name=domains value="isa-afp.org"><br><input type=radio name=sitesearch value=""> Web <input type=radio name=sitesearch value="isa-afp.org" checked>Archive of Formal Proofs<br>
</font>
</td></tr></TABLE>
</FORM>
<!-- SiteSearch Google -->
<p>&nbsp;</p>
<p>Google may take some time to index new pages. Very new Submissions might be missed.</p>
</div>
{% endblock %}

