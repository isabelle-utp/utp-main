<!-- MathJax for LaTeX support in abstracts -->
{#
  The following is the MathJax configuration.
  This means that formulae can be enclosed in either $ … $ or \( … \)
#}
<script>
MathJax = {
  tex: {
    inlineMath: [['$', '$'], ['\\(', '\\)']]
  },
  processEscapes: true,
  svg: {
    fontCache: 'global'
  }
};
</script>
{# The following can be used instead to use MathJax from their CDN as opposed to our local copy.
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js">
</script>
#}
<script id="MathJax-script" async src="{{ ROOT_PATH }}components/mathjax/es5/tex-mml-chtml.js"></script>

