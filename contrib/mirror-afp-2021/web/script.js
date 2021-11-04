// Script to make the BibTeX-Code less obstrusive
function show(a) {
	$(a).parent().next().show();
	$(a).parent().remove();
}
$(document).ready(function() {
	$('td.formatted pre').each(function(n,pre) {
		$(pre) .after($(pre).clone().hide())
			.text( $(pre).text().split('\n')[0] )
			.append(' <a id="bib" href="" onclick="show(this);return false;">[...]</a>');
	});
});

