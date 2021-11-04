{% extends "base.tpl" %}

{% block headline %}
<font class="first">S</font>tatistics
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>
      <h2>Statistics</h2>

<table>
<tr><td>Number of Articles:</td><td class="statsnumber">{{ entries|length }}</td></tr>
<tr><td>Number of Authors:</td><td class="statsnumber">{{ entries.authors|length }}</td></tr>
<tr><td>Number of lemmas:</td><td class="statsnumber">~{{ '{:,d}'.format(num_lemmas|round(-2)|int) }}</td></tr>
<tr><td>Lines of Code:</td><td class="statsnumber">~{{ '{:,d}'.format(num_loc|round(-2)|int) }}</td></tr>
</table>
<h4>Most used AFP articles:</h4>
<table id="most_used">
<tr>
<th></th><th>Name</th><th>Used by ? articles</th>
</tr>

{# You could use loop.index here, but there's an obscure bug in Jinja2 with
   loop.index and groupBy #}
{% for no_of_imports, articles in most_used %}
  <tr><td>{{ loop.index }}.</td>
  {% set td_joiner = joiner('<td></td>') %}
  {% for article in articles %}
    {{ td_joiner() }}
    <td><a href="entries/{{ article.name }}.html">{{ article.name }}</a></td>
    <td>{{ no_of_imports }}</td>
    </tr>
  {% endfor %}
{% endfor %}

</table>
<script>
// DATA
var years = [{{ years|join(", ") }}];
var no_articles = [{{ articles_year|join(", ") }}];
var no_loc = [{{ loc_years|join(", ") }} ];
var no_authors = [{{ author_years|join(", ") }}];
var no_authors_series = [{{ author_years_cumulative|join(", ") }}];
{% set comma = joiner(",") %}
var all_articles = [ {% for article in articles_by_time %}{{ comma() }}"{{article.name}}"{% endfor %}];
{% set comma = joiner(",") %}
var years_loc_articles = [
{%- for year, articles in articles_per_year %}
  {{ comma() }}{{year}}
  {%- set comma1 = joiner(",") %}
  {%- for article in articles %}
    {{ comma1() }}
  {%- endfor %}
{%- endfor %}];
{% set comma = joiner(",") %}
var loc_articles = [ {% for article in articles_by_time %}{{ comma() }}"{{article.loc}}"{% endfor %}];

</script>
<h4>Growth in number of articles:</h4>
<script src="Chart.js"></script>
<div class="chart">
<canvas id="NumberOfArticles" width="400" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("NumberOfArticles");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years,
        datasets: [{
            label: 'size of the AFP in # of articles',
            data: no_articles,
            backgroundColor: "rgba(46, 45, 78, 1)"
        }],
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
     }
});
</script>

<h4>Growth in lines of code:</h4>
<div class="chart">
<canvas id="NumberOfLoc" width="400" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("NumberOfLoc");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years,
        datasets: [{
            label: 'size of the AFP in lines of code',
            data: no_loc,
            backgroundColor: "rgba(101, 99, 136, 1)"
        }],
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
     }
});
</script>

<h4>Growth in number of authors:</h4>
<div class="chart">
<canvas id="NumberOfAuthors" width="400" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("NumberOfAuthors");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years,
        datasets: [{
            label: 'new authors per year',
            data: no_authors,
            backgroundColor: "rgba(101, 99, 136, 1)"
            },
            {
            label: 'number of authors contributing (cumulative)',
            data: no_authors_series,
            backgroundColor: "rgba(0, 15, 48, 1)"
        }],
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
     }
});
</script>

<h4>Size of articles:</h4>
<div style="width: 800px" class="chart">
<canvas id="LocArticles" width="800" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("LocArticles");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years_loc_articles,
        datasets: [{
            label: 'loc per article',
            data: loc_articles,
            backgroundColor: "rgba(101, 99, 136, 1)"
            }]
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            xAxes: [{
                categoryPercentage: 1,
                barPercentage: 0.9,
                ticks: {
                    autoSkip: false
                }
                }],
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
        tooltips: {
            callbacks: {
                title: function(tooltipItem, data) {
                       return all_articles[tooltipItem[0].index];
                       }
            }
        }
     }
});
</script>

    </td></tr>

  </tbody>
</table>
{% endblock %}

{% block footer %}
<script src="Chart.js"></script>
{% endblock %}
