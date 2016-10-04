from django.conf.urls import patterns, include, url
from django.contrib import admin
from django.conf.urls.defaults import * # added

urlpatterns = patterns('',
    (r'^$', 'dj_apache.logview.views.list_files'),
    (r'^viewlog/(?P<sortmethod>.*?)/(?P<filename>.*?)/$',
        'dj_apache.logview.views.view_log'),
)
