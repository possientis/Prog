"""
curses based Apache log viewer

usage:

    python3 curses_test.py logfile

This will start an interactive, keyboard driven log viewing 
application. Here are what the various key presses do:

    u/d     - scroll up/down
    t       - go to the top of the logfile
    q       - quit
    b/h/s   - sort by bytes/hostname/status
    r       - restore to initial sort order
"""

import curses
import sys
import operator

class CursesLogViewer(object):
    def __init__(self, logfile=None):
        self.screen = curses.initscr()
        self.curr_topline = 0
        self.logfile = logfile
        self.loglines = []

    def page_up(self):
        self.curr_topline = self.curr_topline - (2 * curses.LINES)
        if self.curr_topline < 0:
            self.curr_topline = 0
        self.draw_loglines()

    def page_down(self):
        self.draw_loglines()

    def top(self):
        self.curr_topline = 0
        self.draw_loglines()

    def sortby(self, field):
        #self.loglines = sorted(self.loglines, key=operator.itemgetter(field))
        self.loglines.sort(key=operator.itemgetter(field))
        self.top()

    def set_logfile(self, logfile):
        self.logfile = logfile
        self.load_loglines()
        
    def load_loglines(self):
        pass # TODO

    def draw_loglines(self):
        pass # TODO


