inductive WeekDay : Type
| Sunday    : WeekDay
| Monday    : WeekDay
| Tuesday   : WeekDay
| Wednesday : WeekDay
| Thursday  : WeekDay
| Friday    : WeekDay
| Saturday  : WeekDay

#check @WeekDay.Sunday

open WeekDay

#check @Sunday

#check @WeekDay.rec
#check @WeekDay.rec_on


def numberOfDay1 (d : WeekDay) : ℕ := WeekDay.rec_on d 1 2 3 4 5 6 7
def numberOfDay2 (d : WeekDay) : ℕ := WeekDay.rec 1 2 3 4 5 6 7 d
def numberOfDay3 (d : WeekDay) : ℕ := WeekDay.cases_on d 1 2 3 4 5 6 7

#reduce numberOfDay1 Sunday
#reduce numberOfDay1 Monday
#reduce numberOfDay2 Sunday
#reduce numberOfDay2 Monday
#reduce numberOfDay3 Tuesday
#reduce numberOfDay3 Wednesday




