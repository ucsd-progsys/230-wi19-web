# CSE 230: Proofs of Programs (for Programs (by Programs))

Course materials for UCSD CSE 230, Winter 2019

## Private Links 

- [HW solutions](https://github.com/ucsd-progsys/230-wi19-private)
- [Concrete-LH](https://github.com/ucsd-progsys/concrete-semantics-lh)

## Course Description

CSE 230 is an introduction to the Formal Semantics of Programming Languages.

Unlike most engineering artifacts, Programming Languages and Programs are
mathematical objects whose properties can be formalized. The goal of this
course is to introduce students to fundamental intellectual and mechanical
tools required to rigorously analyze Languages and Programs and to expose
them to recent developments in and applications of these techniques.

We shall study operational and axiomatic semantics, two different ways of
precisely capturing the meaning of programs by characterizing their executions.
We will see how the lambda calculus can be used to distill essence of
computation into a few powerful constructs. We use that as a launching pad to
study expressive type systems useful for for analyzing the behavior of programs
at compile-time and then, how to derive expressive program analyses using
Abstract Interpretation.

All of the above will be done in a *concrete* fashion, i.e. by writing programs
that define the various kinds of semantics, and writing  more programs that
correspond to proofs about those objects!

## Co-ordinates

- *Lectures:*          MWF 1:00p-1:50p in WLH 2113
- *Final:*             Take home during finals week
- *Announcements:*     [On Piazza](https://piazza.com/class/jqk23zupq7a62c)

## Staff

- [Ranjit Jhala](http://ranjitjhala.github.io)
- [Anish Tondwalkar](http://ani.sh/)

## Calendar

- [Deadlines, Office Hours](https://calendar.google.com/calendar?cid=ZW5nLnVjc2QuZWR1X292YWFsOWY4NWE0bTNqYXU2NWlmajNlOW4wQGdyb3VwLmNhbGVuZGFyLmdvb2dsZS5jb20)

## Prerequisites

- Functional Programming e.g. CSE 130

## Text

There is **no text** for CSE 230, but we will be basing much of the material on:

- [Nipkow and Klein's: Concrete Semantics](http://concrete-semantics.org/)

## Proofs of Programs, for Programs, by Programs

| Week | Topic                   | Code             | Link                                     |
|-----:|:------------------------|:-----------------|:-----------------------------------------|
| 1.   | Refinement Types        | [lhs](src/Week1) | [tutorial](https://liquid.kosmikus.org/) |
|      |                         |                  |                                          |
|      | **Proofs of Programs**  |                  |                                          |
| 2.   | Programs  as Proofs     | [lhs](src/Week2) | Ch2 of Nipkow & Klein                    |
| 3.   | Induction on Terms      | [lhs](src/Week3) | Ch3 of Nipkow & Klein		       |
| 4.   | Induction on Evidence   | [lhs](src/Week4) | Ch4 of Nipkow & Klein                    |
|      |                         |                  |                                          |
|      | **Proofs for Programs** |                  |                                          |
| 5.   | Big Step Semantics      | [lhs](src/Week5) | Ch7 of Nipkow & Klein                    |
| 6.   |                         | [lhs](src/Week6) |                                          |
| 7.   | Small Step Semantics    | [lhs](src/Week7) | [pdf](static/img/smallstep.pdf)          |
| 8.   |                         | [lhs](src/Week8) |                                          |
| 9.   | Axiomatic Semantics     | [lhs](src/Week9) | [pdf](static/img/axiomatic.pdf)          |
| 10.  |                         | [lhs](src/Week10)| 					       |
|      |                         |                  |                                          |
|      | Type Systems            |                  | 					       |
|      | **Proofs by Programs**  |                  |                                          |
|      | Horn Clauses            |                  |                                          |
|      | Abstract Interpretation |                  |                                          |
|      | Refinement Types        |                  |                                          |
|      |                         |                  |                                          |

## Scribe Notes

- Can be found [here](notes/)

## Assignments Starter Code

- [HW1](https://github.com/ucsd-cse230-wi19/hw1)
- [HW2](https://github.com/ucsd-cse230-wi19/hw2)
- [HW3](https://github.com/ucsd-cse230-wi19/hw3)
- [HW4](https://github.com/ucsd-cse230-wi19/hw4)
- [HW5](https://github.com/ucsd-cse230-wi19/hw5)
- [HW6](https://github.com/ucsd-cse230-wi19/hw6)
- [Final](https://github.com/ucsd-cse230-wi19/final)

## Piazza

All announcements are on [on Piazza](https://piazza.com/class/jqk23zupq7a62c)

## Github Assignments 

- [HW1](https://classroom.github.com/a/PQ9R2Yfh) due 1/20
- [HW2](https://classroom.github.com/a/qcYaxHeJ) due 2/1
- [HW3](https://classroom.github.com/a/VW5sqKmL) due 2/11
- [HW4](https://classroom.github.com/a/BiyzylSq) due 2/20
- [HW5](https://classroom.github.com/a/4LWQx956) due 3/3
- [HW6](https://classroom.github.com/a/pjo_q4I9) due 3/10




## Grading

### Class Participation (10%)

Involves in class participation and answering questions on Piazza.

### Programming Assignments (45%)

- There will be a total of 5-6
- You have a total of *four late days* 
- They may be **done in pairs**

A *late day* can be used for any programming assignment and is
anything between 1 second and 23 hours 59 minutes and 59 seconds 
after the deadline.

### Scribe Notes (20%)

- Produce LaTeX lecture notes **for one lecture**
- Due **one week after** the lecture
- They may be **done in pairs**
- Stay tuned for **signup form** and **template** 

### Final (25%)

- This will be a "take home" exam
- Run during finals week.

## Links

### LiquidHaskell

- [Repo](https://github.com/ucsd-progsys/liquidhaskell)
- [Install](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/INSTALL.md)
- [Blog](https://ucsd-progsys.github.io/liquidhaskell-blog/)

### Getting Started with Haskell

- [Haskell-Lang](http://haskell-lang.org)
- [Getting started with Haskell](https://haskell-lang.org/get-started)
- [What I Wish I Knew When Learning Haskell](http://dev.stephendiehl.com/hask/)
- [Haskell Cheat Sheet](http://cheatsheet.codeslower.com/CheatSheet.pdf)
- [Haskell Pitfalls](http://users.jyu.fi/~sapekiis/haskell-pitfalls/)

### Books on Haskell

- [Haskell Programming from First Principles](http://haskellbook.com) by Christopher Allen and Julie Moronuki
- [Programming in Haskell](http://www.cs.nott.ac.uk/~gmh/book.html) by Graham Hutton
- [Real World Haskell](http://www.realworldhaskell.org) by Bryan O' Sullivan, John Goerzen, and Don Stewart

### Miscellaneous

- A Simple editor-independent [mini-ide](https://github.com/ndmitchell/ghcid#readme)
- API Search Engines:
  [Hoogle](http://haskell.org/hoogle)
  [Hayoo](http://holumbus.fh-wedel.de/hayoo/hayoo.html)
- Haskell modes:
  [Emacs](https://commercialhaskell.github.io/intero/)
  [Atom](https://atom.io/packages/ide-haskell)
  [Vim](http://projects.haskell.org/haskellmode-vim/)


## Diversity and Inclusion

We are committed to fostering a learning environment for
this course that supports a diversity of thoughts, perspectives
and experiences, and respects your identities (including race,
ethnicity, heritage, gender, sex, class, sexuality, religion,
ability, age, educational background, etc.) Our goal is to
create a diverse and inclusive learning environment where
all students feel comfortable and can thrive.

Our instructional staff will make a concerted effort to 
be welcoming and inclusive to the wide diversity of students 
in this course.  If there is a way we can make you feel more 
included please let one of the course staff know, either in 
person, via email/discussion board, or even in a note under 
the door.  Our learning about diverse perspectives and 
identities is an ongoing process, and we welcome your 
perspectives and input.  

We also expect that you, as a student in this course, will 
honor and respect your classmates, abiding by the [UCSD Principles of Community](https://ucsd.edu/about/principles.html).  
Please understand that others’ backgrounds, perspectives 
and experiences may be different than your own, and help 
us to build an environment where everyone is respected 
and feels comfortable.

If you experience any sort of harassment or discrimination, 
please contact the instructor as soon as possible.   If you 
prefer to speak with someone outside of the course, please 
contact the [Office of Prevention of Harassment and Discrimination.](https://ophd.ucsd.edu/) 

## Integrity of Scholarship

University rules on integrity of scholarship will be strictly enforced. By
taking this course, you implicitly agree to abide by the UCSD Policy on
Integrity of Scholarship described [here](http://www-senate.ucsd.edu/manual/Appendices/app2.htm).
In particular,

> all academic work will be done by the student to whom it is assigned,
> without unauthorized aid of any kind.

You are expected to do your own work on all assignments; when
specified, you **may work in pairs** -- but will submit the
assignments individually. You may (and are encouraged to)
engage in **general discussions** with your classmates
regarding the assignments, but specific details of a
solution, including the solution itself,
**must always be your own work**.

There will be graded assignments and exam in this course,
as described below. All exams are closed book; no tools
other than your brain and a writing instrument are to be used.

Incidents which violate the University's rules on integrity of scholarship
will be taken seriously.  In addition to **receiving a zero (0)** on the
assignment/exam in question, students may also face other penalties,
up to and including, expulsion from the University.  Should you have
any doubts about the moral and/or ethical implications of an activity
regarding the course, please see the instructor.

## Research

Your class work might be used for research purposes. For example, we may
use anonymized student assignments to design algorithms or build tools to
help programmers. Any student who wishes to opt out can contact the
instructor or TA to do so after final grades have been issued.
**This has no impact on your grade in any manner.**
