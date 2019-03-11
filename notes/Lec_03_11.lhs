Looking at triples of the form:

\begin{verbatim}
{P} c {Q}
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Conjecture: for any Q,

\begin{verbatim}
{TRUE} c {Q}
\end{verbatim}

Is this legit? Probably not. E.g., not legit for:

\begin{verbatim}
Q = (x > 10)
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

What about:

\begin{verbatim}
{FALSE} c {Q}
\end{verbatim}

This is legit, because the set of post-c states is empty.

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

What about:

\begin{verbatim}
{P} c {TRUE}
\end{verbatim}

This is also legit, because any post-c state matches the condition.

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

What about:

\begin{verbatim}
{P} c {FALSE}
\end{verbatim}

Not legit, because any post-c state fails the condition.

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Now let's look at:

\begin{verbatim}
{P} c {Q}
---------
{P} c {Q'}

Q' is a subset of Q
\end{verbatim}

Let's think about Q' = (x = 1) and Q = (x \textgreater{}= 0). The subset
relation holds (visualize as a number line).

Consider:

\begin{verbatim}
{TRUE} c {x >= 0}
-----------------
{TRUE} c {x = 1}
\end{verbatim}

This doesn't hold: x being 2 fits the numerator, but not the
denominator.

Then what we really need is for Q to be a subset of Q'. Swap around Q
and Q':

\begin{verbatim}
{TRUE} c {x = 1}
-----------------
{TRUE} c {x >= 0}
\end{verbatim}

Now it works!

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Recall the definition of legit:

\begin{verbatim}
forall s s'. IF P(s), c, s -> s' THEN Q(s')
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Define the ``implies'' relation:

\begin{verbatim}
Q => Q' = IF Q(s) THEN Q'(s)
\end{verbatim}

Then we can say:

\begin{verbatim}
{P} c {Q}   Q => Q'
-------------------
{P} c {Q'}
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Suppose we have:

\begin{verbatim}
{P} c {Q}   P => P'
-------------------
{P'} c {Q}
\end{verbatim}

No, doesn't work.

In this case we need P' to be a subset of P - consider: P = (x
\textgreater{}= 0) and P' = (x = 5).

So what we need is:

\begin{verbatim}
{P'} c {Q}   P => P'
--------------------
{P} c {Q}
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Bring it all together (FHCons):

\begin{verbatim}
{P'} c {Q'}   P => P'   Q' => Q
-------------------------------
{P} c {Q}
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

For any P, the following is legit (FHSkip):

\begin{verbatim}
{P} SKIP {P}
\end{verbatim}

Now consider:

\begin{verbatim}
{FALSE} SKIP {FALSE} - legit

{FALSE} SKIP {TRUE} - legit

{TRUE} SKIP {FALSE} - not legit

{TRUE} SKIP {TRUE} - legit
\end{verbatim}

Think of it as a truth table:

\begin{verbatim}
P Q | P => Q
------------
0 0 | 1
0 1 | 1
1 0 | 0
1 1 | 1
\end{verbatim}

This is boolean implication. Can we derive this?

In fact we can, from FHSkip and FHCons.

\begin{verbatim}
IF P, Q
  {P} SKIP {Q}
THEN
  P => Q
\end{verbatim}

\begin{verbatim}
------------------[FHSkip]
{TRUE} SKIP {TRUE}           FALSE => TRUE   TRUE => TRUE
---------------------------------------------------------[FHCons]
{FALSE} SKIP {TRUE}
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Rules we have in our toolkit:

CONSEQ, SKIP, ASSIGN, SEQ, IF, WHILE

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Reminder, rule for SEQ:

\begin{verbatim}
{P} c1 {MID}   {MID} c2 {Q}
---------------------------
{P} c1; c2 {Q}
\end{verbatim}

\begin{center}\rule{0.5\linewidth}{\linethickness}\end{center}

Let's formulate the rule for IF:

\begin{verbatim}
{P ^ b} c1 {Q}   {P ^ ~b} c2 {Q}
--------------------------------
{P} IF b c1 c2 {Q}
\end{verbatim}
