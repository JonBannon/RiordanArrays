# Dialogue

Working thread. This is where we think out loud: conjectures, failed attempts,
referee objections, half-formed ideas. It is version-controlled but is **not**
the manuscript. When something settles, it gets promoted to a section under
`sections/` and a one-line pointer is left here.

## How to use this file

- Date entries. Keep the messy reasoning; that is the point.
- Mark unresolved questions with `OPEN:` so they are greppable.
- When an argument is promoted, replace the worked-out block with a pointer:
  `-> promoted to sections/intro.tex, "..." paragraph (YYYY-MM-DD)`.

---

## 2026-08-19 - repository created

Scaffolded from `paper-templates` (mathematics flavor). Working title:
"Riordan Arrays". Nothing settled yet.

## 2026-08-19 - ordinary Riordan truncations as crossing operators

We tested the most direct local construction. Let $V$ have dimension two,
and regard the $4\times4$ principal truncation of an ordinary Riordan array
$(g,f)$ as a crossing operator $R:V\otimes V\to V\otimes V$. Multiplying
$g$ by a nonzero scalar only multiplies both sides of the braided
Yang--Baxter equation by the same scalar cubed, so normalize $g(0)=1$. Write

\[
g=1+g_1x+g_2x^2+g_3x^3+\cdots,
\qquad
f=f_1x+f_2x^2+f_3x^3+\cdots.
\]

The principal truncation is

\[
R=\begin{pmatrix}
1&0&0&0\\
g_1&f_1&0&0\\
g_2&f_2+g_1f_1&f_1^2&0\\
g_3&f_3+g_1f_2+g_2f_1&2f_1f_2+g_1f_1^2&f_1^3
\end{pmatrix}.
\]

Set

\[
D=(R\otimes I)(I\otimes R)(R\otimes I)
 -(I\otimes R)(R\otimes I)(I\otimes R).
\]

Several entries give a complete certificate. With zero-based indices,

\[
D_{1,0}=-f_1g_1,
\qquad
D_{1,1}=-f_1(f_1-1).
\]

Since a Riordan array has $f_1\ne0$, these equations force $g_1=0$ and
$f_1=1$. After those substitutions,

\[
D_{2,1}=-f_2,
\qquad
D_{2,0}=-g_2,
\]

so $f_2=g_2=0$. Finally, after these substitutions,

\[
D_{3,0}=-g_3,
\qquad
D_{3,1}=-f_3.
\]

Thus the only normalized $4\times4$ Riordan truncation satisfying the
Yang--Baxter equation is $I_4$. Without the normalization, it is a scalar
multiple of $I_4$, which cannot distinguish knots after the usual closure
normalization.

The load-bearing limitation is the ansatz: the calculation treats a principal
truncation of one ordinary one-variable Riordan array as the entire two-state
crossing operator. It does not rule out larger state spaces, constructions
using several Riordan arrays, coefficient contractions, or diagram-indexed
state sums. The reproducible computation is in
`scripts/riordan_yang_baxter.py`.
