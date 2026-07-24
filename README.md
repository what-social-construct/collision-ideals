# Collision ideals and diagonal ideals

Let

\[
F=(F_1,\ldots,F_n):\mathbb A^n_{\mathbb C}\longrightarrow
\mathbb A^n_{\mathbb C}
\]

be a polynomial map.  In the coordinate ring of two copies of the source,

\[
S=\mathbb C[x_1,\ldots,x_n,y_1,\ldots,y_n],
\]

there are two canonical ideals:

\[
I_R(F)=\bigl(F_i(x)-F_i(y)\bigr)_{i=1}^n,
\qquad
I_\Delta=\bigl(x_i-y_i\bigr)_{i=1}^n.
\]

Every polynomial difference vanishes on the diagonal, so there is a
canonical inclusion

\[
I_R(F)\subseteq I_\Delta
\]

and therefore a canonical \(S/I_R(F)\)-module

\[
\operatorname{Obs}(F):=I_\Delta/I_R(F).
\]

Thus \(\operatorname{Obs}(F)\) is not an additional independent object: it
is the canonical defect module in the exact sequence

\[
0\longrightarrow I_R(F)\longrightarrow I_\Delta
\longrightarrow\operatorname{Obs}(F)\longrightarrow0.
\]

The purpose of this project is to study the vanishing of
\(\operatorname{Obs}(F)\).
Since \(I_R(F)\subseteq I_\Delta\), the elementary module criterion gives

\[
\operatorname{Obs}(F)=0
\quad\Longleftrightarrow\quad
I_R(F)=I_\Delta.
\]

## Automorphism criterion

Over \(\mathbb C\), the quotient has a direct interpretation:

\[
\boxed{
F\text{ is a polynomial automorphism}
\quad\Longleftrightarrow\quad
\operatorname{Obs}(F)=0.
}
\]

If \(F\) has a polynomial inverse, applying the inverse to the two output
tuples gives \(I_\Delta\subseteq I_R(F)\).  Conversely, vanishing gives
\(I_R(F)=I_\Delta\), hence injectivity on complex points; Ax–Grothendieck
then gives a polynomial automorphism.

Geometrically, if \(A_F=S/I_R(F)\), then

\[
\operatorname{Spec}(A_F)
=
\mathbb A^n\times_{\mathbb A^n}\mathbb A^n
\]

parametrizes ordered pairs with the same image under \(F\).  The closed
subscheme cut out by \(\operatorname{Obs}(F)\), regarded as an ideal of
\(A_F\), is the diagonal.  Thus \(\operatorname{Obs}(F)=0\) says that the
self-fiber product is scheme-theoretically only the diagonal.

## Lean status

The current development is dimension-generic and proves:

- every polynomial difference lies in the diagonal ideal;
- the canonical containment \(I_R(F)\subseteq I_\Delta\);
- \(\operatorname{Obs}(F)=0\) if and only if \(I_R(F)=I_\Delta\);
- equality of the two ideals implies injectivity on points;
- a polynomial left inverse forces \(I_R(F)=I_\Delta\);
- the abstract secant-determinant identities and resulting idempotent
  decomposition.

The definitions are generic in the coefficient ring, source variables, and
output coordinates.  The planar specialization uses
`R := ℂ` and `Fin 2`.

Build the project with:

```bash
lake build
```

## Planar Vanishing

For a polynomial self-map \(F:\mathbb A^2_{\mathbb C}\to\mathbb A^2_{\mathbb
C}\), write

\[
\operatorname{Keller}(F)
\quad:\Longleftrightarrow\quad
\det JF\in\mathbb C^\times.
\]

The main theorem target is:

\[
\boxed{
\operatorname{Keller}(F)
\Longrightarrow
\operatorname{Obs}(F)=0.
}
\]

In Lean, `PlanarVanishing` records this proposition without assuming it as an
axiom.  Proving it is the unresolved two-dimensional Jacobian-conjecture
case; by the automorphism criterion above, the planar Jacobian conjecture is
an immediate corollary.

The next formal step is the local theorem: for a Keller map, the diagonal is
an open-and-closed subscheme of the self-fiber product, so
\(\operatorname{Obs}(F)\) is supported on the off-diagonal complement.  The
substantive planar step is then to prove that this complement is empty.

## Secant determinant and annihilator

Write the collision equations in secant form

\[
\binom{F_1(x)-F_1(y)}{F_2(x)-F_2(y)}
=
M_F(x,y)\binom{x_1-y_1}{x_2-y_2}
\]

and set \(\delta_F=\det M_F\).  If \(\det JF=c\in\mathbb C^\times\), then

\[
\delta_F I_\Delta\subseteq I_R(F),
\qquad
\delta_F\equiv c\pmod {I_\Delta}.
\]

In \(A_F=S/I_R(F)\), this says that \(\bar\delta_F\) annihilates
\(\operatorname{Obs}(F)\) and is congruent to the unit \(c\) modulo
\(\operatorname{Obs}(F)\).  Consequently

\[
q_F=1-\frac{\bar\delta_F}{c}
\]

is idempotent and

\[
\operatorname{Obs}(F)=A_Fq_F,
\qquad
\operatorname{Ann}_{A_F}(\operatorname{Obs}(F))
=A_F(1-q_F).
\]

Thus the following are equivalent:

\[
\operatorname{Obs}(F)=0
\quad\Longleftrightarrow\quad
q_F=0
\quad\Longleftrightarrow\quad
\text{the off-diagonal clopen summand is empty}.
\]

The secant argument constructs this decomposition; it does not by itself
prove that \(q_F=0\).  Forcing that vanishing is the specifically planar
step.

## Finite completion and hidden inertia

Write

\[
B=\mathbb C[P,Q]\subset A=\mathbb C[x,y],\qquad
K=\operatorname{Frac}(B)\subset L=\operatorname{Frac}(A),
\]

and let \(N/K\) be the normal closure, with

\[
G=\operatorname{Gal}(N/K),\qquad H=\operatorname{Gal}(N/L).
\]

For \(Y=\operatorname{Spec}(B)\), set

\[
Z=\operatorname{Norm}_{Y}(N),\qquad
\overline X=\operatorname{Norm}_{Y}(L)\cong Z/H.
\]

Zariski Main places the original affine plane model in the finite model:

\[
X=\operatorname{Spec}(A)\hookrightarrow\overline X\longrightarrow Y.
\]

Although \(F:X\to Y\) is étale, the finite map
\(\overline X\to Y\) may ramify at points of the deleted boundary
\(\overline X\setminus X\).  In the Galois completion \(Z\to Y\), this is
recorded by nontrivial divisorial inertia.  Normalization does not create
ramification from nothing: it reveals valuations of \(N/K\) whose centers
were absent from the original affine sheet.

The fiber product makes this mechanism precise.  Let

\[
\overline R=\overline X\times_Y\overline X,
\qquad
R=X\times_YX.
\]

On \(R\), étaleness makes the diagonal open and closed:

\[
R=\Delta_X\sqcup R^\circ.
\]

At a ramified boundary divisor of the finite completion, the closure of
the diagonal and the closure of an off-diagonal component can meet inside
\(\overline R\).  Equivalently, the diagonal idempotent on \(R\) need not
extend across the divisorial boundary to \(\overline R\).

Algebraically, for a ring map \(B\to A\), put

\[
C=A\otimes_BA,\qquad \mu:C\to A.
\]

Formal unramifiedness is equivalent to the existence of a tensor \(t\in C\)
such that

\[
\mu(t)=1,\qquad
(1\otimes a-a\otimes1)t=0\quad(a\in A).
\]

Then \(t\) is the diagonal projector, \(q=1-t\) is the off-diagonal
projector, and

\[
\ker(\mu)=Cq.
\]

Thus a fiber-product form of the missing planar step is an idempotent
extension, or closure-separation, statement: the diagonal and
off-diagonal components, separated over \(X\), cannot meet again solely
along the boundary of the finite completion.  This is a reformulation of
the hard planar assertion, not a consequence of normalization alone.

This extension problem can be concentrated further on the conductor.  If
\(\widetilde C\) is the normalization of the completed fiber-product
algebra \(\overline C\), let

\[
\mathfrak c=
\{d\in\widetilde C:d\widetilde C\subseteq\overline C\}
\]

be the conductor.  The normalized off-diagonal idempotent
\(\widetilde q\in\widetilde C\) descends to \(\overline C\) exactly when

\[
\widetilde q\bmod\mathfrak c
\]

lies in the image of

\[
\overline C/\mathfrak c\longrightarrow
\widetilde C/\mathfrak c.
\]

Thus the target planar lemma says that the \(0/1\) labels on the normalized
diagonal and off-diagonal branches are compatible along the conductor
where those branches are glued.

## Dimension three: the contrasting narrative

The dimensional contrast is:

\[
\begin{array}{c|c}
n=2 &
\operatorname{Keller}(F)\Longrightarrow\operatorname{Obs}(F)=0
\quad\text{(Planar Vanishing target)},\\[2mm]
n=3 &
\operatorname{Obs}(F)\neq0
\quad\text{in the known example; its off-diagonal field is the }
S_3\text{-Galois closure}.
\end{array}
\]

In the known cubic-fiber counterexample in dimension three, the
obstruction module \(\operatorname{Obs}(F)\) does not vanish.  Generically,
let \(L/K\) be the resulting cubic function-field extension.  Then

\[
L\otimes_KL\cong L\times M,
\]

where the \(L\)-factor is the diagonal and \(M/K\) is the degree-\(6\)
Galois closure with \(\operatorname{Gal}(M/K)\cong S_3\).  Thus the generic
function field of the off-diagonal component is precisely the
\(S_3\)-Galois closure.  It records ordered pairs of distinct sheets and
governs the failure of

\[
F(u)=F(v)\Longrightarrow u=v.
\]

This final example is a contrast, not a universal assertion that every
three-dimensional collision relation has \(S_3\)-monodromy.

For the explicit counterexample and independent formal verification, see the
[Archive of Formal Proofs entry](https://isa-afp.org/entries/Jacobian_Counterexample.html).
For the cubic-fiber and \(S_3\) structure, see the
[ordered-root/Galois-closure account](https://mathoverflow.net/questions/513387/).
