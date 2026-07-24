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

## Universal property

The construction is dimension-generic.  Put

\[
A=R[x_i]_{i\in\iota},\qquad B=R[t_j]_{j\in\kappa},
\qquad t_j\longmapsto F_j.
\]

For every commutative \(R\)-algebra \(T\), the collision quotient satisfies

\[
\operatorname{Hom}_{R\text{-alg}}(S/I_R(F),T)
\cong
\left\{
(f,g):A\rightrightarrows T:
f(F_j)=g(F_j)\text{ for every }j
\right\}.
\]

Consequently there is a canonical equivalence

\[
S/I_R(F)\cong A\otimes_BA.
\]

This universal construction does not assert vanishing.  Dimension two and
dimension three are specializations of the same object: the planar target
says its off-diagonal factor is zero, whereas in the cubic
\(S_3\)-example the normalized off-diagonal factor is the Galois closure.

## Lean status

The current development is dimension-generic and proves:

- every polynomial difference lies in the diagonal ideal;
- the canonical containment \(I_R(F)\subseteq I_\Delta\);
- the universal property of the collision quotient;
- the canonical equivalence \(S/I_R(F)\simeq A\otimes_BA\);
- the obstruction ideal is the kernel of the diagonal map
  \(S/I_R(F)\to A\);
- \(\operatorname{Obs}(F)=0\) if and only if \(I_R(F)=I_\Delta\);
- equality of the two ideals implies injectivity on points;
- a polynomial left inverse forces \(I_R(F)=I_\Delta\);
- the abstract secant-determinant identities and resulting idempotent
  decomposition;
- saturation stabilizes at \(I_R:I_\Delta\) when the diagonal is clopen;
- the complementary-ideal identities and Chinese-remainder sheet
  decomposition;
- the affine off-diagonal collision scheme
  \(R_F^\circ=\operatorname{Spec}(S/(I_R:I_\Delta))\);
- the canonical identification of \(\operatorname{Spec}(S/I_R)\) with
  the categorical affine self-fiber product \(X\times_YX\);
- from the clopen-projector datum, the scheme coproduct decomposition
  \(\operatorname{Spec}(S/I_R)\cong
    \operatorname{Spec}(S/I_\Delta)\sqcup R_F^\circ\);
- emptiness of \(R_F^\circ\), vanishing of the obstruction ideal, and
  equality \(I_R=I_\Delta\) are equivalent.

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

The geometric form of the project goal is:

> **Planar étale-correspondence rigidity.**
> Let \(F:X=\mathbb A^2\to Y=\mathbb A^2\) be a Keller map and set
> \[
> R_F^\circ
> =
> \operatorname{Spec}\bigl(S/(I_R:I_\Delta)\bigr).
> \]
> Then \(R_F^\circ\) is empty.

The colon presentation is the scheme-theoretic meaning of the complement
here.  Étaleness makes the diagonal open and closed in \(X\times_YX\), so
its complement is again an affine clopen subscheme rather than merely a
set-theoretic difference.  The Chinese-remainder decomposition below
identifies it canonically.

Every irreducible component \(S\subseteq R_F^\circ\) has two étale
quasi-finite projections

\[
p_1,p_2:S\longrightarrow X
\]

satisfying

\[
F\circ p_1=F\circ p_2.
\]

Galois theory identifies the generic function field of \(S\) as a
double-coset field in the normal closure of
\(\mathbb C(x,y)/\mathbb C(P,Q)\).  The intended planar argument is then to
use the geometry of affine surfaces to show that no such nonfinite
off-diagonal correspondence can hide its ramification entirely in boundary
curves.  Finite connected correspondence components reduce to graphs of
deck automorphisms; the substantive case is the nonfinite boundary case.

This gives the intended contradiction architecture.

First, the standard finite-correspondence rigidity statement says:

> For a planar Keller map, there is no nonempty connected off-diagonal
> collision component finite over either projection.

\[
S\neq\varnothing
\quad\Longrightarrow\quad
p_1:S\to X\text{ is not finite}.
\]

Indeed, a connected finite étale cover of
\(\mathbb A^2_{\mathbb C}\) is trivial, so a finite component would be the
graph of a finite-order deck automorphism.  Such a graph cannot remain
disjoint from the diagonal.

The graph-extraction part is now explicit in Lean.
`collisionGraphEndomorphism` trivializes the first projection of a
`CollisionCocone` and turns the second projection into a source-ring
endomorphism.  Lean proves that this endomorphism fixes every coordinate
of \(F\), that its graph reconstructs the original second projection, and
that a bijective second projection upgrades it to
`collisionGraphAutomorphism`.

The finite-order route no longer needs a separately assumed bijectivity
of the second projection.  `algEquivOfFiniteOrder` proves that a
finite-order algebra endomorphism is automatically an automorphism, and
`collisionGraphAutomorphismOfFiniteOrder` applies this directly to a
collision graph.  On points, `planeAutomorphismPointMap` is the geometric
map represented by that coordinate-ring automorphism.  Lean proves that
if the automorphism fixes \(F\), then

\[
F(\gamma(a))=F(a)
\]

and hence every point of its graph annihilates \(I_R(F)\).  A fixed point
of \(\gamma\) is therefore exactly an intersection of its graph with the
diagonal.  `FixedPointIdeal` makes the same statement algebraically:

\[
J_\gamma=(\gamma(x_1)-x_1,\gamma(x_2)-x_2)
\]

is proper exactly when \(\gamma\) has a fixed point, and \(J_\gamma=(1)\)
exactly when the graph avoids the diagonal.  The converse direction uses
the Nullstellensatz over \(\mathbb C\).

At the component level, `FiniteComponentAutomorphismBridge` records the
remaining geometric passage from a finite off-diagonal component to a
finite-order, fixed-point-free deck automorphism.
The more primitive `FiniteComponentEndomorphismBridge` records only the
endomorphism naturally produced by trivializing the first projection;
Lean derives the automorphism bridge from its finite-order field.
`FiniteOrderPlaneAutomorphismFixedPoint` records the classical
affine-plane fixed-point input.  Lean proves

```text
FiniteComponentAutomorphismBridge
FiniteOrderPlaneAutomorphismFixedPoint
--------------------------------------
FiniteCorrespondenceRigidity
```

in `finiteCorrespondenceRigidity_of_automorphismBridge`.  Neither the
geometric construction of the bridge nor the classical fixed-point
theorem is silently assumed as an axiom: both occur as explicit hypotheses.

Two unconditional finite-symmetry steps are separated into their own
modules.  `FiniteFieldSymmetry` proves that a self-embedding of a finite
field extension is bijective and that every automorphism of such an
extension has finite order.  `FiniteOrderFixedPoint` proves by averaging a
finite orbit that every finite-order **affine** automorphism in
characteristic zero has a fixed point.  What is not yet in mathlib is the
additional plane-polynomial linearization theorem needed to pass from a
finite-order polynomial automorphism to that affine case.

Likewise, mathlib does not currently supply the theorem that every
connected finite étale cover of \(\mathbb A^2_{\mathbb C}\) is trivial.
Thus the finite case is reduced to two explicit classical geometric
interfaces:

\[
\begin{aligned}
&S\to\mathbb A^2_{\mathbb C}\text{ connected, finite, étale}
  \Longrightarrow S\cong\mathbb A^2_{\mathbb C},\\
&\gamma\in\operatorname{Aut}(\mathbb A^2_{\mathbb C}),\
  \gamma\text{ finite order}
  \Longrightarrow \gamma\text{ has a fixed point}.
\end{aligned}
\]

The algebra between these interfaces is formalized; neither interface is
being presented as a completed Lean theorem.

The specifically planar theorem target is the opposite implication:

\[
S\neq\varnothing
\quad\Longrightarrow\quad
p_1:S\to X\text{ is finite}.
\]

Equivalently, the finite normalization of \(S\) over \(X\) has no deleted
boundary curve.  Conductor compatibility of the normalized collision
idempotent is the proposed mechanism for proving this finiteness.  The two
statements together force \(S=\varnothing\), hence planar vanishing.

This contradiction is formalized in Lean.  A
`PlanarCollisionComponentModel` records the component predicate, finiteness
of \(p_1\), and the fact that a nonzero obstruction produces an
off-diagonal component.  Then

```text
FiniteCorrespondenceRigidity
PlanarBoundaryFiniteness
--------------------------------
PlanarVanishing
```

is proved by `planarVanishing_of_finite_and_nonfinite`.  This theorem is the
complete logical proof scaffold; instantiating the model with actual scheme
components and proving `PlanarBoundaryFiniteness` remain the substantive
planar geometry.

The refined adapter
`planarVanishing_of_automorphismBridge_and_boundaryFiniteness` plugs the
graph-automorphism argument directly into this scaffold.

There is one caveat to a componentwise inertia proof: a degree-one
off-diagonal component can have an unramified boundary.  Such components
are governed generically by \(N_G(H)/H\).  The global normal-closure
argument below avoids identifying nonfiniteness of an individual component
with ramification.

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

Equivalently,

\[
\bar\delta_F=c(1-q_F).
\]

Thus

\[
\operatorname{Supp}\operatorname{Obs}(F)
\subseteq V(I_R,\delta_F).
\]

After the idempotent decomposition, this determinantal locus is precisely
the off-diagonal factor scheme-theoretically: \(\delta_F\) is the unit
\(c\) on the diagonal factor and zero on the off-diagonal factor.  It is
the degenerate-secant locus where a hypothetical planar counterexample
must live.

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

### Off-diagonal saturation and Chinese remainders

Once the obstruction ideal in \(S/I_R\) is generated by an idempotent
\(q_F\), the complementary sheet has a canonical ideal already in \(S\):

\[
I_{\mathrm{off}}
:=
I_R:I_\Delta.
\]

The usual saturation is

\[
I_R:I_\Delta^\infty
=
\bigcup_{n\geq1}(I_R:I_\Delta^n).
\]

Clopenness makes this chain stabilize immediately.  Lean proves

\[
I_R:I_\Delta^\infty
=I_R:I_\Delta
=I_{\mathrm{off}}.
\]

Moreover,

\[
I_R=I_\Delta\cap I_{\mathrm{off}},
\qquad
I_\Delta+I_{\mathrm{off}}=S.
\]

The Chinese remainder theorem therefore gives the canonical sheet
decomposition

\[
\boxed{
S/I_R
\cong
S/I_\Delta\times S/I_{\mathrm{off}}.
}
\]

Passing contravariantly to affine schemes gives

\[
\boxed{
\operatorname{Spec}(S/I_R)
\cong
\operatorname{Spec}(S/I_\Delta)
\sqcup
R_F^\circ,
\qquad
R_F^\circ:=\operatorname{Spec}(S/I_{\mathrm{off}}).
}
\]

Since \(\operatorname{Spec}(S/I_\Delta)\cong X\), this says exactly that
the self-collision space is the disjoint union of its diagonal copy of the
source and the affine off-diagonal collision scheme.  In particular,

\[
\boxed{
R_F^\circ=\varnothing
\Longleftrightarrow
S/I_{\mathrm{off}}\text{ is the zero ring}
\Longleftrightarrow
I_{\mathrm{off}}=S
\Longleftrightarrow
\operatorname{Obs}(F)=0.
}
\]

Under these equivalent conditions,

\[
X\times_YX
\cong
\operatorname{Spec}(S/I_R)
\cong
\operatorname{Spec}(S/I_\Delta)
\cong
\Delta_X
\cong X.
\]

Thus the Lean proposition `PlanarOffDiagonalVanishing` is equivalent to
`PlanarVanishing`; this is proved in `OffDiagonalScheme`.  The construction
removes an ambiguity in the geometric language, but the assertion that this
scheme is empty for every planar Keller map remains the substantive
Jacobian-conjecture step.

The corresponding principal neighborhood statement needs a slightly
stronger formulation than merely choosing \(h\notin I_\Delta\).  Lean
constructs an element satisfying

\[
h\equiv1\pmod{I_\Delta},
\qquad
hI_\Delta\subseteq I_R.
\]

Thus \(D(h)\) contains the whole diagonal and
\((I_R)_h=(I_\Delta)_h\).  These results are in `OffDiagonal`; their only
geometric input is the explicit idempotent-projector datum expressing that
the diagonal is clopen.

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

Here normalization and Galois closure play complementary, not identical,
roles.  Normalization is the geometric operation that separates integral
collision branches.  The Galois closure is the finite symmetry object that
simultaneously contains every conjugate sheet.  If \(g\in G\), the generic
field of the collision component indexed by \(HgH\) is

\[
L\,g(L)=N^{\,H\cap gHg^{-1}}.
\]

Consequently the normal \(N\)-model maps **to** the normalization of that
collision component:

\[
\operatorname{Norm}_{N}(Y)
\longrightarrow
\operatorname{Norm}_{L\,g(L)}(Y).
\]

A single normalized self-fiber product need not be the Galois closure.
Rather, normalized components of iterated fiber products intersect the
conjugate stabilizers; when their intersection is the normal core of
\(H\), their compositum is \(N\).  This is the precise bridge from the
equal-functions language of \(I_R\) to the equal-embeddings language of
Galois theory.

Although \(F:X\to Y\) is étale, the finite map
\(\overline X\to Y\) may ramify at points of the deleted boundary
\(\overline X\setminus X\).  In the Galois completion \(Z\to Y\), this is
recorded by nontrivial divisorial inertia.  Normalization does not create
ramification from nothing: it reveals valuations of \(N/K\) whose centers
were absent from the original affine sheet.

### Global planar rigidity bridge

In the intermediate quotient, generic sheets are represented by \(G/H\).
For a branch divisor \(B\subseteq Y\), choose \(E\subseteq Z\) above it and
write \(I_E\leq G\) for its inertia group.  The stabilizer of the sheet
\(gH\) is \(gHg^{-1}\), so invisibility of inertia at that sheet is

\[
I_E\leq gHg^{-1}.
\]

Equivalently, every element of \(I_E\) fixes \(gH\).  The kernel of the
action on all sheets is

\[
\ker\bigl(G\curvearrowright G/H\bigr)
=\operatorname{core}_G(H).
\]

Because \(N\) is the actual normal closure, \(H\) is core-free.  Thus any
nontrivial inertia group fixes some sheets only by moving others.  The
affine étale model can exist only if every moved sheet is deleted at the
boundary.

The formal target is `PlanarHiddenInertiaRigidity`: for each actual branch
divisor, inertia that is invisible on every sheet remaining in the affine
plane must be trivial.  `PlanarGaloisInertiaModel` records the following
bridge:

\[
\operatorname{Obs}(F)\ne0
\Longrightarrow G\ne1
\Longrightarrow \exists E,\ I_E\ne1,
\]

together with étale invisibility on the visible sheets.  Lean then proves

\[
\texttt{PlanarHiddenInertiaRigidity}
\Longrightarrow \operatorname{Obs}(F)=0
\]

and, uniformly for Keller maps,

\[
\boxed{
\texttt{HasPlanarHiddenInertiaBridge}
\Longrightarrow \texttt{PlanarVanishing}.
}
\]

The final implication is
`planarVanishing_of_hiddenInertiaRigidity`.  The coset stabilizer,
normal-core, and contradiction steps are proved.  Constructing the
geometric model from \(Z=\operatorname{Norm}_N(Y)\) and proving
`PlanarHiddenInertiaRigidity` are the remaining substantive planar
geometry; they are not assumed as axioms.

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
