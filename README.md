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

Equivalently, let

\[
\bar\mu_F:S/I_R(F)\longrightarrow S/I_\Delta,
\qquad
[f]_{I_R}\longmapsto[f]_{I_\Delta},
\]

be the quotient map induced by \(I_R(F)\subseteq I_\Delta\).  Then

\[
\boxed{
\ker(\bar\mu_F)=\operatorname{Obs}(F)=I_\Delta/I_R(F),
}
\]

so there is a second canonical exact sequence

\[
0\longrightarrow\operatorname{Obs}(F)
\longrightarrow S/I_R(F)
\xrightarrow{\bar\mu_F}S/I_\Delta
\longrightarrow0.
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

The Lean proposition `PlanarJacobianConjecture` records the usual
automorphism formulation.  The proposition `PlanarAxGrothendieck` records
the classical injective-polynomial-map automorphism principle as an
explicit interface.  Most theorems continue to accept it parametrically;
`Planar.ExternalAssumptions.axGrothendieckA2` is the isolated project axiom
used by the literature-backed corollary.  Lean proves

```text
PlanarAxGrothendieck →
  (PlanarJacobianConjecture ↔ PlanarKernelVanishing)
```

in `planarJacobianConjecture_iff_planarKernelVanishing`; Lean also proves
`PlanarKernelVanishing ↔ PlanarVanishing`.

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
- a concrete planar secant decomposition whose chosen determinant restricts
  to the planar Jacobian determinant;
- for planar Keller maps,
  \(I_R:I_\Delta=I_R+(\delta_F)\) and
  \(I_R=I_\Delta\iff I_R+(\delta_F)=S\);
- the concrete secant projector witnessing that the planar collision
  diagonal is a clopen factor;
- saturation stabilizes at \(I_R:I_\Delta\) when the diagonal is clopen;
- the complementary-ideal identities and Chinese-remainder sheet
  decomposition;
- the affine off-diagonal collision scheme
  \(R_F^\circ=\operatorname{Spec}(S/(I_R:I_\Delta))\);
- the canonical identification of \(\operatorname{Spec}(S/I_R)\) with
  the categorical affine self-fiber product \(X\times_YX\);
- the concrete planar function fields
  \(K=\mathbb C(P,Q)\subset L=\mathbb C(x,y)\), a finite normal-closure
  interface \(L\hookrightarrow N\), and the fixing subgroup
  \(H=\operatorname{Gal}(N/L)\);
- the normalized affine models
  \[
  Z=\operatorname{Norm}_N(Y)\longrightarrow
  \overline X=\operatorname{Norm}_L(Y)\longrightarrow Y
  \]
  and the commuting normalization triangle;
- for abstract candidate-inertia data, the group-theoretic relative index
  \([I_E:I_E\cap H]\), including that it is greater than one in the
  finite case relevant here when \(I_E\nsubseteq H\);
- the well-defined double-coset index on
  \(D_E\backslash G/H\), using normality of inertia in the decomposition
  group, and its planar valuation specialization;
- the exact visible-sheet detection condition required from the global
  system of conjugate affine opens;
- the formal reduction from normalization rigidity and the
  generic-degree-one collision lemma to `PlanarVanishing`;
- from the clopen-projector datum, the scheme coproduct decomposition
  \(\operatorname{Spec}(S/I_R)\cong
    \operatorname{Spec}(S/I_\Delta)\sqcup R_F^\circ\);
- emptiness of \(R_F^\circ\), vanishing of the obstruction ideal, and
  equality \(I_R=I_\Delta\) are equivalent;
- assuming the explicit Ax–Grothendieck interface, the standard planar
  Jacobian conjecture is equivalent to `PlanarVanishing`.

The definitions are generic in the coefficient ring, source variables, and
output coordinates.  The planar specialization uses
`R := ℂ` and `Fin 2`.

Build the project with:

```bash
lake build
```

## Module layout

The generic implementation modules under `CollisionIdeals/` contain the
dimension-independent construction: collision and diagonal ideals, the
canonical diagonal map, the obstruction kernel, secant identities, fiber
products, normalization interfaces, coset and double-coset sheets, the
abstract inertia quotient \([I:I\cap H]\), conductor descent, and
finite-field symmetry.  A few older top-level filenames remain as
compatibility facades for the new planar leaves.

The `CollisionIdeals/Planar/` directory contains only the complex
two-dimensional specialization:

- `Basic` defines `PlanePolynomial`, the planar Jacobian determinant, and
  the Keller condition;
- `Vanishing` states the planar obstruction/kernel target;
- `Normalization` constructs \(K\subset L\subset N\), the normalized
  models \(Z\to\overline X\to Y\), and states the finite-model rigidity
  target;
- `Inertia` gives an abstract interface for divisorial centers and inertia
  subgroups, and proves the associated relative subgroup-index
  calculation;
- `ValuationInertia` constructs valuation-ring decomposition and inertia
  subgroups and isolates the additional geometric DVR bridge
  \(e=|I|\);
- `DecompositionSheets` specializes the generic
  \(D_E\backslash G/H\) calculation to planar valuation inertia;
- `NormalizationDiagram` wires those existing double-coset classes to
  centers on the finite normalization and separates local visible-sheet
  inertia from the later global planar boundary-rigidity theorem;
- `ConjugateBoundary` retains the earlier abstract visible-subset and
  stabilizer-detection interface;
- `PurityRigidity` states divisorial purity and affine-plane finite-étale
  rigidity as two explicit geometric inputs and proves their formal
  composition;
- `EtaleBoundary` isolates both the Keller-to-scheme-étale theorem and the
  valuation/inertia-to-boundary theorem still needed;
- `ExternalAssumptions` contains exactly the three explicitly declared
  literature inputs: specialized branch purity, finite-étale rigidity of
  \(\mathbb A^2_{\mathbb C}\), and planar Ax–Grothendieck;
- `ConditionalVanishing` packages the remaining internal hidden-inertia
  data and proves the user-facing conditional planar-vanishing theorem;
- `GenericFiber` isolates the passage from generic degree one to emptiness
  of the off-diagonal collision scheme;
- `Components`, `Secant`, `Rigidity`, and `FixedPointIdeal` package the
  other proposed planar proof interfaces.

The former top-level planar import paths remain as compatibility wrappers.
The `CollisionIdeals/ComplexThree/` directory is presently a minimal
specialization layer.  It imports the generic collision and Galois
machinery; the concrete cubic ordered-root theorem will be added there
with all separability, degree, and non-Galois hypotheses explicit.

## Planar Vanishing

For a polynomial self-map \(F:\mathbb A^2_{\mathbb C}\to\mathbb A^2_{\mathbb
C}\), write

\[
\operatorname{Keller}(F)
\quad:\Longleftrightarrow\quad
\det JF\in\mathbb C^\times.
\]

The explicit complex-plane automorphism target is:

\[
\boxed{
\operatorname{Keller}(F)
\Longrightarrow
F\in\operatorname{Aut}_{\mathrm{poly}}(\mathbb A^2_{\mathbb C}).
}
\]

Its equivalent kernel/ideal target is:

\[
\boxed{
\operatorname{Keller}(F)
\Longrightarrow
\ker(\bar\mu_F)=\operatorname{Obs}(F)=0.
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

The concrete secant construction now supplies the idempotent witnessing
that, for a Keller map, the diagonal is an open-and-closed factor of the
self-fiber product.  Thus \(\operatorname{Obs}(F)\) is supported on the
off-diagonal complement.  The substantive planar step is to prove that this
complement is empty.

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

For a planar Keller map, a chosen secant determinant \(\delta_F\) gives an
especially direct description of the complementary ideal:

\[
\boxed{
I_{\mathrm{off}}
=I_R:I_\Delta
=I_R+(\delta_F).
}
\]

Consequently Lean proves

\[
\boxed{
\operatorname{Obs}(F)=0
\Longleftrightarrow
I_R=I_\Delta
\Longleftrightarrow
I_R+(\delta_F)=S.
}
\]

Although \(\delta_F\) comes from a fixed choice of secant coefficients, the
ideal it generates together with \(I_R\) is canonical here because it equals
\(I_R:I_\Delta\).  The proposition `PlanarSecantVanishing` is the assertion
that the last ideal is the unit ideal for every planar Keller map, and Lean
proves `PlanarSecantVanishing ↔ PlanarVanishing`.  This packages the
remaining mathematical target as one concrete ideal statement without
claiming its vanishing.

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
\overline X=\operatorname{Norm}_{Y}(L).
\]

The canonical finite diagram is

\[
\begin{array}{ccc}
Z&\longrightarrow&\overline X\\
&\searrow&\downarrow\nu\\
&&Y,
\end{array}
\]

At the function-field level \(N^G=K\) and \(N^H=L\).  Under the usual
normality and invariant-ring hypotheses, the corresponding geometric
quotients are \(Z/G\simeq Y\) and \(Z/H\simeq\overline X\).  The current
Lean development proves the fixed-field statement and constructs the
displayed maps; it does not yet construct these two scheme quotients.

Zariski Main places the original affine plane model in the intermediate
finite model over the image base:

\[
X=\operatorname{Spec}(A)\xrightarrow{j}\overline X
\xrightarrow{\nu}Y,
\]

After identifying \(Y=\operatorname{Spec}\mathbb C[P,Q]\) with the
abstract polynomial-ring target, the composite is the original map \(F\).

The Lean module `Planar.Normalization` now constructs the two integral
closures, all three displayed morphisms, and the commuting triangle.
It also proves that the fixed field of the displayed subgroup \(H\) is
the distinguished copy of \(L\) in \(N\), and that
\[
\operatorname{core}_G(H)=1
\]
because the conjugate images of \(L\) generate the supplied normal closure.
Module-finiteness of the integral closures and the assertion that \(j\) is
an open immersion remain explicit properties: they are not manufactured
by the definitions.

There is one further target-identification bridge.  The normalization base
is literally \(\operatorname{Spec}\mathbb C[P,Q]\), while the original map
was presented with an abstract polynomial-ring target.  Injectivity of the
coordinate homomorphism identifies these rings and yields
\[
\operatorname{Spec}\mathbb C[P,Q]\simeq\mathbb A^2_{\mathbb C}.
\]
`PlanarKellerTargetImageBridge` isolates the still-unformalized implication
from the concrete Keller determinant to this injectivity; under it, Lean
constructs the displayed scheme isomorphism.

Here normalization and Galois closure play complementary, not identical,
roles.  Normalization is the geometric operation that separates integral
collision branches.  The Galois closure is the finite symmetry object that
simultaneously contains every conjugate sheet.  The expected generic
fiber-product/Galois bridge identifies the collision component indexed by
\(HgH\) with the compositum field

\[
L\,g(L)=N^{\,H\cap gHg^{-1}}.
\]

It would then induce a map from the normal \(N\)-model to the normalization
of that collision component:

\[
\operatorname{Norm}_{N}(Y)
\longrightarrow
\operatorname{Norm}_{L\,g(L)}(Y).
\]

A single normalized self-fiber product need not be the Galois closure.
Rather, normalized components of iterated fiber products should intersect
the conjugate stabilizers; when their intersection is the normal core of
\(H\), their compositum is \(N\).  Constructing this functorial
component-to-normalization map is still missing in Lean.  It is the exact
geometric adapter needed between the equal-functions language of \(I_R\)
and the equal-embeddings language of Galois theory.

Although \(F:X\to Y\) is étale, the finite map
\(\overline X\to Y\) may ramify at points of the deleted boundary
\[
D=\overline X\setminus j(X).
\]
In the Galois completion \(Z\to Y\), this is
recorded by nontrivial divisorial inertia.  Normalization does not create
ramification from nothing: it reveals valuations of \(N/K\) whose centers
were absent from the original affine sheet.

For a codimension-one point \(E\subset Z\), let \(I_E\leq G\) be its
inertia group.  The ramification index induced in the marked intermediate
extension is

\[
\boxed{
e_E(L/K)
=[I_E:I_E\cap H]
=\frac{|I_E|}{|I_E\cap H|}.
}
\]

Thus

\[
I_E\nsubseteq H
\Longrightarrow e_E(L/K)>1.
\]

For an actual divisorial valuation whose center is compatible with these
models, étaleness of the visible sheet should force the center on
\(\overline X\) of every such divisor into \(D\).  This center-compatibility
and boundary implication is an explicit target, not a consequence yet
proved in Lean.  Inertia contained in \(H\) is invisible in \(L/K\), so it
is important not to assert that every ramification divisor of \(Z/Y\) must
lie over the deleted boundary of the marked sheet.
`Planar.Inertia` formalizes the group-theoretic index as
`H.relIndex I_E`.  Its divisor type, centers, and subgroups are an abstract
interface: the module does not yet construct codimension-one valuations or
prove that a supplied subgroup is their geometric inertia group.
`Planar.EtaleBoundary` therefore exposes separate theorem targets:
Keller implies scheme-theoretic étaleness, and a realized valuation center
with \(I_E\nsubseteq H\) lies in the deleted boundary.  The latter is named
`PlanarValuationCenterBoundaryBridge` precisely because the present
abstract divisor data does not itself certify that its stored point is the
center of its stored valuation.

At the valuation level, mathlib already defines the decomposition subgroup
of a valuation ring as its stabilizer and the inertia subgroup as the
kernel of its action on the residue field.  `Planar.ValuationInertia`
specializes these constructions to \(N/K\), restricts the valuation ring
to \(K\), and defines the DVR ramification index.  For the intended
geometric divisorial towers, the required identification is
\[
e(w_E/v_B)=|I_E|
\]
and is exposed as `InertiaCardinalityBridge`; it is not yet proved from the
currently recorded DVR hypotheses.  In particular, the current structure
does not yet encode geometric centeredness, residue separability, or all
defectlessness hypotheses.  Conditional on the bridge, Lean proves that
ramification index different from one is equivalent to nontrivial inertia.
`PlanarValuationInertiaFamily.toInertiaDivisorData` then feeds these
concrete inertia kernels into the pre-existing relative-index interface;
there is only one definition of the intermediate quotient
\([I_E:I_E\cap H]\), namely the dimension-independent
`inertiaQuotientIndex` in `CollisionIdeals/InertiaQuotient.lean`.
The same generic module proves that, for core-free \(H\), every nontrivial
\(I\) has
\[
[I:I\cap gHg^{-1}]>1
\]
on at least one conjugate sheet \(gH\).  `Planar.Inertia` now specializes
this theorem to the actual subgroup \(H=\operatorname{Gal}(N/L)\).

The decomposition group sharpens this statement.  Fix \(E\subset Z\)
above a base divisor \(B\), with decomposition and inertia groups
\[
I_E\trianglelefteq D_E\leq G.
\]
Using the convention
\[
q_g=(g^{-1}E)\cap N^H,
\]
the primes of the intermediate normalization above \(B\) are indexed by
the double cosets
\[
D_E\backslash G/H.
\]
For the class represented by \(g\),
\[
e(q_g/B)
=[I_E:I_E\cap gHg^{-1}].
\]
Normality of \(I_E\) in \(D_E\) makes this expression invariant under the
left \(D_E\)-action; right \(H\)-invariance is automatic.
`DecompositionSheets` formalizes this well-defined group-theoretic index,
and `Planar.DecompositionSheets` instantiates it with mathlib's actual
valuation decomposition and inertia subgroups.  Lean now proves
\[
I_E\neq1
\Longrightarrow
\exists q\in D_E\backslash G/H,\quad
\iota_E(q):=[I_E:I_E\cap gHg^{-1}]>1.
\]
`Planar.NormalizationDiagram` now exposes the missing wiring without
introducing another double-coset object.  Its `NormalizationDiagram`
structure uses the existing `PlanarDecompositionSheetClasses` and records
a center on \(\overline X\) for each class, compatibility of every center
with the map to \(Y\), and identification of the identity class with the
canonical contraction \(Z\to\overline X\).  Constructing these fields from
the standard prime/double-coset classification, including the relative
DVR ramification formula, remains an explicit obligation.

The normalization-form planar target is:

> **Planar normalization rigidity.**
> In the setup above, if \(X\simeq\mathbb A^2_{\mathbb C}\) and
> \(\nu|_X:X\to Y\) is everywhere étale, then \(L=K\).

Equivalently, no nontrivial finite extension \(K\subsetneq L\) admits an
affine-plane open model whose intermediate ramification is displaced
entirely into the deleted boundary.  In Lean,
`PlanarFunctionFieldExtensionTrivial F` means that the canonical embedding
\(K\hookrightarrow L\) is surjective, and `PlanarNormalizationRigidity`
states the displayed theorem.  It is deliberately a proposition to be
proved, not an axiom or a completed theorem; this is the decisive planar
Jacobian-conjecture step.

Once normalization rigidity supplies \(L=K\), Lean proves that the
function-field finrank is one.  Lean also proves the concrete generic
source-fiber calculation
\[
\texttt{planarGenericSourceTensorEquiv}:\qquad
K\otimes_B A\simeq_K L.
\]
The map is \(k\otimes a\mapsto ka\).  Mathlib identifies its source with
the localization of \(A\) at the image of the non-zero-divisors of \(B\),
which proves injectivity; surjectivity is exactly the hypothesis \(L=K\).

The remaining generic-collision step is isolated as
`PlanarGenericDegreeOneExcludesOffDiagonal`: a nonempty component of the
étale self-fiber product has open image under its first projection and
hence would contribute another generic sheet.  Therefore

\[
L=K
\Longrightarrow R_F^\circ=\varnothing
\Longrightarrow\ker(\bar\mu_F)=0
\Longrightarrow I_R=I_\Delta.
\]

The last two implications are already unconditional Lean theorems.
`planarVanishing_of_normalizationRigidity` packages the full reduction and
shows exactly which normalization and generic-fiber inputs remain.

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
nontrivial inertia group moves at least one sheet.  Turning that moved
generic sheet into a ramified divisor on a conjugate affine model, and
then proving that its center must be deleted at the boundary, is the
missing conjugate-sheet geometric adapter.

That local conclusion is not yet a contradiction: the ramified center may
indeed lie outside its conjugate affine-plane open.  The additional input
is global.  For a fixed \(E\), let
\[
V_E\subseteq G/H
\]
be the sheets whose corresponding centers remain in their conjugate affine
opens.  Étaleness gives
\[
I_E\leq\bigcap_{gH\in V_E}gHg^{-1}.
\]
The required overlap/coverage assertion is precisely that these visible
stabilizers detect inertia:
\[
I_E\leq\bigcap_{gH\in V_E}gHg^{-1}
\Longrightarrow I_E=1.
\]
An ordinary union cover is not by itself sufficient.  The stronger
condition \(V_E=G/H\) works because the intersection is then
\(\operatorname{core}_G(H)=1\); smaller visible families also suffice when
their stabilizer intersection is trivial.

The canonical normalization-diagram route now separates the two missing
geometric statements exactly.

First, `VisibleConjugateSheetInertiaAt D E q` is pointwise:

\[
\overline q\in j(X)
\quad\Longrightarrow\quad
\iota_E(q)=1
\]

when the affine-plane sheet is étale.  Its family version
`VisibleConjugateSheetInertia` quantifies over the existing classes
\(q\in D_E\backslash G/H\).  Lean formally derives the contrapositive:
every class with \(\iota_E(q)\ne1\) has its recorded center in the deleted
boundary.

Second, `NormalizationDiagram.PlanarBoundaryRigidity` is deliberately
global and later:

\[
\left(
  \forall q,\ \iota_E(q)\ne1
    \Longrightarrow \overline q\in\overline X\setminus X
\right)
\Longrightarrow I_E=1.
\]

The diagram is indexed by the canonical subtype of actual ramified
height-one primes of \(Z\), not by an arbitrary divisor family.  Therefore
local visible-sheet inertia plus global boundary rigidity makes that
subtype empty and yields `NoCodimensionOneRamification` with no hidden
exhaustiveness assumption.  `Planar.ConjugateBoundary` remains available
as the earlier dimension-independent visible-stabilizer shadow.

`Planar.PurityRigidity` now separates the two geometric inputs used after
hidden-inertia detection:

\[
\begin{aligned}
\texttt{DivisorialPurity}:&\quad
  \text{no nontrivial divisorial inertia}
  \Longrightarrow Z\to Y\text{ is étale},\\
\texttt{FiniteEtaleRigidity}:&\quad
  Z\to Y\text{ is étale}
  \Longrightarrow N=K.
\end{aligned}
\]

The first two are explicit geometric propositions supplied to the
normalization spine.  Ax–Grothendieck enters only at the final
injective-to-automorphism arrow.  The dedicated
`Planar.ExternalAssumptions` module declares exactly three project axioms:

\[
\texttt{branchPurityA2}:\texttt{BranchPurityA2},
\qquad
\texttt{affinePlaneFiniteEtaleRigidity}:
  \texttt{AffinePlaneFiniteEtaleRigidity},
\qquad
\texttt{axGrothendieckA2}:
  \texttt{PlanarAxGrothendieck}.
\]

The branch-purity assumption consumes actual height-one local
unramifiedness through `NoCodimensionOneRamification`; it is not quantified
over an arbitrary, potentially non-exhaustive valuation family.

`Planar.ConditionalVanishing` packages the remaining internal data for one
map as `PlanarHiddenInertiaRigidity F`: the normalization diagram, the
Keller-to-étale bridge, pointwise visible-conjugate-sheet inertia, the
separate global planar boundary-rigidity theorem, and the generic-degree-one
descent to the off-diagonal collision scheme.  From the middle three
fields Lean now derives height-one unramifiedness rather than storing it
as an opaque field.  It then proves the exact conditional spine

\[
\texttt{planarVanishing\_of}\;
  \texttt{branchPurityA2}\;
  \texttt{affinePlaneFiniteEtaleRigidity}\;
  h_{\mathrm{hidden}}\;
  h_{\mathrm{Keller}}
\;:\;
\operatorname{Obs}(F)=0.
\]

Consequently,
`Planar.planarVanishing_assuming_externalAG hHidden hKeller`
supplies the first two isolated external assumptions automatically.
`Planar.planarAutomorphism_assuming_externalLiterature` then supplies
Ax–Grothendieck at the final arrow.  The generic-fiber hypothesis is not
silently asserted as another axiom: its map-specific form is a named field
of `hHidden`.  Lean then proves the formal composition

\[
\begin{array}{c}
\text{collision nerve / iterated fiber products}\\
\downarrow\\
\text{normal closure and double-coset centers}\\
\downarrow\\
\operatorname{core}_G(H)=1\\
\downarrow\\
I_E\ne1\Longrightarrow
  \exists q\in D_E\backslash G/H,\ \iota_E(q)>1\\
\downarrow\\
\text{étale visibility would give }\iota_E(q)=1\\
\downarrow\\
\iota_E(q)>1\Longrightarrow
  \overline q\in\overline X\setminus X\\
\downarrow\\
\text{PlanarBoundaryRigidity}\\
\downarrow\\
\text{all divisorial inertia is trivial}\\
\downarrow\quad\text{\rm(branch purity)}\\
Z\to Y\text{ is finite étale}\\
\downarrow\quad\text{\rm(finite-étale rigidity of }\mathbb A^2_{\mathbb C}\text{\rm)}\\
N=K\Longrightarrow L=K\\
\downarrow\quad\text{\rm(generic collision bridge)}\\
q_F=0\\
\downarrow\\
I_R=I_\Delta\Longrightarrow F\text{ injective}\\
\downarrow\quad\text{\rm(Ax--Grothendieck)}\\
F\text{ is a polynomial automorphism.}
\end{array}
\]

\[
\texttt{DetectsInertia}
+\texttt{DivisorialPurity}
+\texttt{FiniteEtaleRigidity}
\Longrightarrow N=K
\Longrightarrow L=K.
\]

For compatibility with the earlier contrapositive route, Lean also derives
`NontrivialExtensionHasDivisor` from these two geometric inputs:
\(L\neq K\) then supplies a nontrivial divisorial-inertia witness.
After the explicit generic-fiber bridge, the theorem
`obstructionIdeal_eq_bot_of_detectsInertia` returns this conclusion to the
original collision obstruction
\[
I_\Delta/I_R=0.
\]

The earlier abstract route packages this goal as
`PlanarHiddenInertiaRigidity`: for each supplied branch divisor, inertia
that is invisible on every supplied visible sheet must be trivial.
`PlanarGaloisInertiaModel` separately records the schematic implication

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

The final conditional implication is
`planarVanishing_of_hiddenInertiaRigidity`.  The coset stabilizer,
normal-core, and contradiction steps are proved.  The normalized models
and their canonical domination map are now constructed in Lean.  The older
`PlanarGaloisInertiaModel` route and the newer normalized-valuation route
now use the same visible-sheet detection language, but there is not yet a
theorem constructing one model from the other.  What remains is to
construct an exhaustive family of actual ramification divisors, identify
their double-coset prime classes and centers, construct the conjugate
visible opens, and prove the displayed global detection property.  These
are substantive planar geometry, not assumed axioms.

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

Algebraically, in the finitely presented setting relevant here, put

\[
C=A\otimes_BA,\qquad \mu:C\to A.
\]

Formal unramifiedness makes the finitely generated diagonal ideal
idempotent, equivalently giving a tensor \(t\in C\) such that

\[
\mu(t)=1,\qquad
(1\otimes a-a\otimes1)t=0\quad(a\in A).
\]

Then \(t\) is the diagonal projector, \(q=1-t\) is the off-diagonal
projector, and

\[
\ker(\mu)=Cq.
\]

This is where the ideal quotient meets the Galois sheets.  Passing to the
generic fiber gives
\[
A\otimes_BA
\longrightarrow
L\otimes_KL,
\]
and normalizing the generic collision algebra separates its conjugate
components, indexed by the appropriate \(H\backslash G/H\) classes.  The
image of \(t\) is the \(0/1\) label of the identity component and the image
of \(q\) labels the off-diagonal components.  Constructing this
componentwise normalization map functorially is still one of the explicit
fiber-product/Galois adapters.

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

`ConductorDescent` proves this criterion for an arbitrary injective ring
map: an idempotent has an idempotent preimage exactly when its residue
modulo the conductor lies in the image of the corresponding quotient map.

Thus the target planar lemma says that the \(0/1\) labels on the normalized
diagonal and off-diagonal branches are compatible along the conductor
where those branches are glued.

The complete intended loop is therefore
\[
I_\Delta/I_R\neq0
\Longrightarrow R_F^\circ\neq\varnothing
\Longrightarrow N/K\text{ nontrivial}
\Longrightarrow \text{nontrivial boundary inertia}
\]
\[
\Longrightarrow
\text{failure of conjugate-open/conductor compatibility}.
\]
Proving that planar geometry forbids the final failure reverses the loop:
\[
N=K
\Longrightarrow R_F^\circ=\varnothing
\Longrightarrow \ker(\bar\mu_F)=0
\Longrightarrow I_\Delta/I_R=0.
\]
Thus the quotient of the two canonical ideals is both the starting
obstruction and the final vanishing statement.

### Exported planar-rigidity conclusion

`Planar.Conclusion` now exposes the intended theorem spine with the Keller
condition explicit from the outset.

For every planar map \(F\), `planarCollisionIdempotent F` is a canonical
choice of the secant projector on the Keller locus (and is defined to be
zero off that locus).  If \(F\) is Keller, Lean proves

\[
q_F^2=q_F,
\qquad
\ker(\bar\mu_F)=(q_F),
\]

and hence

\[
q_F=0
\Longleftrightarrow
\ker(\bar\mu_F)=0
\Longleftrightarrow
I_R(F)=I_\Delta.
\]

`PlanarRigidity.HiddenInertiaConfiguration` packages one normalized
valuation route through the remaining geometry.  It contains:

- `hKeller : IsPlanarKeller F`;
- a finite normal-closure model;
- an actual family of nontrivial valuation inertia;
- conjugate-open visibility;
- visible-sheet detection;
- the explicit divisorial-purity input;
- the explicit affine-plane finite-étale-rigidity input.

From such a package, Lean proves first

\[
N=K
\]

and then immediately \(L=K\).  Because these fields have different Lean
types, the first proposition is
represented by surjectivity of the canonical embedding \(K\to N\).
`normalClosureEquivBase` exposes the resulting algebra isomorphism

\[
K\simeq_K N.
\]

Finally, after supplying
`PlanarGenericDegreeOneExcludesOffDiagonal` and the explicit classical
`PlanarAxGrothendieck` interface,
`HiddenInertiaConfiguration.conclusion` returns the bundled result

\[
\boxed{
q_F=0,\qquad
I_R(F)=I_\Delta,\qquad
F\text{ is a polynomial automorphism}.
}
\]

Likewise, `planarVanishing_implies_jc2` proves
`JacobianConjectureTwo` from uniform vanishing of the canonical
idempotent while keeping Ax--Grothendieck as a visible parameter; the
new external-literature corollary is the one that supplies the isolated
project axiom.

For the Galois-sheet stage, a twofold generic collision component indexed
by \(HgH\) has field

\[
N^{H\cap gHg^{-1}},
\]

which need not be all of \(N\).  The unconditional normal-closure
construction therefore uses a sufficiently iterated collision algebra:
choose a finite tuple \(g_1,\ldots,g_r\) with

\[
\bigcap_i g_iHg_i^{-1}
=\operatorname{core}_G(H)
=1.
\]

The corresponding primitive component has fraction field \(N\).  This
iteration is automatic because \(G\) is finite and the normal-closure
action is faithful.  In the cubic \(S_3\) case a pair of distinct-root
sheets already has trivial stabilizer intersection, so the twofold
collision algebra suffices.

The new conclusion module does not manufacture the hidden-inertia
configuration.  The remaining substantive work is still the functorial
generic tensor decomposition, extension of its primitive idempotents to
the normalized collision algebra, the open immersion into
\(\operatorname{Norm}_N(Y)\), the boundary-module support theorem, and the
global planar rigidity theorem excluding a nontrivial cover whose
different is supported entirely in the deleted boundary.

## Cubic \(S_3\) contrast

The intended comparison is:

\[
\begin{array}{c|c}
\text{planar Keller target} &
\operatorname{Keller}(F)\Longrightarrow\operatorname{Obs}(F)=0
\\[2mm]
\text{separable non-Galois cubic class} &
\operatorname{Obs}(F)\neq0
\quad\text{when an off-diagonal collision occurs.}
\end{array}
\]

The cubic class is the intended dimension-three case study, but the
\(S_3\) mechanism comes from the degree-three field extension, not from
ambient dimension alone.

For such a map, strict containment

\[
I_R\subsetneq I_\Delta
\]

is equivalent to

\[
\ker(\bar\mu_F)\neq0,
\qquad
C_F^{\mathrm{off}}\neq0.
\]

Generically, suppose the associated function-field extension \(L/K\) is
separable, cubic, and non-Galois, with normal closure \(N/K\).  Then, as
\(L\)-algebras,

\[
L\otimes_KL\cong L\times N,
\]

where the first factor is the diagonal and
\(\operatorname{Gal}(N/K)\cong S_3\).  The original cubic sheet marks one
root; the off-diagonal fiber product marks a second distinct root; those
two roots determine the third.  Consequently, the function field of the
dominant normalized off-diagonal component is \(N\), the ordered-root
\(S_3\)-Galois closure.  It records the failure of

\[
F(u)=F(v)\Longrightarrow u=v.
\]

This is a conditional cubic-extension statement.  It is neither a
universal assertion that every three-dimensional collision relation has
\(S_3\)-monodromy nor, without a separately verified Keller hypothesis, a
counterexample to the three-dimensional Jacobian conjecture.
