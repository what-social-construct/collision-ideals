# Collision ideals and diagonal ideals

Let

$$
F=(F_1,\ldots,F_n):\mathbb A^n_{\mathbb C}\longrightarrow
\mathbb A^n_{\mathbb C}
$$

be a polynomial map.  In the coordinate ring of two copies of the source,

$$
S=\mathbb C[x_1,\ldots,x_n,y_1,\ldots,y_n],
$$

there are two canonical ideals:

$$
I_R(F)=\bigl(F_i(x)-F_i(y)\bigr)_{i=1}^n,
\qquad
I_\Delta=\bigl(x_i-y_i\bigr)_{i=1}^n.
$$

Every polynomial difference vanishes on the diagonal, so there is a
canonical inclusion

$$
I_R(F)\subseteq I_\Delta
$$

and therefore a canonical $S/I_R(F)$-module

$$
\operatorname{Obs}(F):=I_\Delta/I_R(F).
$$

Thus $\operatorname{Obs}(F)$ is not an additional independent object: it
is the canonical defect module in the exact sequence

$$
0\longrightarrow I_R(F)\longrightarrow I_\Delta
\longrightarrow\operatorname{Obs}(F)\longrightarrow0.
$$

Equivalently, let

$$
\bar\mu_F:S/I_R(F)\longrightarrow
\mathbb C[x_1,\ldots,x_n],
\qquad
[f]_{I_R}\longmapsto f(x,x),
$$

be diagonal evaluation on the collision ring.  Since the kernel of
diagonal evaluation on $S$ is $I_\Delta$, we have

$$
\boxed{
\ker(\bar\mu_F)=\operatorname{Obs}(F)=I_\Delta/I_R(F),
}
$$

so there is a second canonical exact sequence

$$
0\longrightarrow\operatorname{Obs}(F)
\longrightarrow S/I_R(F)
\xrightarrow{\bar\mu_F}\mathbb C[x_1,\ldots,x_n]
\longrightarrow0.
$$

The purpose of this project is to study the vanishing of
$\operatorname{Obs}(F)$.
Since $I_R(F)\subseteq I_\Delta$, the elementary module criterion gives

$$
\operatorname{Obs}(F)=0
\quad\Longleftrightarrow\quad
I_R(F)=I_\Delta.
$$

## Automorphism criterion

Over $\mathbb C$, the quotient has a direct interpretation:

$$
\boxed{
F\text{ is a polynomial automorphism}
\quad\Longleftrightarrow\quad
\operatorname{Obs}(F)=0.
}
$$

If $F$ has a polynomial inverse, applying the inverse to the two output
tuples gives $I_\Delta\subseteq I_R(F)$.  Conversely, vanishing gives
$I_R(F)=I_\Delta$, hence injectivity on complex points; Ax–Grothendieck
then gives a polynomial automorphism.

The Lean proposition `PlanarJacobianConjecture` records the usual
automorphism formulation.  The proposition `PlanarAxGrothendieck` records
the injective-polynomial-map automorphism principle as an explicit
interface.  Lean proves the canonical formulation directly:

```text
PlanarAxGrothendieck →
  (PlanarJacobianConjecture ↔ PlanarVanishing)
```

in `planarJacobianConjecture_iff_planarVanishing`.  For each individual
map, `collisionDiagonal_ker` identifies the kernel of $\bar\mu_F$ with
the obstruction ideal.

The dimension-independent automorphism and Jacobian-conjecture interfaces
live in `AutomorphismCriterion` and `JacobianConjecture`; the planar file
is only their $n=2,\ k=\mathbb C$ specialization.

All literature interfaces, including the standard Ax–Grothendieck
instance, are listed together in the canonical planar spine below.

Geometrically, if $A_F=S/I_R(F)$, then

$$
\operatorname{Spec}(A_F)
=
\mathbb A^n\times_{\mathbb A^n}\mathbb A^n
$$

parametrizes ordered pairs with the same image under $F$.  The closed
subscheme cut out by $\operatorname{Obs}(F)$, regarded as an ideal of
$A_F$, is the diagonal.  Thus $\operatorname{Obs}(F)=0$ says that the
self-fiber product is scheme-theoretically only the diagonal.

## Universal property

The construction is dimension-generic.  Put

$$
A=R[x_i]_{i\in\iota},\qquad B=R[t_j]_{j\in\kappa},
\qquad t_j\longmapsto F_j.
$$

For every commutative $R$-algebra $T$, the collision quotient satisfies

$$
\operatorname{Hom}_{R\text{-alg}}(S/I_R(F),T)
\cong
\left\{
(f,g):A\rightrightarrows T:
f(F_j)=g(F_j)\text{ for every }j
\right\}.
$$

Consequently there is a canonical equivalence

$$
S/I_R(F)\cong A\otimes_BA.
$$

This universal construction does not assert vanishing.  The planar target
asks for the off-diagonal factor to vanish.  Under the explicit separable
cubic normal-closure conditions formalized here, the generic collision
algebra decomposes as $L\otimes_KL\simeq L\times N$, and the same residual
field satisfies $\operatorname{Gal}(N/K)\simeq S_3$.  No concrete
three-dimensional Keller counterexample is asserted.

## Lean status

The current development is dimension-generic and proves:

- every polynomial difference lies in the diagonal ideal;
- the canonical containment $I_R(F)\subseteq I_\Delta$;
- the universal property of the collision quotient;
- the canonical equivalence $S/I_R(F)\simeq A\otimes_BA$;
- the obstruction ideal is the kernel of the diagonal map
  $S/I_R(F)\to A$;
- $\operatorname{Obs}(F)=0$ if and only if $I_R(F)=I_\Delta$;
- equality of the two ideals implies injectivity on points;
- a polynomial left inverse forces $I_R(F)=I_\Delta$;
- the abstract secant-determinant identities and resulting idempotent
  decomposition;
- a concrete planar secant decomposition whose chosen determinant restricts
  to the planar Jacobian determinant;
- for planar Keller maps,
  $I_R:I_\Delta=I_R+(\delta_F)$ and
  $I_R=I_\Delta\iff I_R+(\delta_F)=S$;
- the concrete secant projector witnessing that the planar collision
  diagonal is a clopen factor;
- saturation stabilizes at $I_R:I_\Delta$ when the diagonal is clopen;
- the complementary-ideal identities and Chinese-remainder sheet
  decomposition;
- the affine off-diagonal collision scheme
  $R_F^\circ=\operatorname{Spec}(S/(I_R:I_\Delta))$;
- the canonical identification of $\operatorname{Spec}(S/I_R)$ with
  the categorical affine self-fiber product $X\times_YX$;
- the concrete planar function fields
  $K=\mathbb C(P,Q)\subset L=\mathbb C(x,y)$, a finite normal-closure
  interface $L\hookrightarrow N$, and the fixing subgroup
  $H=\operatorname{Gal}(N/L)$;
- the normalized affine models
  \[
  Z=\operatorname{Norm}_N(Y)\longrightarrow
  \overline X=\operatorname{Norm}_L(Y)\longrightarrow Y
  \]
  and the commuting normalization triangle;
- the dimension-independent double-coset index on
  $D_E\backslash G/H$, with its planar type specialization;
- a supplied height-one normalization diagram recording divisorial
  valuations and their conjugate centers;
- a separate supplied realization identifying its group-theoretic index
  with the geometric ramification index
  $[I_E:I_E\cap gHg^{-1}]$;
- from the supplied Keller-to-étale bridge and ramification realization,
  the theorem placing every positive-index conjugate center in the deleted
  boundary, kept separate from `PlanarNoHiddenInertia`;
- the conditional composition from no hidden inertia through branch
  purity and finite-étale rigidity to `PlanarVanishing`;
- the dimension-generic function-field bridge
  $K\otimes_B(S/I_R)\simeq L\otimes_KL$, under the explicit
  generic-source surjectivity condition;
- for a separable cubic power-basis extension, the proved CRT decomposition
  $L\otimes_KL\simeq L\times\operatorname{AdjoinRoot}(\operatorname{minpolyDiv})$, with first
  projection equal to diagonal multiplication;
- a compatible nontrivial second factor in the generic collision algebra
  descends, by flatness of $K=\operatorname{Frac}(B)$, to
  $\operatorname{Obs}(F)\ne0$ and $I_R(F)\subsetneq I_\Delta$;
- under explicit residual-field, degree-three, marked-normal-closure,
  marked-embedding compatibility, and nontrivial-fixing-subgroup
  conditions, the same residual field $N$ satisfies
  $\operatorname{Gal}(N/K)\simeq S_3$;
- for $F:\mathbb A^3_{\mathbb C}\to\mathbb A^3_{\mathbb C}$, the theorem
  `complexThreeCubicS3Collision` packages the Keller condition, the
  generic decomposition $K\otimes_BC_F\simeq L\times N$, the $S_3$
  certificate, `IsComplexThreeJacobianCounterexample F`, nonemptiness of
  the off-diagonal collision scheme, and strict containment
  $I_R(F)\subsetneq I_\Delta$;
- from the clopen-projector datum, the scheme coproduct decomposition
  $\operatorname{Spec}(S/I_R)\cong\operatorname{Spec}(S/I_\Delta)\sqcup R_F^\circ$;
- emptiness of $R_F^\circ$, vanishing of the obstruction ideal, and
  equality $I_R=I_\Delta$ are equivalent;
- assuming the explicit Ax–Grothendieck interface, the standard planar
  Jacobian conjecture is equivalent to `PlanarVanishing`.

The definitions are generic in the coefficient ring, source variables, and
output coordinates.  The planar specialization uses
`R := ℂ` and `Fin 2`.

Build the project with:

```bash
lake build
```

## Canonical planar dependency spine

The planar development has one preferred route.  Its map-specific package is

```text
PlanarKellerCollisionModel F
```

and its global geometric condition is supplied separately as

```text
PlanarNoHiddenInertia M.diagram
```

This separation is intentional.  Once the model supplies the
Keller-to-étale bridge and the ramification realization, its Keller
certificate forces ramified centers into the boundary.  It does not prove
that the boundary cannot support such ramification.

The canonical modules are:

| Stage | Main module | Role |
|---|---|---|
| automorphism criterion | `AutomorphismCriterion`, `JacobianConjecture` | dimension-independent obstruction detection and conjecture interface |
| planar map | `Planar.Basic` | polynomials, Jacobian determinant, Keller condition |
| vanishing target | `Planar.Vanishing` | obstruction and collision-ideal equality |
| finite models | `NormalClosure`, `PolynomialNormalization` | dimension-independent $K\subseteq L\subseteq N$ and $Z\to\overline X\to Y$ |
| planar notation | `Planar.Normalization` | thin $n=2,\ k=\mathbb C$ specialization |
| inertia | `ValuationInertia` | dimension-independent divisorial valuations and inertia kernels |
| conjugate sheets | `DecompositionSheets` | dimension-independent $D_E\backslash G/H$ classes and sheet index |
| geometric centers | `PolynomialNormalizationDiagram`, `Planar.NormalizationDiagram` | shared centers/boundary predicates and the planar no-hidden-inertia target |
| ramification realization | `VisibleRamification` | dimension-independent identification of sheet and geometric ramification indices |
| Keller local geometry | `KellerGeometry` | dimension-generic Keller-to-étale and Keller-to-flat bridges |
| Keller collision model | `KellerCollisionModel` | dimension-generic package of the supplied normalization and local-geometry data |
| generic degree one | `GenericDegreeOne` | dimension-generic descent from $L=K$ and flatness to obstruction vanishing |
| literature interfaces | `Planar.ExternalAssumptions` | branch purity, finite-étale rigidity, Ax–Grothendieck |
| composition | `Planar.ConditionalVanishing` | the conditional planar vanishing and automorphism theorems |
| secant projector | `Planar.Secant` | planar construction of $q_F$ from the secant determinant |
| endpoint API | `Planar.Conclusion` | packaged consequences |

`Planar.Secant` is an independent algebraic entry point into the same
off-diagonal factor.  It constructs the secant projector and proves the
colon-ideal criterion described below.

### The map-specific model

`PlanarKellerCollisionModel F` is the $n=2,\ k=\mathbb C$
abbreviation of the dimension-independent
`PolynomialKellerCollisionModel F`.  It contains:

- the explicit Keller certificate;
- a finite normal-closure field $N/K$;
- the normalization diagram;
- the Keller-to-étale and Keller-to-flat bridges;
- the valuation formula realizing double-coset indices as ramification
  indices.

The generic-degree-one descent from $L=K$, together with the model's
Keller-to-flat bridge, to $\operatorname{Obs}(F)=0$ is proved in
`GenericDegreeOne`; it is not stored as opaque data in the model.

It does **not** contain planar no-hidden-inertia rigidity.  That assertion
is a separate condition, so the local consequence of Keller étaleness and
the global planar rigidity input cannot be conflated.

### From Keller étaleness to the boundary

For a ramified height-one point $E$ of the normal cover and a conjugate
sheet $q\in D_E\backslash G/H$, let

$$
\iota_E(q)
=
[I_E:I_E\cap gHg^{-1}]
$$

be the relative inertia index.  The normalization diagram records the
corresponding center $\overline q$ on the intermediate finite model.
The predicate

```text
RamifiedConjugateCentersInBoundaryAt E
```

means

$$
\forall q,\qquad
\iota_E(q)\ne1
\Longrightarrow
\overline q\in\overline X\setminus X.
$$

Its family version is

```text
RamifiedConjugateCentersInBoundary.
```

The theorem

```text
ramifiedConjugateCentersInBoundary_of_keller
```

is the exact Keller contribution.  It combines the double-coset visibility
calculation, the valuation realization, and étaleness of the conjugate
affine sheet to place every positive-index center in the deleted boundary.

### The separate planar rigidity assertion

The existence of one complete hidden orbit is

```text
HasHiddenInertiaOrbit :=
  ∃ E,
    (∃ q, 1 < inertiaIndex E q) ∧
    RamifiedConjugateCentersInBoundaryAt E.
```

The planar assertion is its negation:

```text
PlanarNoHiddenInertia := ¬ HasHiddenInertiaOrbit.
```

Thus the logical step is short and explicit:

$$
\begin{aligned}
&\texttt{RamifiedConjugateCentersInBoundary},\\
&\texttt{core}(H)=1
  \Longrightarrow \text{a positive-index conjugate sheet exists},\\
&\texttt{PlanarNoHiddenInertia}
\end{aligned}
\quad\Longrightarrow\quad
\text{there are no ramified height-one points.}
$$

In Lean this is

```text
M.diagram.noCodimensionOneRamification.
```

There is no separate planar visible-subset condition or parallel planar
hidden-inertia model in the canonical route; the reusable generic
visible-sheet API remains available.

### Downstream conditional theorem

Once height-one ramification is absent, the remaining arrows are:

$$
\begin{array}{c}
\text{no codimension-one ramification}\\
\downarrow\quad\text{branch purity}\\
Z\to Y\text{ is finite étale}\\
\downarrow\quad\text{finite-étale rigidity of }\mathbb A^2_{\mathbb C}\\
N=K\\
\downarrow\\
L=K\\
\downarrow\quad\text{generic collision descent using }A/B\text{ flat}\\
R_F^\circ=\varnothing\\
\downarrow\\
\operatorname{Obs}(F)=0\\
\downarrow\\
I_R(F)=I_\Delta.
\end{array}
$$

Ax–Grothendieck is used only after this chain, to pass from injectivity to
a polynomial automorphism.

The three standard literature results not presently supplied by mathlib are
isolated once, in `Planar.ExternalAssumptions`:

```text
branchPurityA2
affinePlaneFiniteEtaleRigidity
axGrothendieckA2
```

They are the only project axioms in this route.  The no-hidden-inertia
statement is not hidden among them: it remains the explicit map-specific
planar condition passed to the conditional theorem.

The principal exported statements are schematically:

```text
planarVanishing_of
  branchPurity
  finiteEtaleRigidity
  model
  noHiddenInertia :
  obstructionIdeal F = ⊥

planarVanishing_assuming_standardGeometry
  model
  noHiddenInertia :
  obstructionIdeal F = ⊥

planarAutomorphism_assuming_externalLiterature
  model
  noHiddenInertia :
  IsPolynomialAutomorphism F
```

This is the complete conditional dependency statement.  The fully
parameterized theorem `planarVanishing_of` displays the geometric
interfaces in its signature.  The two convenience wrappers use the named
literature axioms internally; those dependencies are visible with
`#print axioms`.

### Secant and off-diagonal formulations

Choose a secant matrix $M_F(x,y)$ satisfying

$$
F(x)-F(y)=M_F(x,y)(x-y)
$$

and let $\delta_F=\det M_F$.  For a planar Keller map with
$\det JF=c\in\mathbb C^\times$,

$$
\delta_F I_\Delta\subseteq I_R(F),
\qquad
\delta_F\equiv c\pmod {I_\Delta}.
$$

In the collision ring $A_F=S/I_R(F)$, this produces the idempotent

$$
q_F=1-\frac{\overline\delta_F}{c}
$$

with

$$
\operatorname{Obs}(F)=A_Fq_F.
$$

The complementary ideal in the polynomial ring is canonical:

$$
I_{\mathrm{off}}
=I_R:I_\Delta
=I_R+(\delta_F).
$$

Consequently,

$$
\boxed{
\operatorname{Obs}(F)=0
\Longleftrightarrow
I_R(F)=I_\Delta
\Longleftrightarrow
I_R+(\delta_F)=S
\Longleftrightarrow
R_F^\circ=\varnothing.
}
$$

The secant construction gives the clopen diagonal/off-diagonal
decomposition.  The planar no-hidden-inertia route is what conditionally
forces the off-diagonal factor to vanish.

### Public planar modules

`CollisionIdeals.Planar` exposes exactly the dependency spine in the table
above.  The normalization diagram and its no-hidden-inertia predicate form
the single planar boundary API.

## Cubic $S_3$ contrast

The intended comparison is:

$$
\begin{array}{c|c}
\text{conditional planar Keller target} &
\operatorname{Keller}(F)+\text{normalization model}
+\text{no hidden inertia}
\Longrightarrow\operatorname{Obs}(F)=0
\\[2mm]
\text{separable non-Galois cubic class} &
\operatorname{Obs}(F)\neq0
\quad\text{under the cubic residual/Galois conditions.}
\end{array}
$$

The cubic class is the intended dimension-three case study, but the
$S_3$ mechanism comes from the degree-three field extension, not from
ambient dimension alone.

For such a map, strict containment

$$
I_R\subsetneq I_\Delta
$$

is equivalent to

$$
\ker(\bar\mu_F)\neq0,
\qquad
C_F^{\mathrm{off}}\neq0.
$$

Generically, suppose the associated function-field extension $L/K$ is
separable, cubic, and non-Galois, with normal closure $N/K$.  Then, as
$L$-algebras,

$$
L\otimes_KL\cong L\times N,
$$

where the first factor is the diagonal and
$\operatorname{Gal}(N/K)\cong S_3$.  The original cubic sheet marks one
root; the generic off-diagonal factor marks a second distinct root; those
two roots determine the third.  Thus the generic factor is the ordered-root
$S_3$-Galois closure $N$.  The formal theorem requires that the marked
embedding in `NormalClosureData` agree with the $L$-algebra structure
used for this residual factor.  It identifies $N$ at the generic
base-changed level; it does not assert an equivalence
$\operatorname{Frac}(C_F^{\mathrm{off}})\simeq N$.
The nonzero generic kernel nevertheless descends to the affine
obstruction and records the failure of

$$
F(u)=F(v)\Longrightarrow u=v.
$$

The dimension-three specialization is organized by
`ComplexThree.FunctionField`, `ComplexThree.S3Collision`,
`ComplexThree.CubicGaloisGroup`, and `ComplexThree.CubicS3`.

This is a conditional cubic-extension statement.  It is neither a
universal assertion that every three-dimensional off-diagonal collision locus has
$S_3$-monodromy nor, without a separately verified Keller condition, a
counterexample to the three-dimensional Jacobian conjecture.

## License

The Lean source and other software in this repository are available under
the [MIT License](LICENSE).  The manuscript and other non-code material in
[`paper/`](paper/) are available under
[CC BY 4.0](paper/LICENSE).
