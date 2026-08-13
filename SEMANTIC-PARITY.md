# Planar semantic parity queue

This queue tracks the manuscript's planar reduction as two proved statements,
one missing morphism, and the existing divisorial endgame.  It is deliberately
conservative: an older declaration is not deleted merely because it is not on
the shortest current proof path.

## Deletion gate

An object may be removed only after all of the following hold:

1. its intended mathematical role has a proved replacement;
2. every Lean and manuscript consumer has migrated to that replacement;
3. the replacement has the same hypotheses, quantifiers, and conclusion on
   both sides of the manuscript/Lean boundary;
4. the compatibility or deprecation layer has no downstream consumers;
5. `lake build`, the manuscript build, and `git diff --check` all pass.

Until then, classify the object as `retain`, `compatibility`, or
`research-optional`; do not delete it.

## Semantic spine

For (T=A_N), a prime-order subgroup (C\leq G), and

\[
  \mathfrak J_C=\mathfrak a_C+\mathfrak j_C^{\mathrm{mov}},
  \qquad
  \mathcal P_C^{\mathrm{fm}}=H^1_{\mathfrak J_C}(T),
\]

the current research reduction is:

1. **Fixed--moving pole tower.**  If a height-one prime contains
   (\mathfrak J_C), then the localization of
   (\mathcal P_C^{\mathrm{fm}}) is
   (\operatorname{Frac}(T_{\mathfrak p})/T_{\mathfrak p}).
2. **Trace-dual bounded stage.**  The quotient
   (Q_{\mathrm{tr}}=T^\dagger/T) is finite and has bounded height-one
   poles.
3. **Missing Secant--Frame Trace Landing.**  The explicit first-jet
   secant--frame lattice has the nonzero denominator ideal
   (\mathfrak d_{C,1}^{\mathrm{sf}}).  Prove the coefficientwise inclusion
   (\mathfrak d_{C,1}^{\mathrm{sf}}\subseteq
   \mathfrak c_C^{\mathrm{tr}}), where
   (\mathfrak c_C^{\mathrm{tr}}=
   \{s:sR_C\subseteq T^\dagger\}).  Equivalently, prove the uniform trace
   identity (\operatorname{Tr}_{N/K}(srt)\in B) for all
   (s\in\mathfrak d_{C,1}^{\mathrm{sf}}), (r\in R_C), and (t\in T).
4. **Endgame.**  The resulting contradiction gives boundary separation,
   then no height-one ramification, purity, (N=K), and collision vanishing.

The secant--frame denominator ideal is constructed and nonzero; its inclusion
in the trace transporter remains open.  A merely nonzero intersection would
still be equivalent to boundary separation, because nonzero ideals in the
domain (T) have nonzero product.  The coefficientwise inclusion is likewise
logically equivalent to separation here; its proposed value is that it is a
prescribed trace identity tied to the finite secant--frame coefficients, not
an arbitrary existential bridge.  No established identity yet shows that
the first-jet choice is sufficient.

## Parity queue

| Priority | Semantic item | Manuscript | Lean | Action |
|---|---|---|---|---|
| P0 | Fixed, moving, and fixed--moving boundary ideals | proved | proved | retain stable API |
| P0 | Prime-order formulation of boundary separation | proved by Cauchy reduction | all nontrivial subgroups only | prove subgroup monotonicity and the prime-order equivalence |
| P0 | Fixed-locus containment versus inertia | stated as an iff | only actual inertia implies containment | prove the converse and then `Sep ↔ no height-one ramification` |
| P1 | (\mathcal P_C^{\mathrm{fm}}) | defined and analyzed | definition only | retain; formalize localization and support |
| P1 | DVR pole-tower calculation | proved | missing | add local-cohomology localization/Čech infrastructure and unboundedness |
| P1 | (S_2) vanishing and `Sep ↔ P=0` | proved | missing | formalize after the local calculation |
| P1 | Common map (\mathcal P_C^{\mathrm{fm}}\to N/T) | constructed by the open-complement sequence | missing | construct before typing the landing square |
| P2 | Trace dual (T^\dagger) | specialized and proved finite | generic carrier only | identify the generic object with Mathlib `Submodule.traceDual`, then specialize |
| P2 | (Q_{\mathrm{tr}}=T^\dagger/T\to N/T) | proved | missing | define quotient, finiteness, and ambient inclusion |
| P2 | Local inverse-different stage | proved | missing | reuse Mathlib different/trace-dual API; formalize tame exponent afterward |
| P2 | Finite local freeness of (T/B) | proved from surface CM and miracle flatness | not formalized | prove it or expose a narrowly scoped geometric interface |
| P3 | Explicit divided-difference secant matrix | defined canonically | explicit coefficientwise construction and its identities are proved in `Planar.ExplicitSecant`; legacy chosen data remain in use | migrate downstream secant consumers only after proving equivalence/compatibility |
| P3 | Conjugate secant evaluation | proved for actual (g\)-sheets | only generic collision-cocone vanishing | construct the (g\)-cocone and prove the (g\in H/g\notin H) formula |
| P3 | Inverse-Jacobian frame | defined and proved; extension preserves each (A_g), not (T) | polynomial frame and four duality identities are proved in `Planar.KellerFrame`; field extensions are missing | extend to (L,N) and conjugate rings |
| P3 | Secant--frame denominator candidate | first-jet lattice and nonzero denominator are proved; landing is open | generic nonzero finite-family denominator theorem is proved in `Research.SecantFrameDenominator`; the actual evaluated family is missing | construct the conjugate evaluated coefficient family and specialize without adding an existential bridge |
| P3 | Landing compatibility square | missing theorem | absent | define only after both ambient embeddings and the concrete multiplier exist |
| P4 | Landing implies separation | proved by the DVR contradiction | absent | formalize; injectivity of the landing map is not required |
| P4 | Purity/endgame | proved | forward implication formalized with explicit literature interfaces | retain and compose after P4 landing contradiction |

## Retain-until-gates inventory

These objects are not required by the minimal landing spine, but nothing is
deleted yet:

- `FinitePrincipalPartsControl`: a valid stronger, injective-comparison
  experiment.  The current landing map need not be injective, so mark this
  `research-optional`; remove it from active presentation only after the
  direct landing contradiction is formalized.
- `HasUniformIdealPowerAnnihilator` and
  `HasUniformFixedMovingBoundaryAnnihilator`: an alternate uniform-bound
  formulation.  Retain until the scalar landing mechanism supersedes all
  consumers.
- `LogarithmicInertia` and `CompletedTameRamification`: local diagnostics,
  not inputs to Statements I or II.  Retain as opt-in research until the
  candidate multiplier either uses or definitively bypasses them.
- Hilbert--Burch and the off-diagonal canonical module: a proved candidate
  secant input, but no comparison to (Q_{\mathrm{tr}}) currently consumes
  it.  Retain in the manuscript while that construction choice is open.
- `PlanarBoundaryCoherence`, `PlanarRamificationRigidity`, coverage, and
  no-hidden-inertia wrappers: equivalent endpoint/compatibility languages,
  not landing inputs.  Retain until their direct equivalences and consumer
  migrations are formalized.
- `BoundaryCoherenceBridge` and `RamificationRigidityBridge`: retain until
  actual Lean proofs replace them; do not replace them with a third landing
  bridge.

## Naming discipline

- Use (Q_{\mathrm{tr}}) for the target.  The canonical-module presentation
  is (Q_F^\omega=\omega_Z/T\eta_F\); it contains no secant construction by
  itself.
- The missing map is multiplication-compatible, not assumed injective.
- Height one belongs to localization, separation, and purity—not to the
  definitions of the fixed--moving ideal or principal-parts module.
- Exact inverse-different exponent (e-1) is useful local structure, but
  finiteness of (Q_{\mathrm{tr}}) already suffices for the contradiction.
