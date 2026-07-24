# Collision ideals and diagonal ideals

Let

\[
F=(F_1,\ldots,F_m):\mathbb A^n_{\mathbb C}\longrightarrow
\mathbb A^m_{\mathbb C}
\]

be a polynomial map.  In the coordinate ring of two copies of the source,

\[
S=\mathbb C[x_1,\ldots,x_n,y_1,\ldots,y_n],
\]

there are two canonical ideals:

\[
I_R(F)=\bigl(F_j(x)-F_j(y)\bigr)_{j=1}^m,
\qquad
I_\Delta=\bigl(x_i-y_i\bigr)_{i=1}^n.
\]

The project is organized around one question:

\[
\boxed{\text{When is }I_R(F)=I_\Delta?}
\]

## The obstruction

Every polynomial difference \(H(x)-H(y)\) belongs to \(I_\Delta\).  Hence

\[
I_R(F)\subseteq I_\Delta.
\]

Let \(A_F=S/I_R(F)\), the coordinate ring of the collision space.  The image

\[
J_F:=I_\Delta A_F
\]

is the obstruction ideal.  Equivalently, as an \(A_F\)-module it is
\(I_\Delta/I_R(F)\).  The central equality is exactly

\[
I_R(F)=I_\Delta
\quad\Longleftrightarrow\quad
J_F=0.
\]

Geometrically,

\[
\operatorname{Spec}(A_F)
=
\mathbb A^n\times_{\mathbb A^m}\mathbb A^n
\]

parametrizes ordered pairs with the same image under \(F\).  The closed
subscheme cut out by \(J_F\) is the diagonal.  Thus \(J_F=0\) says that the
self-fiber product is scheme-theoretically only the diagonal.

## Lean status

The current development is dimension-generic and proves:

- every polynomial difference lies in the diagonal ideal;
- the canonical containment \(I_R(F)\subseteq I_\Delta\);
- \(J_F=0\) if and only if \(I_R(F)=I_\Delta\);
- equality of the two ideals implies injectivity on points.
- a polynomial left inverse forces \(I_R(F)=I_\Delta\).

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
J_F=0
\quad
\text{(equivalently, }I_R(F)=I_\Delta\text{).}
}
\]

In Lean, `PlanarVanishing` records this proposition without assuming it as an
axiom.  Proving it is the unresolved two-dimensional Jacobian-conjecture
case; the repository keeps that boundary explicit.

The next formal step is the local theorem: for a Keller map, the diagonal is
an open-and-closed subscheme of the self-fiber product, so \(J_F\) is
supported on the off-diagonal complement.  The substantive planar step is
then to prove that this complement is empty.

## Dimension three: the contrasting narrative

In the known cubic-fiber counterexample in dimension three, the
off-diagonal collision obstruction does not vanish.  Generically, the map
has three sheets and a cubic fiber equation with \(S_3\)-Galois group.  The
off-diagonal component records ordered pairs of distinct sheets; its
Galois-closure description is the \(S_3\) phenomenon governing the failure
of

\[
F(u)=F(v)\Longrightarrow u=v.
\]

This final example is a contrast, not a universal assertion that every
three-dimensional collision relation has \(S_3\)-monodromy.

For the explicit counterexample and independent formal verification, see the
[Archive of Formal Proofs entry](https://isa-afp.org/entries/Jacobian_Counterexample.html).
For the cubic-fiber and \(S_3\) structure, see the
[ordered-root/Galois-closure account](https://mathoverflow.net/questions/513387/).
