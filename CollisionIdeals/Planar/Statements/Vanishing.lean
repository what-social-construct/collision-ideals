import CollisionIdeals.General.Automorphism.Statements
import CollisionIdeals.Planar.Basic

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The central planar vanishing statement:
the obstruction `I_Δ / I_R(F)` vanishes for every planar Keller map.

This definition records the theorem target without adding it as an axiom.
-/
abbrev PlanarVanishing : Prop :=
  ComplexKellerVanishing 2

end

end CollisionIdeals
