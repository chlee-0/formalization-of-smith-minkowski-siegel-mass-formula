import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSOSurjectivity
import SMSFormula.RationalCliffordGeneralSpinAdelicSpecialOrthogonalQuotient

/-!
# Surjectivity of lattice general Spin onto adelic SO

The fieldwise real lift and the cofinally integral finite-adelic lift assemble
through the literal real--finite product equivalences.  Thus the actual
intrinsic `GSpin(A) -> SO(A)` map is surjective for the lattice form, and so
is its map on rational left quotients.  This is carrier exactness only; no
measure or Tamagawa assertion is made here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The actual full-adelic intrinsic `GSpin -> SO` map for a lattice form is
surjective in every rank at least two. -/
theorem fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom := by
  intro g
  let V := L.rationalQuadraticSpaceMatrix
  let gpair := V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g
  obtain ⟨xr, hxr⟩ :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective
      V ℝ gpair.1
  change V.realCliffordGeneralSpinToSpecialOrthogonalHom xr = gpair.1 at hxr
  obtain ⟨xf, hxf⟩ :=
    finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective L gpair.2
  let x : V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm (xr, xf)
  refine ⟨x, ?_⟩
  apply V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.injective
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_toSO]
  rw [show V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x = (xr, xf) by
    exact V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply
      (xr, xf)]
  change
    (V.realCliffordGeneralSpinToSpecialOrthogonalHom xr,
      V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom xf) = gpair
  rw [hxr, hxf]

/-- The horizontal map from the rational general-Spin quotient onto the
rational special-orthogonal quotient is surjective. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal := by
  let V := L.rationalQuadraticSpaceMatrix
  intro q
  refine Quot.inductionOn q ?_
  intro g
  obtain ⟨x, hx⟩ :=
    fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective L g
  refine ⟨V.fullAdelicCliffordGeneralSpinLeftQuotientMap x, ?_⟩
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk, hx]
  rfl

end PositiveDefiniteIntegralLattice
