import SMSFormula.RationalCliffordGeneralSpinLatticeFullAdelicSOSurjectivity
import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalTorsor

/-!
# Horizontal fibers of the lattice general-Spin quotient

For the actual lattice form, the horizontal map from the rational adelic
general-Spin quotient is onto.  The central rational idele-class action is
associative and unital, and its orbit map identifies the idele-class group
with each fiber of the horizontal map.  This is the carrier-level torsor
needed for the horizontal crossed measure; no measure is chosen here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

@[simp]
theorem rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_one
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient 1 z = z := by
  induction z using Quot.inductionOn with
  | _ x =>
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele 1 * x) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap x
    simp

theorem rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_mul
    (c d : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient c
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient d z) =
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        (c * d) z := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
    induction d using QuotientGroup.induction_on with
    | _ b =>
      induction z using Quot.inductionOn with
      | _ x =>
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a *
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele b * x)) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele (a * b) * x)
        rw [map_mul, mul_assoc]

/-- For a fixed quotient point, its central idele-class orbit map is
injective. -/
theorem rationalIdeleClassOrbitMap_injective
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Function.Injective (fun c : RationalIdeleClassGroup =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient c z) := by
  intro c d hcd
  have hacted := congrArg
    (fun w => V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
      d⁻¹ w) hcd
  change
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient d⁻¹
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient c z) =
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient d⁻¹
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient d z)
    at hacted
  have hfixed :
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          (d⁻¹ * c) z = z := by
    rw [V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_mul,
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_mul]
        at hacted
    simpa using hacted
  have hone : d⁻¹ * c = 1 :=
    (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_eq_iff
      (d⁻¹ * c) z).1 hfixed
  exact (inv_mul_eq_one.mp hone).symm

/-- The fiber over the horizontal image of `z` is canonically equivalent,
after choosing `z` as its origin, to the rational idele-class group. -/
def rationalIdeleClassEquivHorizontalFiber
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    RationalIdeleClassGroup ≃
      {w : V.FullAdelicCliffordGeneralSpinLeftQuotient //
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w =
          V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z} where
  toFun c :=
    ⟨V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient c z,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_scalarAction c z⟩
  invFun w := Classical.choose
    ((V.fullAdelicCliffordGeneralSpinLeftQuotient_sameSO_iff_ideleClassOrbit
      z w.1).1 w.2.symm)
  left_inv c := by
    apply V.rationalIdeleClassOrbitMap_injective z
    exact (Classical.choose_spec
      ((V.fullAdelicCliffordGeneralSpinLeftQuotient_sameSO_iff_ideleClassOrbit
        z
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient c z)).1
        (V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_scalarAction
          c z).symm)).symm
  right_inv w := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((V.fullAdelicCliffordGeneralSpinLeftQuotient_sameSO_iff_ideleClassOrbit
        z w.1).1 w.2.symm)).symm

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Every horizontal `SO` quotient point has a general-Spin lift whose fiber
is explicitly an idele-class torsor. -/
theorem exists_generalSpinQuotient_horizontalFiber_equiv_ideleClass
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    ∃ z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient,
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z = q ∧
        Nonempty (RationalQuadraticSpaceMatrix.RationalIdeleClassGroup ≃
          {w : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient //
            L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w = q}) := by
  obtain ⟨z, hz⟩ :=
    fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L q
  refine ⟨z, hz, ⟨?_⟩⟩
  let V := L.rationalQuadraticSpaceMatrix
  let e := V.rationalIdeleClassEquivHorizontalFiber z
  exact
    { toFun := fun c => ⟨(e c).1, (e c).2.trans hz⟩
      invFun := fun w => e.symm ⟨w.1, w.2.trans hz.symm⟩
      left_inv := by
        intro c
        exact e.left_inv c
      right_inv := by
        intro w
        let wz : {u : V.FullAdelicCliffordGeneralSpinLeftQuotient //
            V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal u =
              V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z} :=
          ⟨w.1, w.2.trans hz.symm⟩
        have he : e (e.symm wz) = wz := e.right_inv wz
        have hev : (e (e.symm wz)).1 = wz.1 :=
          congrArg (fun u : {u : V.FullAdelicCliffordGeneralSpinLeftQuotient //
            V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal u =
              V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z} => u.1) he
        exact Subtype.ext hev }

end PositiveDefiniteIntegralLattice
