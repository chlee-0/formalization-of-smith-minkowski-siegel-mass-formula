import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalActionTopology
import SMSFormula.RationalSpecialOrthogonalAdelicSpinorNormDiagonal

/-!
# Freeness of the horizontal idele-class action

The central rational idele-class action on `GSpin(Q)\GSpin(A)` is free.
Together with the orbit description, each nonempty fiber
of the horizontal map to `SO(Q)\SO(A)` is therefore a torsor under
the rational idele-class group.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 300000

/-- The central scalar inclusion in intrinsic general Spin is injective. -/
theorem CliffordGeneralSpinIntrinsicPoint.scalarGroupHom_injective
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A) := by
  intro a b hab
  apply Units.ext
  apply V.cliffordCoordinateBaseChange_algebraMap_injective A
  have h := congrArg
    (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
      (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)) hab
  simpa only [CliffordGeneralSpinIntrinsicPoint.scalarGroupHom,
    CliffordGeneralSpinIntrinsicPoint.scalarMonoidHom,
    CliffordGeneralSpinIntrinsicPoint.ofScalar,
    CliffordGeneralSpinIntrinsicPoint.coe_scalarCliffordUnit] using h

/-- Equality in the rational adelic general-Spin left quotient is detected
by the relative element lying in the rational diagonal subgroup. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_eq_iff
    (x y : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap x =
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap y ↔
      y * x⁻¹ ∈ V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
  change Quot.mk
      (leftCosetSetoid
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) x =
      Quot.mk
        (leftCosetSetoid
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) y ↔ _
  rw [leftCoset_mk_eq_iff]
  constructor
  · rintro ⟨gamma, rfl⟩
    convert gamma.property using 1
    simp [mul_assoc]
  · intro h
    refine ⟨⟨y * x⁻¹, h⟩, ?_⟩
    simp [mul_assoc]

/-- The central rational idele-class action on the rational adelic
general-Spin quotient is free. -/
theorem rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_eq_iff
    (c : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        c z = z ↔ c = 1 := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
    induction z using Quot.inductionOn with
    | _ x =>
      constructor
      · intro h
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap x at h
        have hmem :=
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_eq_iff
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x) x).1 h
        have hscalar : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a⁻¹ ∈
              V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
          simpa [map_inv, mul_assoc] using hmem
        rcases hscalar with ⟨gamma, hgamma⟩
        have hgammaSO :
            CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                V ℚ gamma = 1 := by
          apply V.rationalSpecialOrthogonalFullAdelicDiagonalHom_injective
          calc
            V.rationalSpecialOrthogonalFullAdelicDiagonalHom
                (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                  V ℚ gamma) =
                V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
                  (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) :=
              (V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal
                gamma).symm
            _ = V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
                  (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                    V RationalAdele a⁻¹) := by rw [hgamma]
            _ = 1 := by
              have hk : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                  V RationalAdele a⁻¹ ∈
                    (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                      V RationalAdele).ker := by
                rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
                  V RationalAdele]
                exact ⟨a⁻¹, rfl⟩
              exact hk
            _ = V.rationalSpecialOrthogonalFullAdelicDiagonalHom 1 := by simp
        have hgammaKer : gamma ∈
            (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
              V ℚ).ker := hgammaSO
        rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
          V ℚ] at hgammaKer
        rcases hgammaKer with ⟨q, hq⟩
        have haInv : a⁻¹ = rationalUnitFullAdelicDiagonalHom q := by
          apply CliffordGeneralSpinIntrinsicPoint.scalarGroupHom_injective
            V RationalAdele
          calc
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V RationalAdele a⁻¹ =
                V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma :=
              hgamma.symm
            _ = V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
                  (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q) := by
              rw [hq]
            _ = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                  V RationalAdele
                    (rationalUnitFullAdelicDiagonalHom q) :=
              (V.rational_fullAdelic_diagonal_generalSpinScalar q).symm
        apply (QuotientGroup.eq_one_iff _).mpr
        refine ⟨q⁻¹, ?_⟩
        calc
          rationalUnitFullAdelicDiagonalHom q⁻¹ =
              (rationalUnitFullAdelicDiagonalHom q)⁻¹ := by simp
          _ = (a⁻¹)⁻¹ := by rw [haInv]
          _ = a := inv_inv a
      · intro hc
        have haClass : QuotientGroup.mk' rationalIdeleDiagonalSubgroup a = 1 :=
          hc
        have haMem : a ∈ rationalIdeleDiagonalSubgroup :=
          (QuotientGroup.eq_one_iff _).mp haClass
        rcases haMem with ⟨q, hq⟩
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap x
        rw [← hq, V.rational_fullAdelic_diagonal_generalSpinScalar]
        exact leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          ⟨V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q),
            ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q,
              rfl⟩⟩ x

end RationalQuadraticSpaceMatrix
