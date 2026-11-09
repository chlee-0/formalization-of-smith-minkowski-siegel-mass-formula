import SMSFormula.RationalCliffordGeneralSpinVerticalFiberKernelInvariance
import SMSFormula.RationalCliffordGeneralSpinHorizontalMeasurableDescent

/-!
# Descent of the vertical Spin kernel to rational idele classes

For a lattice form of rank at least three, two ambient adelic `GSpin` origins
with the same rational idele class differ by a rational `GSpin` diagonal and
an adelic Spin point on the left.  The representative invariance theorem for
the ambient-source vertical kernel therefore makes its value constant on the
exact fibers of the ambient idele-class map.

The existing definition-only representatives already define the translated
vertical Spin measures.  Standard-Borel measurable descent proves that
this family is measurable, hence gives a genuine rational-idele-class-indexed
s-finite kernel whose pullback is the ambient-source kernel.  No measurable
section, Cartesian presentation, measure bind, or ambient Haar-scale
comparison is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open MeasurableSpace
open scoped ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- Two ambient adelic `GSpin` origins with the same rational idele class
differ on the left by a rational `GSpin` diagonal and an adelic Spin point. -/
theorem exists_rationalGeneralSpin_spin_mul_of_same_ideleClass
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {x y : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup}
    (hxy :
      QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            y) =
        QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            x)) :
    ∃ gamma : L.rationalQuadraticSpaceMatrix.RationalCliffordGeneralSpinGroup,
      ∃ s : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup,
        y =
          L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalHom
              gamma *
            L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom
              s * x := by
  let V := L.rationalQuadraticSpaceMatrix
  let z : V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x⁻¹
      (V.fullAdelicCliffordGeneralSpinLeftQuotientMap y)
  have hzneutral :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass z = 1 := by
    dsimp only [z]
    rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_rightMul,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk,
      map_inv, map_inv, hxy]
    exact mul_inv_cancel _
  have hzrange : z ∈ Set.range
      V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin :=
    (L.mem_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_iff_of_rankAtLeastThree
      hn z).2 hzneutral
  rcases hzrange with ⟨q, hq⟩
  let s : V.FullAdelicCliffordSpinCandidateGroup := Quot.out q
  have hsquot :
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s) =
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap (y * x⁻¹) := by
    calc
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s) =
          V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
            (V.fullAdelicCliffordSpinCandidateLeftQuotientMap s) := rfl
      _ = V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q := by
        rw [show V.fullAdelicCliffordSpinCandidateLeftQuotientMap s = q from
          Quot.out_eq q]
      _ = z := hq
      _ = V.fullAdelicCliffordGeneralSpinLeftQuotientMap (y * x⁻¹) := rfl
  have hrel : IsLeftCosetRelated
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s) (y * x⁻¹) :=
    (leftCoset_mk_eq_iff
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup _ _).mp hsquot
  rcases hrel with ⟨delta, hdelta⟩
  rcases delta.property with ⟨gamma, hgamma⟩
  refine ⟨gamma, s, ?_⟩
  calc
    y = (y * x⁻¹) * x := by simp [mul_assoc]
    _ = (delta : V.FullAdelicCliffordGeneralSpinGroup) *
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * x := by
      rw [hdelta]
    _ = V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma *
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * x := by
      rw [hgamma]

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

/-- The ambient-source vertical kernel is constant on the exact fibers of the
ambient rational idele-class map. -/
theorem verticalSpinFiberKernelAtAmbient_eq_of_same_ideleClass
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    {x y : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup}
    (hxy :
      QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            y) =
        QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            x)) :
    D.verticalSpinFiberKernelAtAmbient (V := L.rationalQuadraticSpaceMatrix) y =
      D.verticalSpinFiberKernelAtAmbient (V := L.rationalQuadraticSpaceMatrix) x := by
  rcases L.exists_rationalGeneralSpin_spin_mul_of_same_ideleClass hn hxy with
    ⟨gamma, s, rfl⟩
  exact D.verticalSpinFiberKernelAtAmbient_rationalDiagonal_spin_mul gamma s x

/-- Pulling the existing translated vertical Spin measure family back along
the ambient idele-class map recovers the measurable ambient-source kernel. -/
theorem verticalSpinFiberMeasure_ambient_projection
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj
        (QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            g)) =
      D.verticalSpinFiberKernelAtAmbient
        (V := L.rationalQuadraticSpaceMatrix) g := by
  let V := L.rationalQuadraticSpaceMatrix
  let c := QuotientGroup.mk'
    RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
    (V.fullAdelicCliffordGeneralSpinSimilitudeHom g)
  calc
    D.verticalSpinFiberMeasure V hsurj c =
        D.verticalSpinFiberKernelAtAmbient (V := V)
          (V.verticalGeneralSpinRepresentative hsurj c) :=
      (D.verticalSpinFiberKernelAtAmbient_verticalRepresentative hsurj c).symm
    _ = D.verticalSpinFiberKernelAtAmbient (V := V) g := by
      apply D.verticalSpinFiberKernelAtAmbient_eq_of_same_ideleClass L hn
      rw [V.verticalGeneralSpinRepresentative_ideleClass]

/-- The translated vertical Spin measures form a measurable family on the
rational idele-class base.  Measurability is descended from the already
measurable ambient-source kernel through the standard-Borel ambient group. -/
theorem measurable_verticalSpinFiberMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Measurable
      (D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj) := by
  let V := L.rationalQuadraticSpaceMatrix
  let f : V.FullAdelicCliffordGeneralSpinGroup →
      RationalQuadraticSpaceMatrix.RationalIdeleClassGroup := fun g =>
    QuotientGroup.mk'
      RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
      (V.fullAdelicCliffordGeneralSpinSimilitudeHom g)
  letI : StandardBorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupStandardBorelSpaceForMeasurableDescent
  letI : CountablyGenerated
      RationalQuadraticSpaceMatrix.RationalIdeleClassGroup :=
    BorelSpace.countablyGenerated
  letI : SeparatesPoints
      RationalQuadraticSpaceMatrix.RationalIdeleClassGroup := by
    infer_instance
  letI : CountablySeparated
      RationalQuadraticSpaceMatrix.RationalIdeleClassGroup :=
    countablySeparated_of_separatesPoints
  have hf : Measurable f := by
    have hquot : Measurable
        (QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup) :=
      RationalQuadraticSpaceMatrix.rationalIdeleClassQuotientMap_isCoveringMap
        |>.continuous.measurable
    exact hquot.comp
      V.continuous_fullAdelicCliffordGeneralSpinSimilitudeHom.measurable
  have hqsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap := by
    intro q
    induction q using Quot.inductionOn with
    | _ g => exact ⟨g, rfl⟩
  have hfsurj : Function.Surjective f := hsurj.comp hqsurj
  apply (hf.measurable_comp_iff_of_surjective hfsurj).mp
  have hcomp :
      D.verticalSpinFiberMeasure V hsurj ∘ f =
        fun g => D.verticalSpinFiberKernelAtAmbient (V := V) g := by
    funext g
    exact D.verticalSpinFiberMeasure_ambient_projection L hn hsurj g
  rw [hcomp]
  exact (D.verticalSpinFiberKernelAtAmbient (V := V)).measurable

/-- The genuine measurable s-finite vertical Spin kernel indexed by rational
idele classes. -/
noncomputable def verticalSpinFiberKernelAtIdeleClass
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    ProbabilityTheory.Kernel
      RationalQuadraticSpaceMatrix.RationalIdeleClassGroup
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  ⟨D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj,
    D.measurable_verticalSpinFiberMeasure L hn hsurj⟩

instance verticalSpinFiberKernelAtIdeleClass_apply_sFinite
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    SFinite (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c) := by
  change SFinite
    (D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj c)
  rw [← D.verticalSpinFiberKernelAtAmbient_verticalRepresentative hsurj c]
  infer_instance

@[simp]
theorem verticalSpinFiberKernelAtIdeleClass_apply
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalQuadraticSpaceMatrix.RationalIdeleClassGroup) :
    D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c =
      D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj c :=
  rfl

/-- Pulling the descended idele-class kernel back to any ambient origin
recovers the original measurable source kernel exactly. -/
theorem verticalSpinFiberKernelAtIdeleClass_ambient_projection
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    D.verticalSpinFiberKernelAtIdeleClass L hn hsurj
        (QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            g)) =
      D.verticalSpinFiberKernelAtAmbient
        (V := L.rationalQuadraticSpaceMatrix) g :=
  D.verticalSpinFiberMeasure_ambient_projection L hn hsurj g

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
