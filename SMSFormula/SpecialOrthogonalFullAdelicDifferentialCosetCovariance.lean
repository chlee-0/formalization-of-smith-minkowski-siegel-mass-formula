import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasureSum

/-!
# Covariance of the full-adelic differential coset measures

Ambient left multiplication permutes the quotient indices of the open
real/unrestricted, finite/integral stabilizer.  The discrepancy between the
chosen representative of the translated quotient class and the translated
chosen representative is a literal element of the stabilizer.  Left
invariance of the internally constructed stabilizer differential measure
therefore proves exact covariance of every one-coset ambient measure.

This module does not reindex the countable sum, assert ambient invariance or
Haar regularity, compare with reference Haar, form a quotient measure, or use
a Tamagawa theorem.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Ambient left multiplication as a permutation of the open stabilizer's
left-coset quotient index. -/
def fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.FullAdelicRealFiniteLatticeStabilizerCosetIndex ≃
      L.FullAdelicRealFiniteLatticeStabilizerCosetIndex where
  toFun :=
    Quotient.map' (fun x => g * x) fun a b hab => by
      apply QuotientGroup.leftRel_apply.mpr
      have hab' :=
        QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hab'
  invFun :=
    Quotient.map' (fun x => g⁻¹ * x) fun a b hab => by
      apply QuotientGroup.leftRel_apply.mpr
      have hab' :=
        QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hab'
  left_inv C := by
    induction C using Quotient.inductionOn'
    apply congrArg QuotientGroup.mk
    exact inv_mul_cancel_left g _
  right_inv C := by
    induction C using Quotient.inductionOn'
    apply congrArg QuotientGroup.mk
    exact mul_inv_cancel_left g _

/-- The quotient-index permutation sends the class of `x` to the class of
`g * x`. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g
        (x : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
      ((g * x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :=
  rfl

/-- The inverse quotient-index permutation sends the class of `x` to the
class of `g⁻¹ * x`. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv_symm_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g).symm
        (x : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
      ((g⁻¹ * x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :=
  rfl

/-- Ambient left multiplication maps a chosen stabilizer coset exactly onto
the chosen coset indexed by the explicit quotient permutation. -/
theorem image_fullAdelicRealFiniteLatticeStabilizerCoset_mul_left
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * x) ''
        L.fullAdelicRealFiniteLatticeStabilizerCoset C =
      L.fullAdelicRealFiniteLatticeStabilizerCoset
        (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C) := by
  ext x
  simp only [Set.mem_image,
    L.mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [←
      L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv_apply g y]
    exact congrArg
      (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g) hy
  · intro hx
    refine ⟨g⁻¹ * x, ?_, ?_⟩
    · rw [←
        L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv_symm_apply
          g x]
      calc
        (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g).symm
            (x : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
            (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g).symm
              (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
                g C) := congrArg _ hx
        _ = C :=
          (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
            g).symm_apply_apply C
    · exact mul_inv_cancel_left g x

/-- The discrepancy between the chosen representative of the translated
quotient class and the translated chosen representative, as an element of the
open stabilizer. -/
def fullAdelicRealFiniteLatticeStabilizerRepresentativeAdjustment
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
  ⟨(Quotient.out
      (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C))⁻¹ *
      g * Quotient.out C, by
    have hclass :
        ((Quotient.out
          (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C) :
          L.ConcreteFullAdelicSpecialOrthogonalGroup) :
            L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
          ((g * Quotient.out C :
            L.ConcreteFullAdelicSpecialOrthogonalGroup) :
              L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) := by
      calc
        ((Quotient.out
          (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C) :
          L.ConcreteFullAdelicSpecialOrthogonalGroup) :
            L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
            L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C :=
              Quotient.out_eq _
        _ =
            ((g * Quotient.out C :
              L.ConcreteFullAdelicSpecialOrthogonalGroup) :
                L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) := by
              calc
                L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
                    g C =
                    L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
                      g
                      ((Quotient.out C :
                        L.ConcreteFullAdelicSpecialOrthogonalGroup) :
                          L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :=
                  congrArg
                    (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
                      g)
                    (Quotient.out_eq C).symm
                _ = _ :=
                  L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv_apply
                    g (Quotient.out C)
    simpa only [mul_assoc] using
      (QuotientGroup.eq
        (s := L.fullAdelicRealFiniteLatticeStabilizerSubgroup)).mp hclass⟩

/-- Multiplying the translated chosen representative by the representative
adjustment recovers the translated original representative. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerRepresentativeAdjustment_identity
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    Quotient.out
        (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C) *
        (L.fullAdelicRealFiniteLatticeStabilizerRepresentativeAdjustment g C :
          L.ConcreteFullAdelicSpecialOrthogonalGroup) =
      g * Quotient.out C := by
  simp only [
    fullAdelicRealFiniteLatticeStabilizerRepresentativeAdjustment,
    mul_assoc, mul_inv_cancel_left]

/-- Every one-coset ambient differential measure is covariant under ambient
left multiplication, with its quotient index transformed by the explicit
quotient permutation. -/
theorem map_mul_left_fullAdelicRealFiniteAmbientCosetDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    Measure.map
        (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * x)
        (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C) =
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P
        (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C) := by
  let μ :=
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure P
  let a :=
    L.fullAdelicRealFiniteLatticeStabilizerRepresentativeAdjustment g C
  letI : Measure.IsMulLeftInvariant μ :=
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure_isMulLeftInvariant hP
  have hg :
      Measurable
        (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * x) :=
    (continuous_const.mul continuous_id).measurable
  have hC :
      Measurable
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out C * h) :=
    (continuous_const.mul continuous_subtype_val).measurable
  have htarget :
      Measurable
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out
            (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
              g C) * h) :=
    (continuous_const.mul continuous_subtype_val).measurable
  have ha :
      Measurable
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup => a * h) :=
    (continuous_const.mul continuous_id).measurable
  rw [
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_eq_map_mul_left P C,
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_eq_map_mul_left
      P
        (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C)]
  change
    Measure.map
        (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * x)
        (Measure.map
          (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
            Quotient.out C * h) μ) =
      Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out
            (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
              g C) * h) μ
  rw [Measure.map_map hg hC]
  change
    Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          g * (Quotient.out C * h)) μ =
      Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out
            (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
              g C) * h) μ
  have hfun :
      (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
        g * (Quotient.out C * h)) =
      (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
        Quotient.out
          (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g C) *
            (a * h)) := by
    funext h
    rw [← mul_assoc, ← mul_assoc]
    exact congrArg
      (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => x * h)
      (L.fullAdelicRealFiniteLatticeStabilizerRepresentativeAdjustment_identity
        g C).symm
  rw [hfun]
  calc
    Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out
            (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
              g C) * (a * h)) μ =
        Measure.map
          (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
            Quotient.out
              (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
                g C) * h)
          (Measure.map
            (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup => a * h)
            μ) := by
          simpa only [Function.comp_apply] using
            (Measure.map_map htarget ha).symm
    _ =
        Measure.map
          (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
            Quotient.out
              (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
                g C) * h) μ := by
          rw [map_mul_left_eq_self μ a]

end PositiveDefiniteIntegralLattice
