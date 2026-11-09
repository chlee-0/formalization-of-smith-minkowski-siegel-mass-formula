import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteAdelicStabilizerMeasure
import SMSFormula.SpecialOrthogonalRealLatticeReference

/-!
# Real/finite differential stabilizer product measure

The real differential Haar measure is multiplied directly with the
transported finite-adelic differential stabilizer measure.  The resulting
product retains the two internally fixed differential scales.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The transported real differential Haar is finite because the real special
orthogonal group is compact. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) :
    IsFiniteMeasure L.concreteRealSpecialOrthogonalDifferentialMeasure := by
  letI : Measure.IsHaarMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isHaarMeasure
  infer_instance

/-- The transported real differential Haar has positive, hence nonzero, total
mass. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ ≠ 0 := by
  letI : Measure.IsHaarMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isHaarMeasure
  exact ne_of_gt <| isOpen_univ.measure_pos
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ_nonempty

/-- The literal product of the real differential Haar and the transported
finite-adelic differential stabilizer measure. -/
noncomputable def realFiniteDifferentialStabilizerProductMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure
      (L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :=
  L.concreteRealSpecialOrthogonalDifferentialMeasure.prod
    (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P)

/-- The real/finite differential product has the literal product of the two
internally fixed total masses. -/
@[simp]
theorem realFiniteDifferentialStabilizerProductMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.realFiniteDifferentialStabilizerProductMeasure P Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  letI : IsFiniteMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
  letI : IsFiniteMeasure
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isFinite hP
  letI : SigmaFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure := by
    infer_instance
  letI : SFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) := by
    infer_instance
  rw [
    realFiniteDifferentialStabilizerProductMeasure,
    ← Set.univ_prod_univ,
    Measure.prod_prod,
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ P]

/-- The real/finite differential product has nonzero total mass. -/
theorem realFiniteDifferentialStabilizerProductMeasure_univ_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.realFiniteDifferentialStabilizerProductMeasure P Set.univ ≠ 0 := by
  rw [L.realFiniteDifferentialStabilizerProductMeasure_univ hP]
  exact mul_ne_zero
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P)

/-- The real/finite differential product measure itself is nonzero. -/
theorem realFiniteDifferentialStabilizerProductMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.realFiniteDifferentialStabilizerProductMeasure P ≠ 0 := by
  intro hzero
  apply L.realFiniteDifferentialStabilizerProductMeasure_univ_ne_zero hP
  rw [hzero]
  rfl

/-- A positive finite-place cutoff limit makes the literal real/finite product
a finite measure. -/
theorem realFiniteDifferentialStabilizerProductMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    IsFiniteMeasure
      (L.realFiniteDifferentialStabilizerProductMeasure P) := by
  letI : IsFiniteMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
  letI : IsFiniteMeasure
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isFinite hP
  letI : SigmaFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure := by
    infer_instance
  letI : SFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) := by
    infer_instance
  unfold realFiniteDifferentialStabilizerProductMeasure
  infer_instance

/-- Componentwise left invariance of the two differential factors makes their
literal product left invariant. -/
theorem realFiniteDifferentialStabilizerProductMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.IsMulLeftInvariant
      (L.realFiniteDifferentialStabilizerProductMeasure P) := by
  letI : IsFiniteMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
  letI : IsFiniteMeasure
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isFinite hP
  letI : SigmaFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure := by
    infer_instance
  letI : SFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isHaarMeasure.toIsMulLeftInvariant
  letI : Measure.IsMulLeftInvariant
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isMulLeftInvariant
      L P
  unfold realFiniteDifferentialStabilizerProductMeasure
  exact Measure.prod.instIsMulLeftInvariant

end PositiveDefiniteIntegralLattice
