import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidue
import SMSFormula.SkewAdjointPadicElementaryUniformCoordinateBallMeasure

/-!
# Form-coordinate mass of the odd-prime density kernel

The prescribed-level form-coordinate residue preimage decomposes the
odd-prime density source into finitely many translated uniform coordinate
balls.  Additive Haar invariance gives every fiber the same explicit mass,
so the source mass is the residue-image cardinality times that ball mass.

No residue-image cardinality is compared with a stabilizer-reduction or
associated-bilinear carrier in this module.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal

namespace Matrix

variable {n : ℕ}

local instance formCoordinateMassMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance formCoordinateMassBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Every translated form-adapted uniform coordinate ball is measurable. -/
theorem measurableSet_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    MeasurableSet
      (skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
        p k F hF hdet x) :=
  (isClopen_skewAdjointFormElementaryPadicUniformCoordinateBall
      p k F hF hdet).preimage
        (Homeomorph.addLeft (-x)).continuous |>.1.measurableSet

/-- Additive translation does not change the form-coordinate comparison mass
of a uniform coordinate ball. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_translatedUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
          p k F hF hdet x) =
      skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicUniformCoordinateBall
          p k F hF hdet) := by
  let μ := skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
  let translation :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    fun y ↦ -x + y
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointFormElementaryPadicCoordinateMeasure_isAddHaarMeasure
      p F hF hdet
  have htranslation : Measurable translation :=
    (continuous_const.add continuous_id).measurable
  have hmap : Measure.map translation μ = μ :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self (-x)
  have happly := congrArg
    (fun ν : Measure
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ↦
      ν (skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet)) hmap
  change
    (Measure.map translation μ)
        (skewAdjointFormElementaryPadicUniformCoordinateBall
          p k F hF hdet) =
      μ (skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet) at happly
  rw [Measure.map_apply htranslation
    (measurableSet_skewAdjointFormElementaryPadicUniformCoordinateBall
      p k F hF hdet)] at happly
  change
    skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
          p k F hF hdet x) =
      skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicUniformCoordinateBall
          p k F hF hdet) at happly
  exact happly

/-- Every translated form-coordinate level-`k` ball has the explicit mass
`p ^ (-k d)`. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_translatedUniformCoordinateBall_explicit
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
          p k F hF hdet x) =
      ((p : ℝ≥0∞) ^
        (k * Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F)))⁻¹ := by
  rw [skewAdjointFormElementaryPadicCoordinateMeasure_translatedUniformCoordinateBall,
    skewAdjointFormElementaryPadicCoordinateMeasure_uniformCoordinateBall]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The finite subtype of form-coordinate residues attained by the selected
density source. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  ↥(L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
    p)

/-- A chosen integral density-source center attaining a specified residue in
the actual residue image. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      p) :
    skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero :=
  Classical.choose a.2

/-- The chosen residue center lies in the integral density source. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
        p a ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
        p :=
  (Classical.choose_spec a.2).1

/-- The chosen center reduces to the specified residue. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      p) :
    skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
          p a) =
      a.1 :=
  (Classical.choose_spec a.2).2

/-- The translated level-`r` form-coordinate ball attached to one attained
residue. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      p) :
    Set
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      p)
    L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      p a).1

/-- Balls attached to distinct attained residues are disjoint. -/
theorem
    pairwise_disjoint_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Pairwise fun a b :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          p ↦
      Disjoint
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
          p a)
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
          p b) := by
  intro a b hab
  rw [Set.disjoint_left]
  intro X hXa hXb
  let ca :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      p a
  let cb :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      p b
  have hdiffa : X - ca.1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    (mem_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall_iff
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero ca.1 X).1 hXa
  have hdiffaL :=
    skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero hdiffa
  have hXL : X ∈
      skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
    have h :=
      (skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero).add_mem hdiffaL ca.2
    have heq : (X - ca.1) + ca.1 = X := by abel
    rwa [heq] at h
  let XL : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero := ⟨X, hXL⟩
  have hreda :=
    (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero ca XL).2 hXa
  have hredb :=
    (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero cb XL).2 hXb
  apply hab
  apply Subtype.ext
  calc
    a.1 = skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ca :=
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
        p a).symm
    _ = skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero XL := hreda.symm
    _ = skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero cb := hredb
    _ = b.1 :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
        p b

/-- The union of the translated balls indexed by attained residues is exactly
the ambient odd-prime density source. -/
theorem
    iUnion_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall_eq_ambientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    (⋃ a :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          p,
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
        p a) =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  ext X
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨a, hXa⟩
    let ca :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
        p a
    have hdiff : X - ca.1 ∈
        skewAdjointFormElementaryPadicUniformCoordinateBall
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            p)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero :=
      (mem_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall_iff
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ca.1 X).1 hXa
    have hadd :=
      (L.add_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_add_pairingDeterminantVal
        p hp2 ca.1 (X - ca.1) hdiff).2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
          p a)
    have heq : ca.1 + (X - ca.1) = X := by abel
    rwa [heq] at hadd
  · intro hX
    let XL :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinatePoint
        p hp2 ⟨X, hX⟩
    have hres :
        skewAdjointFormElementaryPadicCoordinateReduction
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              p)
            L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero XL ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
            p :=
      ⟨XL, hX, rfl⟩
    let a :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          p :=
      ⟨skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            p)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero XL,
        hres⟩
    rw [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    apply
      (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
          p a) XL).1
    rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
      p a]

/-- The form-coordinate comparison mass of the odd-prime density source is
the number of attained residues times the explicit mass of one level-`r`
fiber. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_residueImage_ncard_mul
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    skewAdjointFormElementaryPadicCoordinateMeasure
        p L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          p).ncard *
        ((p : ℝ≥0∞) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              p *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
  letI : Fintype
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        p) :=
    (L.finite_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      p).fintype
  rw [←
    L.iUnion_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall_eq_ambientSet
      p hp2]
  calc
    skewAdjointFormElementaryPadicCoordinateMeasure
        p L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (⋃ a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            p,
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
            p a) =
        ∑' a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            p,
          skewAdjointFormElementaryPadicCoordinateMeasure
            p L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
              p a) := by
      exact measure_iUnion
        (fun a b hab ↦
          L.pairwise_disjoint_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
            p hab)
        (fun a ↦
          measurableSet_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              p)
            L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
              p a).1)
    _ = ∑ a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            p,
        ((p : ℝ≥0∞) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              p *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro a _
      exact
        skewAdjointFormElementaryPadicCoordinateMeasure_translatedUniformCoordinateBall_explicit
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            p)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
            p a).1
    _ =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          p).ncard *
        ((p : ℝ≥0∞) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              p *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
      have hcard :
          Fintype.card
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
                p) =
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              p).ncard := by
        rw [Set.ncard_eq_toFinset_card']
        simp
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ, hcard]

end PositiveDefiniteIntegralLattice
