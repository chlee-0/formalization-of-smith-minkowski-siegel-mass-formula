import SMSFormula.PadicCayleyTranslatedChartDifferentialHaar
import SMSFormula.LocalOrthogonalHaar

/-!
# The integral special-orthogonal stabilizer for corrected p-adic differential Haar

The determinant-one integral stabilizer already occurs in
`LocalOrthogonalHaar` as a kernel inside the ordinary integral orthogonal
stabilizer.  This file presents the same matrices directly as a compact-open
subgroup of the special-orthogonal group on which the corrected differential
Haar measure lives.

The resulting volume is finite and strictly positive.  Its numerical value is
not computed here, and no comparison with a separately normalized reference
Haar measure is used.
-/

noncomputable section

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral lattice stabilizer, now regarded directly as a subgroup of
the p-adic special-orthogonal group carrying the corrected differential Haar
measure. -/
def localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subgroup
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  (localPadicIntegralMatrixUnitsSubgroup p n).comap
    ((formPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).subtype.comp
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).subtype)

@[simp]
theorem mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ↔
      (g.1.1 : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) ∈
        localPadicIntegralMatrixUnitsSubgroup p n :=
  Iff.rfl

/-- Membership in the corrected special stabilizer is exactly the usual
entrywise p-adic integrality condition on a matrix and its inverse. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ↔
      (∀ i j, g.1.1.1 i j ∈ PadicInt.subring p) ∧
        (∀ i j, (g.1.1⁻¹).1 i j ∈ PadicInt.subring p) := by
  exact mem_localPadicIntegralMatrixUnitsSubgroup_iff p n g.1.1

/-- The rational form matrix mapped to `ℚ_[p]` is the local p-adic form
matrix, the pairing matrix over `ℚ_[p]`. -/
theorem rationalFormMatrix_map_padic_eq_pairingMatrix_padicField
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) =
      L.pairingMatrix_padicField p := by
  ext i j
  simp [rationalFormMatrix, pairingMatrix_padicField, pairingMatrix_padic]

/-- The direct corrected stabilizer has exactly the same underlying matrices
as the original determinant-one kernel inside the ordinary stabilizer. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_exists_historical
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ↔
      ∃ h : L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p,
        h.1.1.1 = g.1.1 := by
  constructor
  · intro hg
    let go : L.ConcreteLocalPadicOrthogonalGroup p := ⟨g.1.1, by
      have hpres :
          g.1.1.1ᵀ *
              L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
              g.1.1.1 =
            L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) :=
        g.1.2
      change
        g.1.1.1ᵀ * L.localPadicFormMatrix p * g.1.1.1 =
          L.localPadicFormMatrix p
      change
        g.1.1.1ᵀ * L.pairingMatrix_padicField p * g.1.1.1 =
          L.pairingMatrix_padicField p
      let hmatrix :=
        L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p
      calc
        g.1.1.1ᵀ * L.pairingMatrix_padicField p * g.1.1.1 =
            g.1.1.1ᵀ *
                L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
                g.1.1.1 :=
          congrArg (fun F ↦ g.1.1.1ᵀ * F * g.1.1.1) hmatrix.symm
        _ = L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) := hpres
        _ = L.pairingMatrix_padicField p := hmatrix⟩
    have hgint : go ∈ L.localPadicLatticeStabilizerSubgroup p := by
      exact hg
    let gi : L.localPadicLatticeStabilizerSubgroup p := ⟨go, hgint⟩
    have hdet : gi.1.1.1.det = 1 :=
      (mem_specialFormPreservingMatrixSubgroup_iff
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) g.1).mp g.2
    let h :
        L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p :=
      ⟨gi,
        (L.mem_localPadicSpecialOrthogonalLatticeStabilizerSubgroup_iff
          p gi).mpr hdet⟩
    exact ⟨h, rfl⟩
  · rintro ⟨h, hmatrix⟩
    rw [mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff]
    rw [← hmatrix]
    exact h.1.2

/-- The determinant-one form-preserving subgroup is closed inside the
ordinary form-preserving group. -/
theorem isClosed_localPadicSpecialOrthogonalMatrixSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsClosed
      (specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) :
        Set (formPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])))) := by
  have hset :
      (specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) :
        Set (formPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])))) =
        {g : formPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) |
          g.1.1.det = 1} := by
    ext g
    exact mem_specialFormPreservingMatrixSubgroup_iff
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) g
  rw [hset]
  exact isClosed_eq
    ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
    continuous_const

/-- The rationally presented p-adic form-preserving group is closed in the
ambient matrix units. -/
theorem isClosed_rationalFormMatrixPadicFormPreservingSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsClosed
      (formPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) :
        Set (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) := by
  change IsClosed
    {g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ |
      g.1ᵀ * L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) * g.1 =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])}
  have hcontinuous : Continuous
      (fun g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ ↦
        g.1ᵀ * L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) * g.1) := by
    fun_prop
  exact isClosed_eq hcontinuous continuous_const

/-- The corrected special-orthogonal integral stabilizer is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p :
        Set (specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])))) := by
  exact (isOpen_localPadicIntegralMatrixUnitsSubgroup p n).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

/-- The corrected special-orthogonal integral stabilizer is compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p :
        Set (specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])))) := by
  have hspecial :=
    (L.isClosed_localPadicSpecialOrthogonalMatrixSubgroup p)
      |>.isClosedEmbedding_subtypeVal
  have hform :=
    (L.isClosed_rationalFormMatrixPadicFormPreservingSubgroup p)
      |>.isClosedEmbedding_subtypeVal
  let hembedding := hform.comp hspecial
  exact hembedding.isCompact_preimage
    (isCompact_localPadicIntegralMatrixUnitsSubgroup p n)

local instance localPadicSpecialOrthogonalDifferentialStabilizerMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance localPadicSpecialOrthogonalDifferentialStabilizerBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The literal volume of the integral special-orthogonal stabilizer for the
corrected differential Haar measure. -/
def localPadicSpecialOrthogonalDifferentialStabilizerVolume
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0∞ :=
  padicCayleySpecialOrthogonalDifferentialMeasure
      p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p :
      Set (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))))

/-- The corrected differential volume of the integral special-orthogonal
stabilizer is finite. -/
theorem localPadicSpecialOrthogonalDifferentialStabilizerVolume_lt_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p < ⊤ := by
  let F := L.rationalFormMatrix
  have hFsymm : F.IsSymm := L.form_symm.map _
  have hF : F.det ≠ 0 := L.rationalFormMatrix_det_ne_zero
  let μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  letI : IsFiniteMeasureOnCompacts μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isFiniteOnCompacts
      p n F hFsymm hF
  exact
    (L.isCompact_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      |>.measure_lt_top

/-- The corrected differential volume of the integral special-orthogonal
stabilizer is strictly positive. -/
theorem localPadicSpecialOrthogonalDifferentialStabilizerVolume_pos
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 < L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p := by
  let F := L.rationalFormMatrix
  have hFsymm : F.IsSymm := L.form_symm.map _
  have hF : F.det ≠ 0 := L.rationalFormMatrix_det_ne_zero
  let μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  letI : Measure.IsOpenPosMeasure μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isOpenPosMeasure
      p n F hFsymm hF
  exact
    (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      |>.measure_pos μ
        ⟨1, Subgroup.one_mem _⟩

end PositiveDefiniteIntegralLattice
