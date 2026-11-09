import SMSFormula.SkewAdjointComparisonPrimeSupport
import SMSFormula.SkewAdjointPadicMeasure

/-!
# Form-adapted p-adic skew-adjoint coordinate measure

The form-adapted elementary p-adic basis supplies a continuous coordinate
equivalence.  Pulling back the integral unit coordinate ball gives a
compact-open lattice, and that lattice is used to normalize an additive Haar
measure.

This is a comparison measure.  It is distinct from the fixed-basis
coordinate measure attached to an arbitrary rational differential, and this
file does not compare the two measures.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
private def formElementaryPadicUnitCoordinateBall
    (p d : ℕ) [Fact (Nat.Prime p)] :
    TopologicalSpace.PositiveCompacts (Fin d → ℚ_[p]) where
  carrier := Set.range (fun z : Fin d → ℤ_[p] ↦ fun i ↦ (z i : ℚ_[p]))
  isCompact' := by
    exact isCompact_range <|
      (Topology.IsOpenEmbedding.piMap
        (fun _ : Fin d ↦ PadicInt.isOpenEmbedding_coe)).continuous
  interior_nonempty' := by
    have hopen :
        IsOpen (Set.range
          (fun z : Fin d → ℤ_[p] ↦ fun i ↦ (z i : ℚ_[p]))) := by
      exact (Topology.IsOpenEmbedding.piMap
        (fun _ : Fin d ↦ PadicInt.isOpenEmbedding_coe)).isOpen_range
    rw [hopen.interior_eq]
    exact Set.range_nonempty _

local instance skewAdjointFormElementaryPadicIsTopologicalAddGroup
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance skewAdjointFormElementaryPadicMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointFormElementaryPadicBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Continuous coordinates in the form-adapted elementary p-adic basis. -/
def skewAdjointFormElementaryPadicCoordinateEquiv
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra F)) → ℚ_[p]) := by
  letI := skewAdjointFormElementaryPadicIsTopologicalAddGroup p F
  exact
    (skewAdjointFormElementaryPadicFinBasis
      p F hF hdet).equivFun.toContinuousLinearEquiv

/-- The compact-open lattice whose form-adapted elementary coordinates are
p-adic integers. -/
def skewAdjointFormElementaryPadicCoordinateLattice
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    TopologicalSpace.PositiveCompacts
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (formElementaryPadicUnitCoordinateBall p
      (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))).map
    (skewAdjointFormElementaryPadicCoordinateEquiv
      p F hF hdet).symm
    (skewAdjointFormElementaryPadicCoordinateEquiv
      p F hF hdet).symm.continuous
    (skewAdjointFormElementaryPadicCoordinateEquiv
      p F hF hdet).symm.isOpenMap

/-- Membership in the form-adapted coordinate lattice is coordinatewise
integrality. -/
theorem mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    x ∈ skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet ↔
      ∀ i,
        ‖skewAdjointFormElementaryPadicCoordinateEquiv
          p F hF hdet x i‖ ≤ 1 := by
  change x ∈
      (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).symm ''
        Set.range (fun z :
          Fin (Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p] ↦
              fun i ↦ (z i : ℚ_[p])) ↔ _
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩ i
    simpa using (z i).property
  · intro hx
    refine
      ⟨skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet x,
        ?_, (skewAdjointFormElementaryPadicCoordinateEquiv
          p F hF hdet).symm_apply_apply x⟩
    refine
      ⟨fun i => ⟨skewAdjointFormElementaryPadicCoordinateEquiv
        p F hF hdet x i, hx i⟩, ?_⟩
    rfl

/-- Additive Haar measure normalized by the form-adapted elementary
coordinate lattice.  This is a comparison measure, not a replacement for
`skewAdjointPadicCoordinateMeasure`. -/
def skewAdjointFormElementaryPadicCoordinateMeasure
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Measure
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI := skewAdjointFormElementaryPadicIsTopologicalAddGroup p F
  letI := skewAdjointFormElementaryPadicMeasurableSpace p F
  letI := skewAdjointFormElementaryPadicBorelSpace p F
  exact Measure.addHaarMeasure
    (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet)

/-- The form-adapted elementary coordinate lattice has mass one in its
literal comparison measure. -/
theorem skewAdjointFormElementaryPadicCoordinateMeasure_lattice
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet
        (skewAdjointFormElementaryPadicCoordinateLattice
          p F hF hdet) = 1 := by
  letI := skewAdjointFormElementaryPadicIsTopologicalAddGroup p F
  letI := skewAdjointFormElementaryPadicMeasurableSpace p F
  letI := skewAdjointFormElementaryPadicBorelSpace p F
  exact Measure.addHaarMeasure_self

/-- The form-adapted elementary coordinate comparison measure is additive
Haar. -/
theorem skewAdjointFormElementaryPadicCoordinateMeasure_isAddHaarMeasure
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Measure.IsAddHaarMeasure
      (skewAdjointFormElementaryPadicCoordinateMeasure
        p F hF hdet) := by
  letI := skewAdjointFormElementaryPadicIsTopologicalAddGroup p F
  letI := skewAdjointFormElementaryPadicMeasurableSpace p F
  letI := skewAdjointFormElementaryPadicBorelSpace p F
  unfold skewAdjointFormElementaryPadicCoordinateMeasure
  infer_instance

end Matrix
