import SMSFormula.SkewAdjointBaseChange
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# P-adic coordinate measure on the skew-adjoint model

This file uses the rationally transported skew-adjoint basis to define its
unit coordinate lattice over `ℚ_[p]`. The lattice is compact and open, so it
normalizes an additive Haar measure. Its volume is one.

This is only a coordinate-space measure. It does not move the measure to an
orthogonal group or identify a stabilizer volume.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
private def padicUnitCoordinateBall (p d : ℕ) [Fact (Nat.Prime p)] :
    TopologicalSpace.PositiveCompacts (Fin d → ℚ_[p]) where
  carrier := Set.range (fun z : Fin d → ℤ_[p] ↦ fun i ↦ (z i : ℚ_[p]))
  isCompact' := by
    exact isCompact_range <|
      (Topology.IsOpenEmbedding.piMap
        (fun _ : Fin d ↦ PadicInt.isOpenEmbedding_coe)).continuous
  interior_nonempty' := by
    have hopen :
        IsOpen (Set.range (fun z : Fin d → ℤ_[p] ↦ fun i ↦ (z i : ℚ_[p]))) := by
      exact (Topology.IsOpenEmbedding.piMap
        (fun _ : Fin d ↦ PadicInt.isOpenEmbedding_coe)).isOpen_range
    rw [hopen.interior_eq]
    exact Set.range_nonempty _

local instance skewAdjointPadicIsTopologicalAddGroup
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance skewAdjointPadicMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Coordinates in the rationally transported skew-adjoint basis over
`ℚ_[p]`, as a continuous linear equivalence. -/
def skewAdjointPadicCoordinateEquiv (F : Matrix ι ι ℚ)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℚ_[p]) := by
  letI := skewAdjointPadicIsTopologicalAddGroup F p
  exact
    (skewAdjointScalarExtensionFinBasis
      (K := ℚ_[p]) F).equivFun.toContinuousLinearEquiv

/-- The compact-open lattice whose coordinates in the rationally transported
skew-adjoint basis are p-adic integers. -/
def skewAdjointPadicCoordinateLattice (F : Matrix ι ι ℚ)
    (p : ℕ) [Fact (Nat.Prime p)] :
    TopologicalSpace.PositiveCompacts
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (padicUnitCoordinateBall p
      (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))).map
    (skewAdjointPadicCoordinateEquiv F p).symm
    (skewAdjointPadicCoordinateEquiv F p).symm.continuous
    (skewAdjointPadicCoordinateEquiv F p).symm.isOpenMap

theorem mem_skewAdjointPadicCoordinateLattice_iff
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    x ∈ skewAdjointPadicCoordinateLattice F p ↔
      ∀ i, ‖skewAdjointPadicCoordinateEquiv F p x i‖ ≤ 1 := by
  change x ∈
      (skewAdjointPadicCoordinateEquiv F p).symm ''
        Set.range (fun z :
          Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p] ↦
            fun i ↦ (z i : ℚ_[p])) ↔ _
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩ i
    simpa using (z i).property
  · intro hx
    refine ⟨skewAdjointPadicCoordinateEquiv F p x, ?_,
      (skewAdjointPadicCoordinateEquiv F p).symm_apply_apply x⟩
    refine ⟨fun i ↦ ⟨skewAdjointPadicCoordinateEquiv F p x i, hx i⟩, ?_⟩
    rfl

/-- The additive Haar measure for which the rationally transported
skew-adjoint p-adic coordinate lattice has volume one. -/
def skewAdjointPadicCoordinateMeasure (F : Matrix ι ι ℚ)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI := skewAdjointPadicIsTopologicalAddGroup F p
  letI := skewAdjointPadicMeasurableSpace F p
  letI := skewAdjointPadicBorelSpace F p
  exact Measure.addHaarMeasure (skewAdjointPadicCoordinateLattice F p)

theorem skewAdjointPadicCoordinateMeasure_lattice
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicCoordinateLattice F p) = 1 := by
  letI := skewAdjointPadicIsTopologicalAddGroup F p
  letI := skewAdjointPadicMeasurableSpace F p
  letI := skewAdjointPadicBorelSpace F p
  exact Measure.addHaarMeasure_self

/-- The p-adic coordinate measure is an additive Haar measure. This remains an
explicit theorem value because the model's Borel structure is kept local. -/
theorem skewAdjointPadicCoordinateMeasure_isAddHaarMeasure
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsAddHaarMeasure (skewAdjointPadicCoordinateMeasure F p) := by
  letI := skewAdjointPadicIsTopologicalAddGroup F p
  letI := skewAdjointPadicMeasurableSpace F p
  letI := skewAdjointPadicBorelSpace F p
  unfold skewAdjointPadicCoordinateMeasure
  infer_instance

end Matrix
