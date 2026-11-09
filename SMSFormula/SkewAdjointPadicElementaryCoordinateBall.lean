import SMSFormula.SkewAdjointPadicElementaryCoordinateFormula
import SMSFormula.SkewAdjointPadicCoordinateBallTopology

/-!
# Form-adapted p-adic uniform coordinate balls

The form-adapted integral coordinate lattice is described intrinsically by
the strict-upper entries of `F_p X`.  Its level-`k` uniform ball is the
image under scalar multiplication by `p ^ k`; membership is therefore the
corresponding strict-upper norm bound.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {n : ℕ}

local instance skewAdjointFormElementaryPadicCoordinateBallMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointFormElementaryPadicCoordinateBallBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The form-adapted integral lattice consists exactly of the skew-adjoint
matrices whose strict-upper entries after left multiplication by `F_p` are
integral. -/
theorem mem_skewAdjointFormElementaryPadicCoordinateLattice_iff_upper
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    X ∈ skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet ↔
      ∀ q : StrictUpperPair n,
        ‖(F.map (algebraMap ℚ ℚ_[p]) *
          (X : Matrix (Fin n) (Fin n) ℚ_[p])) q.1.1 q.1.2‖ ≤ 1 := by
  rw [mem_skewAdjointFormElementaryPadicCoordinateLattice_iff]
  constructor
  · intro h q
    have hq :=
      h (skewAdjointFormElementaryIndexEquiv F hF hdet q)
    rw [skewAdjointFormElementaryPadicCoordinateEquiv_apply] at hq
    simpa using hq
  · intro h j
    rw [skewAdjointFormElementaryPadicCoordinateEquiv_apply]
    exact h ((skewAdjointFormElementaryIndexEquiv F hF hdet).symm j)

/-- The form-adapted coordinate lattice is the finite intersection of its
coordinate closed unit balls. -/
theorem skewAdjointFormElementaryPadicCoordinateLattice_eq_iInter_closedBall
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
      Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) =
      ⋂ j,
        (fun X =>
          skewAdjointFormElementaryPadicCoordinateEquiv
            p F hF hdet X j) ⁻¹' Metric.closedBall 0 1 := by
  ext X
  change
    (X ∈ skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet) ↔
      X ∈ ⋂ j,
        (fun X =>
          skewAdjointFormElementaryPadicCoordinateEquiv
            p F hF hdet X j) ⁻¹' Metric.closedBall 0 1
  rw [mem_skewAdjointFormElementaryPadicCoordinateLattice_iff]
  simp only [Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right]

/-- The form-adapted integral coordinate lattice is clopen. -/
theorem isClopen_skewAdjointFormElementaryPadicCoordinateLattice
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    IsClopen
      (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  rw [skewAdjointFormElementaryPadicCoordinateLattice_eq_iInter_closedBall]
  apply isClopen_iInter_of_finite
  intro j
  apply IsClopen.preimage
  · exact
      ⟨Metric.isClosed_closedBall,
        IsUltrametricDist.isOpen_closedBall
          (x := (0 : ℚ_[p])) (r := 1) one_ne_zero⟩
  · exact continuous_apply j |>.comp
      (skewAdjointFormElementaryPadicCoordinateEquiv
        p F hF hdet).continuous

/-- The level-`k` form-adapted uniform coordinate ball is the scalar
`p ^ k` image of the form-adapted integral coordinate lattice. -/
def skewAdjointFormElementaryPadicUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicUniformCoordinateDilation F p k ''
    (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
      Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)

/-- The defining dilation maps the level-zero form-adapted lattice exactly
onto the level-`k` form-adapted ball. -/
theorem image_skewAdjointFormElementaryPadicCoordinateLattice_dilation
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointPadicUniformCoordinateDilation F p k ''
        (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
          Set (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) =
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet :=
  rfl

/-- Every form-adapted uniform coordinate ball is clopen. -/
theorem isClopen_skewAdjointFormElementaryPadicUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    IsClopen
      (skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet) := by
  rw [skewAdjointFormElementaryPadicUniformCoordinateBall]
  have himage :
      (skewAdjointPadicUniformCoordinateDilation F p k) ''
          (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
            Set _) =
        (skewAdjointPadicUniformCoordinateDilation F p k).symm ⁻¹'
          (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
            Set _) := by
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      change
        (skewAdjointPadicUniformCoordinateDilation F p k).symm
            (skewAdjointPadicUniformCoordinateDilation F p k X) ∈
          (skewAdjointFormElementaryPadicCoordinateLattice
            p F hF hdet : Set _)
      rw [(skewAdjointPadicUniformCoordinateDilation
        F p k).symm_apply_apply]
      exact hX
    · intro hY
      exact
        ⟨(skewAdjointPadicUniformCoordinateDilation F p k).symm Y,
          hY,
          (skewAdjointPadicUniformCoordinateDilation F p k).apply_symm_apply Y⟩
  rw [himage]
  exact IsClopen.preimage
    (isClopen_skewAdjointFormElementaryPadicCoordinateLattice
      p F hF hdet)
    (skewAdjointPadicUniformCoordinateDilation
      F p k).toHomeomorph.symm.continuous

/-- Every form-adapted uniform coordinate ball is compact. -/
theorem isCompact_skewAdjointFormElementaryPadicUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    IsCompact
      (skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet) := by
  rw [skewAdjointFormElementaryPadicUniformCoordinateBall]
  exact
    (skewAdjointFormElementaryPadicCoordinateLattice
      p F hF hdet).isCompact.image
        (skewAdjointPadicUniformCoordinateDilation F p k).continuous

/-- Every form-adapted uniform coordinate ball is open. -/
theorem isOpen_skewAdjointFormElementaryPadicUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    IsOpen
      (skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet) :=
  (isClopen_skewAdjointFormElementaryPadicUniformCoordinateBall
    p k F hF hdet).2

/-- Every form-adapted uniform coordinate ball is measurable. -/
theorem measurableSet_skewAdjointFormElementaryPadicUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    MeasurableSet
      (skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet) :=
  (isOpen_skewAdjointFormElementaryPadicUniformCoordinateBall
    p k F hF hdet).measurableSet

/-- Membership in the level-`k` form-adapted ball is exactly the uniform
strict-upper norm bound `‖p ^ k‖`. -/
theorem mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    X ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet ↔
      ∀ q : StrictUpperPair n,
        ‖(F.map (algebraMap ℚ ℚ_[p]) *
          (X : Matrix (Fin n) (Fin n) ℚ_[p])) q.1.1 q.1.2‖ ≤
            ‖(p : ℚ_[p]) ^ k‖ := by
  constructor
  · rintro ⟨Y, hY, rfl⟩ q
    rw [skewAdjointPadicUniformCoordinateDilation_apply]
    have hYq :=
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff_upper
        p F hF hdet Y).1 hY q
    change
      ‖(F.map (algebraMap ℚ ℚ_[p]) *
        (((p : ℚ_[p]) ^ k • Y :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[p])) q.1.1 q.1.2‖ ≤ _
    simp only [Submodule.coe_smul,
      Matrix.mul_smul, smul_eq_mul, Matrix.smul_apply, norm_mul]
    simpa using
      mul_le_mul_of_nonneg_left hYq (norm_nonneg ((p : ℚ_[p]) ^ k))
  · intro hX
    let A := skewAdjointPadicUniformCoordinateDilation F p k
    let Y := A.symm X
    refine ⟨Y, ?_, A.apply_symm_apply X⟩
    apply
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff_upper
        p F hF hdet Y).2
    intro q
    have hXq := hX q
    have hXY : X = A Y := (A.apply_symm_apply X).symm
    rw [hXY, skewAdjointPadicUniformCoordinateDilation_apply] at hXq
    change
      ‖(F.map (algebraMap ℚ ℚ_[p]) *
        ((((p : ℚ_[p]) ^ k) • Y :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[p])) q.1.1 q.1.2‖ ≤
        ‖(p : ℚ_[p]) ^ k‖ at hXq
    simp only [Submodule.coe_smul, Matrix.mul_smul, smul_eq_mul,
      Matrix.smul_apply, norm_mul] at hXq
    have hpne : ((p : ℚ_[p]) ^ k) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    have hp : 0 < ‖(p : ℚ_[p]) ^ k‖ := norm_pos_iff.mpr hpne
    nlinarith [hXq]

end Matrix
