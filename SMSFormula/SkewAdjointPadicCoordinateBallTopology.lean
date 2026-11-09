import SMSFormula.SkewAdjointPadicMeasureDilation
import Mathlib.Topology.Clopen

/-!
# Coordinate-lattice balls in the p-adic skew-adjoint carrier

This module gives the transported coordinate lattice its genuine
nonarchimedean topology. The selected ambient matrix/operator norm need not
carry an `IsUltrametricDist` instance: clopenness is proved coordinatewise
from the p-adic closed unit ball.

Uniform multiplication by `p ^ k` is packaged as a continuous linear
equivalence, so its image of the coordinate lattice is clopen. Translates of
these uniform coordinate balls are consequently clopen neighborhoods of
their centers. No Haar scaling, disjoint cover, or nonlinear transition
control is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointPadicCoordinateBallMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicCoordinateBallBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The transported coordinate lattice is the finite intersection of the
inverse images of the p-adic closed unit ball under its coordinate maps. -/
theorem skewAdjointPadicCoordinateLattice_eq_iInter_closedBall
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointPadicCoordinateLattice F p :
      Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) =
      ⋂ i, (fun x => skewAdjointPadicCoordinateEquiv F p x i) ⁻¹'
        Metric.closedBall 0 1 := by
  ext x
  change
    (x ∈ skewAdjointPadicCoordinateLattice F p) ↔
      x ∈ ⋂ i, (fun x => skewAdjointPadicCoordinateEquiv F p x i) ⁻¹'
        Metric.closedBall 0 1
  rw [mem_skewAdjointPadicCoordinateLattice_iff]
  simp only [Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right]

/-- The transported coordinate lattice is clopen. This uses only the p-adic
coordinate topology, not an ultrametric instance for the ambient operator
norm. -/
theorem isClopen_skewAdjointPadicCoordinateLattice
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsClopen
      (skewAdjointPadicCoordinateLattice F p :
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  rw [skewAdjointPadicCoordinateLattice_eq_iInter_closedBall F p]
  apply isClopen_iInter_of_finite
  intro i
  apply IsClopen.preimage
  · exact
      ⟨Metric.isClosed_closedBall,
        IsUltrametricDist.isOpen_closedBall
          (x := (0 : ℚ_[p])) (r := 1) one_ne_zero⟩
  · exact continuous_apply i |>.comp
      (skewAdjointPadicCoordinateEquiv F p).continuous

theorem zero_mem_skewAdjointPadicCoordinateLattice
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    0 ∈ (skewAdjointPadicCoordinateLattice F p :
      Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  change 0 ∈ skewAdjointPadicCoordinateLattice F p
  rw [mem_skewAdjointPadicCoordinateLattice_iff]
  intro i
  simp

/-- The transported coordinate lattice is an open-and-closed additive
neighborhood of zero. -/
theorem skewAdjointPadicCoordinateLattice_mem_nhds_zero
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointPadicCoordinateLattice F p :
      Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈ 𝓝 0 :=
  (isClopen_skewAdjointPadicCoordinateLattice F p).2.mem_nhds
    (zero_mem_skewAdjointPadicCoordinateLattice F p)

private def skewAdjointPadicUniformPowerUnit
    (p k : ℕ) [Fact (Nat.Prime p)] : ℚ_[p]ˣ :=
  Units.mk0 ((p : ℚ_[p]) ^ k)
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))

/-- Uniform scalar multiplication by `p ^ k` on the transported
skew-adjoint carrier. -/
def skewAdjointPadicUniformCoordinateDilation
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ContinuousLinearEquiv.smulLeft
    (R₁ := ℚ_[p])
    (M₁ := (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (skewAdjointPadicUniformPowerUnit p k)

@[simp]
theorem skewAdjointPadicUniformCoordinateDilation_apply
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicUniformCoordinateDilation F p k x =
      (p : ℚ_[p]) ^ k • x := rfl

/-- The zero-centered uniform coordinate ball of level `k`: the `p ^ k`
scalar image of the coordinate lattice. -/
def skewAdjointPadicUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicUniformCoordinateDilation F p k ''
    (skewAdjointPadicCoordinateLattice F p :
      Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)

/-- Every zero-centered uniform coordinate ball is clopen. -/
theorem isClopen_skewAdjointPadicUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsClopen (skewAdjointPadicUniformCoordinateBall F p k) := by
  rw [skewAdjointPadicUniformCoordinateBall]
  constructor
  · have himage :
        (skewAdjointPadicUniformCoordinateDilation F p k) ''
            (skewAdjointPadicCoordinateLattice F p : Set _) =
          (skewAdjointPadicUniformCoordinateDilation F p k).symm ⁻¹'
            (skewAdjointPadicCoordinateLattice F p : Set _) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          change
            (skewAdjointPadicUniformCoordinateDilation F p k).symm
                (skewAdjointPadicUniformCoordinateDilation F p k x) ∈
              (skewAdjointPadicCoordinateLattice F p : Set _)
          rw [(skewAdjointPadicUniformCoordinateDilation F p k).symm_apply_apply]
          exact hx
        · intro hy
          exact
            ⟨(skewAdjointPadicUniformCoordinateDilation F p k).symm y,
              hy,
              (skewAdjointPadicUniformCoordinateDilation F p k).apply_symm_apply y⟩
    rw [himage]
    exact
      (IsClopen.preimage
        (isClopen_skewAdjointPadicCoordinateLattice F p)
        (skewAdjointPadicUniformCoordinateDilation F p k).toHomeomorph.symm.continuous).1
  · exact
      (skewAdjointPadicUniformCoordinateDilation F p k).toHomeomorph.isOpenMap _
        (isClopen_skewAdjointPadicCoordinateLattice F p).2

/-- Zero belongs to every zero-centered uniform coordinate ball. -/
theorem zero_mem_skewAdjointPadicUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    0 ∈ skewAdjointPadicUniformCoordinateBall F p k := by
  refine ⟨0, ?_, by simp⟩
  exact zero_mem_skewAdjointPadicCoordinateLattice F p

/-- The translated uniform coordinate ball centered at `x`. -/
def skewAdjointPadicTranslatedUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (Homeomorph.addLeft (-x)) ⁻¹'
    skewAdjointPadicUniformCoordinateBall F p k

theorem mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    y ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x ↔
      y - x ∈ skewAdjointPadicUniformCoordinateBall F p k := by
  change -x + y ∈ skewAdjointPadicUniformCoordinateBall F p k ↔ _
  rw [sub_eq_add_neg, add_comm]

/-- Every translated uniform coordinate ball is clopen. -/
theorem isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    IsClopen (skewAdjointPadicTranslatedUniformCoordinateBall F p k x) := by
  exact IsClopen.preimage
    (isClopen_skewAdjointPadicUniformCoordinateBall F p k)
    (Homeomorph.addLeft (-x)).continuous

theorem mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    x ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x := by
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff]
  simpa using zero_mem_skewAdjointPadicUniformCoordinateBall F p k

/-- Translated uniform coordinate balls are neighborhoods of their centers. -/
theorem skewAdjointPadicTranslatedUniformCoordinateBall_mem_nhds
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicTranslatedUniformCoordinateBall F p k x ∈ 𝓝 x :=
  (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall F p k x).2.mem_nhds
    (mem_skewAdjointPadicTranslatedUniformCoordinateBall_self F p k x)

end Matrix
