import SMSFormula.SkewAdjointPadicCoordinateBallTopology
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The uniform p-adic coordinate-ball neighborhood basis

The transported coordinate lattice is compact, hence bounded. The generic
small-scalar lemma sends a bounded set into any prescribed zero-neighborhood
for all sufficiently small scalars. Since `p ^ k` tends to zero in `ℚ_[p]`,
the uniform coordinate balls from
`SkewAdjointPadicCoordinateBallTopology.lean` are cofinal among
zero-neighborhoods.

Translation gives the same cofinality at every point, and the resulting
`Nat`-indexed family is packaged as an explicit countable neighborhood basis.
This module is purely topological: it contains no Haar scaling, cover
selection, or nonlinear transition control.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology Pointwise

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointPadicCoordinateBallBasisMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicCoordinateBallBasisBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Every zero-neighborhood contains a uniform `p ^ k` coordinate ball. -/
theorem
    exists_skewAdjointPadicUniformCoordinateBall_subset_of_mem_nhds_zero
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {s : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hs : s ∈ 𝓝 0) :
    ∃ k, skewAdjointPadicUniformCoordinateBall F p k ⊆ s := by
  have hsmall :
      ∀ᶠ r in 𝓝 (0 : ℚ_[p]),
        ({0} : Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) +
            r • (skewAdjointPadicCoordinateLattice F p : Set _) ⊆ s :=
    eventually_singleton_add_smul_subset
      (skewAdjointPadicCoordinateLattice F p).isCompact.isBounded hs
  have hp :
      Filter.Tendsto (fun k : ℕ => (p : ℚ_[p]) ^ k)
        Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := (hp.eventually hsmall).exists
  refine ⟨k, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  apply hk
  simp only [Set.mem_add, Set.mem_singleton_iff, Set.mem_smul_set]
  exact ⟨0, rfl, (p : ℚ_[p]) ^ k • z, ⟨z, hz, rfl⟩, by simp⟩

/-- The uniform zero-centered coordinate balls form a `Nat`-indexed
neighborhood basis at zero. -/
theorem nhds_zero_hasBasis_skewAdjointPadicUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (𝓝 (0 : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)).HasBasis
      (fun _ : ℕ => True)
      (fun k => skewAdjointPadicUniformCoordinateBall F p k) := by
  refine ⟨fun s => ?_⟩
  constructor
  · intro hs
    obtain ⟨k, hk⟩ :=
      exists_skewAdjointPadicUniformCoordinateBall_subset_of_mem_nhds_zero
        F p hs
    exact ⟨k, trivial, hk⟩
  · rintro ⟨k, -, hk⟩
    exact Filter.mem_of_superset
      ((isClopen_skewAdjointPadicUniformCoordinateBall F p k).2.mem_nhds
        (zero_mem_skewAdjointPadicUniformCoordinateBall F p k)) hk

/-- Every neighborhood of `x` contains a translated uniform coordinate ball
centered at `x`. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    {s : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hs : s ∈ 𝓝 x) :
    ∃ k, skewAdjointPadicTranslatedUniformCoordinateBall F p k x ⊆ s := by
  have hs0 : (Homeomorph.addLeft x) ⁻¹' s ∈ 𝓝 0 := by
    apply (Homeomorph.addLeft x).continuous.tendsto 0
    change s ∈ 𝓝 (x + 0)
    simpa using hs
  obtain ⟨k, hk⟩ :=
    exists_skewAdjointPadicUniformCoordinateBall_subset_of_mem_nhds_zero
      F p hs0
  refine ⟨k, ?_⟩
  intro y hy
  have hy0 := hk
    ((mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff F p k x y).1 hy)
  change x + (y - x) ∈ s at hy0
  simpa using hy0

/-- The translated uniform coordinate balls are an explicit countable
neighborhood basis at every point. -/
theorem nhds_hasBasis_skewAdjointPadicTranslatedUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (𝓝 x).HasBasis (fun _ : ℕ => True)
      (fun k => skewAdjointPadicTranslatedUniformCoordinateBall F p k x) := by
  refine ⟨fun s => ?_⟩
  constructor
  · intro hs
    obtain ⟨k, hk⟩ :=
      exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
        F p x hs
    exact ⟨k, trivial, hk⟩
  · rintro ⟨k, -, hk⟩
    exact Filter.mem_of_superset
      (skewAdjointPadicTranslatedUniformCoordinateBall_mem_nhds F p k x) hk

end Matrix
