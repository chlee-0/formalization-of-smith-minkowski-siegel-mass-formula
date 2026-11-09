import SMSFormula.SkewAdjointPadicCoordinateBallCompactness
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite common-level decompositions by p-adic coordinate balls

Every compact open subset of the transported skew-adjoint `ℚ_[p]` carrier is
a finite pairwise-disjoint union of translated uniform coordinate balls at
one common level.

The proof uses compactness twice.  First, finitely many locally contained
coordinate balls cover the compact set, so the maximum of their levels gives
one level whose ball at every point is still contained in the set.  A second
finite subcover at that common level is then made duplicate-free by passing
to its set-valued image.  Same-level coset geometry makes the remaining
distinct balls pairwise disjoint.

No measure, determinant, or nonlinear transition statement is used.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology Pointwise

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A compact open subset of the transported skew-adjoint carrier is a finite
pairwise-disjoint union of translated uniform coordinate balls at one common
level. -/
theorem
    exists_finite_pairwiseDisjoint_commonLevel_skewAdjointPadicTranslatedUniformCoordinateBall_cover
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {C : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hCcompact : IsCompact C) (hCopen : IsOpen C) :
    ∃ level : ℕ,
      ∃ balls : Set (Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        balls.Finite ∧
        balls.PairwiseDisjoint id ∧
        (∀ B ∈ balls, ∃ x : C,
          B = skewAdjointPadicTranslatedUniformCoordinateBall
            F p level x) ∧
        (∀ B ∈ balls, B ⊆ C) ∧
        ⋃₀ balls = C := by
  classical
  let localLevel : C → ℕ := fun x =>
    Classical.choose
      (exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
        F p x (hCopen.mem_nhds x.property))
  let localBall : C → Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := fun x =>
    skewAdjointPadicTranslatedUniformCoordinateBall F p (localLevel x) x
  have hlocal_subset : ∀ x : C, localBall x ⊆ C := by
    intro x
    exact Classical.choose_spec
      (exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
        F p x (hCopen.mem_nhds x.property))
  have hlocal_open : ∀ x : C, IsOpen (localBall x) := by
    intro x
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        F p (localLevel x) x).2
  have hlocal_cover : C ⊆ ⋃ x : C, localBall x := by
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩,
        mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
          F p (localLevel ⟨x, hx⟩) x⟩
  obtain ⟨localCenters, hlocalCenters_cover⟩ :=
    hCcompact.elim_finite_subcover localBall hlocal_open hlocal_cover
  let level : ℕ := localCenters.sup localLevel
  let commonBall : C → Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := fun x =>
    skewAdjointPadicTranslatedUniformCoordinateBall F p level x
  have hcommon_subset : ∀ x : C, commonBall x ⊆ C := by
    intro x
    have hxcover := hlocalCenters_cover x.property
    rcases Set.mem_iUnion.mp hxcover with ⟨y, hxcover⟩
    rcases Set.mem_iUnion.mp hxcover with ⟨hy, hxy⟩
    have hylevel : localLevel y ≤ level :=
      Finset.le_sup hy
    exact (skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
      F p hylevel hxy).trans (hlocal_subset y)
  have hcommon_open : ∀ x : C, IsOpen (commonBall x) := by
    intro x
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        F p level x).2
  have hcommon_cover : C ⊆ ⋃ x : C, commonBall x := by
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩,
        mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
          F p level x⟩
  obtain ⟨centers, hcenters_cover⟩ :=
    hCcompact.elim_finite_subcover commonBall hcommon_open hcommon_cover
  let balls : Set (Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
    commonBall '' (centers : Set C)
  have hballs_finite : balls.Finite :=
    centers.finite_toSet.image commonBall
  have hballs_pairwise : balls.PairwiseDisjoint id := by
    intro B hB D hD hBD
    obtain ⟨x, hx, rfl⟩ := hB
    obtain ⟨y, hy, rfl⟩ := hD
    rcases
        skewAdjointPadicTranslatedUniformCoordinateBall_disjoint_or_eq
          F p level x y with hdisjoint | heq
    · exact hdisjoint
    · exact (hBD heq).elim
  refine ⟨level, balls, hballs_finite, hballs_pairwise, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact ⟨x, rfl⟩
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact hcommon_subset x
  · apply Set.Subset.antisymm
    · exact Set.sUnion_subset fun B hB => by
        obtain ⟨x, hx, rfl⟩ := hB
        exact hcommon_subset x
    · intro x hx
      have hxcover := hcenters_cover hx
      rcases Set.mem_iUnion.mp hxcover with ⟨y, hxcover⟩
      rcases Set.mem_iUnion.mp hxcover with ⟨hy, hxy⟩
      exact Set.mem_sUnion.mpr
        ⟨commonBall y, ⟨y, hy, rfl⟩, hxy⟩

/-- A locally constant function on an open ambient subtype is constant on
every member of a finite pairwise-disjoint common-level coordinate-ball
decomposition of a compact open subset. -/
theorem
    exists_finite_pairwiseDisjoint_commonLevel_skewAdjointPadicTranslatedUniformCoordinateBall_cover_const
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {β : Type*}
    {S C : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hSopen : IsOpen S)
    (hCcompact : IsCompact C) (hCopen : IsOpen C)
    (hCS : C ⊆ S)
    (f : S → β) (hf : IsLocallyConstant f) :
    ∃ level : ℕ,
      ∃ balls : Set (Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        balls.Finite ∧
        balls.PairwiseDisjoint id ∧
        (∀ B ∈ balls, ∃ x : C,
          B = skewAdjointPadicTranslatedUniformCoordinateBall
              F p level x ∧
            ∀ y : C, y.1 ∈ B →
              f ⟨y.1, hCS y.2⟩ = f ⟨x.1, hCS x.2⟩) ∧
        (∀ B ∈ balls, B ⊆ C) ∧
        ⋃₀ balls = C := by
  classical
  let sourcePoint : C → S := fun x => ⟨x.1, hCS x.2⟩
  have hexists_local : ∀ x : C, ∃ k,
      skewAdjointPadicTranslatedUniformCoordinateBall F p k x ⊆ C ∧
      ∀ y : C,
        y.1 ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x →
          f (sourcePoint y) = f (sourcePoint x) := by
    intro x
    obtain ⟨V, hVopen, hxV, hconst⟩ :=
      hf.exists_open (sourcePoint x)
    have himageOpen : IsOpen (Subtype.val '' V) :=
      hSopen.isOpenEmbedding_subtypeVal.isOpenMap V hVopen
    have hximage : x.1 ∈ Subtype.val '' V :=
      ⟨sourcePoint x, hxV, rfl⟩
    have hxneighborhood :
        C ∩ Subtype.val '' V ∈ 𝓝 x.1 :=
      (hCopen.inter himageOpen).mem_nhds ⟨x.2, hximage⟩
    obtain ⟨k, hk⟩ :=
      exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
        F p x.1 hxneighborhood
    refine ⟨k, fun y hy => (hk hy).1, ?_⟩
    intro y hy
    rcases (hk hy).2 with ⟨Y, hYV, hYeq⟩
    have hY : Y = sourcePoint y := by
      apply Subtype.ext
      exact hYeq
    simpa only [hY] using hconst Y hYV
  let localLevel : C → ℕ := fun x =>
    Classical.choose (hexists_local x)
  let localBall : C → Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := fun x =>
    skewAdjointPadicTranslatedUniformCoordinateBall F p (localLevel x) x
  have hlocal_subset : ∀ x : C, localBall x ⊆ C := by
    intro x
    exact (Classical.choose_spec (hexists_local x)).1
  have hlocal_const : ∀ x y : C, y.1 ∈ localBall x →
      f (sourcePoint y) = f (sourcePoint x) := by
    intro x
    exact (Classical.choose_spec (hexists_local x)).2
  have hlocal_open : ∀ x : C, IsOpen (localBall x) := by
    intro x
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        F p (localLevel x) x).2
  have hlocal_cover : C ⊆ ⋃ x : C, localBall x := by
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩,
        mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
          F p (localLevel ⟨x, hx⟩) x⟩
  obtain ⟨localCenters, hlocalCenters_cover⟩ :=
    hCcompact.elim_finite_subcover localBall hlocal_open hlocal_cover
  let level : ℕ := localCenters.sup localLevel
  let commonBall : C → Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := fun x =>
    skewAdjointPadicTranslatedUniformCoordinateBall F p level x
  have hcommon_subset : ∀ x : C, commonBall x ⊆ C := by
    intro x
    have hxcover := hlocalCenters_cover x.property
    rcases Set.mem_iUnion.mp hxcover with ⟨y, hxcover⟩
    rcases Set.mem_iUnion.mp hxcover with ⟨hy, hxy⟩
    have hylevel : localLevel y ≤ level :=
      Finset.le_sup hy
    exact (skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
      F p hylevel hxy).trans (hlocal_subset y)
  have hcommon_const : ∀ x y : C, y.1 ∈ commonBall x →
      f (sourcePoint y) = f (sourcePoint x) := by
    intro x y hyx
    have hxcover := hlocalCenters_cover x.property
    rcases Set.mem_iUnion.mp hxcover with ⟨z, hxcover⟩
    rcases Set.mem_iUnion.mp hxcover with ⟨hz, hxz⟩
    have hzlevel : localLevel z ≤ level :=
      Finset.le_sup hz
    have hsub :
        commonBall x ⊆ localBall z :=
      skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
        F p hzlevel hxz
    exact (hlocal_const z y (hsub hyx)).trans
      (hlocal_const z x hxz).symm
  have hcommon_open : ∀ x : C, IsOpen (commonBall x) := by
    intro x
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        F p level x).2
  have hcommon_cover : C ⊆ ⋃ x : C, commonBall x := by
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩,
        mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
          F p level x⟩
  obtain ⟨centers, hcenters_cover⟩ :=
    hCcompact.elim_finite_subcover commonBall hcommon_open hcommon_cover
  let balls : Set (Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
    commonBall '' (centers : Set C)
  have hballs_finite : balls.Finite :=
    centers.finite_toSet.image commonBall
  have hballs_pairwise : balls.PairwiseDisjoint id := by
    intro B hB D hD hBD
    obtain ⟨x, hx, rfl⟩ := hB
    obtain ⟨y, hy, rfl⟩ := hD
    rcases
        skewAdjointPadicTranslatedUniformCoordinateBall_disjoint_or_eq
          F p level x y with hdisjoint | heq
    · exact hdisjoint
    · exact (hBD heq).elim
  refine ⟨level, balls, hballs_finite, hballs_pairwise, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact ⟨x, rfl, hcommon_const x⟩
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact hcommon_subset x
  · apply Set.Subset.antisymm
    · exact Set.sUnion_subset fun B hB => by
        obtain ⟨x, hx, rfl⟩ := hB
        exact hcommon_subset x
    · intro x hx
      have hxcover := hcenters_cover hx
      rcases Set.mem_iUnion.mp hxcover with ⟨y, hxcover⟩
      rcases Set.mem_iUnion.mp hxcover with ⟨hy, hxy⟩
      exact Set.mem_sUnion.mpr
        ⟨commonBall y, ⟨y, hy, rfl⟩, hxy⟩

end Matrix
