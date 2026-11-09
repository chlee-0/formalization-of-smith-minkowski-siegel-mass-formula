import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicRestrictedFamilyGroup

/-!
# Principal blocks of finite-adelic Clifford--Spin restricted families

For a finite set `S` of height-one rational places, the `S`-principal block
consists of restricted local candidate families integral outside `S` in every
Clifford and matrix coordinate of the point and its inverse.

The blocks are monotone and cover the restricted-family group.  Inversion
preserves a block.  Multiplication requires one fixed additional finite set:
the places where a rational Clifford multiplication structure constant is
nonintegral.  Thus the product of the `S`- and `T`-blocks lies in the
`(S ∪ T) ∪ bad`-block.  This records the denominator issue literally instead
of silently treating Clifford multiplication as integral at every prime.

The final section compares local block membership with the exact
finite-adelic coordinate condition.  No restricted-product topology, reverse
continuity, local compactness, or measure is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicSpinPrincipalBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinPrincipalBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## Restricted-family principal blocks -/

/-- The restricted-family block integral outside the finite set `S`. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup :=
  {g | ∀ v, v ∉ S →
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v (g.1 v)}

@[simp]
theorem mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup) :
    g ∈ V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S ↔
      ∀ v, v ∉ S →
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v (g.1 v) :=
  Iff.rfl

/-- Every restricted family lies in a finite-exceptional principal block. -/
theorem exists_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      g ∈ V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S := by
  have hfinite :
      {v : IsDedekindDomain.HeightOneSpectrum ℤ |
        ¬V.HeightOnePadicCliffordSpinCandidateIsIntegral v (g.1 v)}.Finite :=
    Filter.eventually_cofinite.mp
      (show V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily g.1 from g.2)
  refine ⟨hfinite.toFinset, ?_⟩
  intro v hv
  by_contra hnot
  exact hv (by simpa using hnot)

/-- Principal blocks are monotone in their exceptional set. -/
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock_mono
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S ⊆
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock T := by
  intro g hg v hvT
  exact hg v fun hvS => hvT (hST hvS)

/-- The principal blocks cover the entire restricted-family group. -/
theorem iUnion_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock :
    (⋃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨S, hg⟩ :=
    V.exists_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock g
  exact Set.mem_iUnion.2 ⟨S, hg⟩

/-! ## The fixed Clifford-multiplication denominator set -/

/-- The finite set of rational places where some Clifford multiplication
structure constant is nonintegral. -/
def cliffordSpinCandidateMultiplicationBadPlaces :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Finset.univ.biUnion fun s : Finset (Fin n) =>
    Finset.univ.biUnion fun t : Finset (Fin n) =>
      Finset.univ.biUnion fun u : Finset (Fin n) =>
        finiteAdeleNonintegralPlaces
          (algebraMap ℚ RationalFiniteAdele
            (V.cliffordMulStructureConstant s t u))

private theorem cliffordMulStructureConstant_integral_of_not_mem_badPlaces
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateMultiplicationBadPlaces)
    (s t u : Finset (Fin n)) :
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        (algebraMap ℚ
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordMulStructureConstant s t u)) ∈
      v.adicCompletionIntegers ℚ := by
  have hv' : v ∉ finiteAdeleNonintegralPlaces
      (algebraMap ℚ RationalFiniteAdele
        (V.cliffordMulStructureConstant s t u)) := by
    intro hmem
    apply hv
    refine Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, ?_⟩
    refine Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, ?_⟩
    exact Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _, hmem⟩
  have hint :
      (algebraMap ℚ RationalFiniteAdele
          (V.cliffordMulStructureConstant s t u)) v ∈
        v.adicCompletionIntegers ℚ := by
    by_contra hnot
    exact hv' ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot)
  change algebraMap ℚ (v.adicCompletion ℚ)
      (V.cliffordMulStructureConstant s t u) ∈
    v.adicCompletionIntegers ℚ at hint
  simpa using hint

private theorem heightOnePadicCliffordSpinCandidateCoordinatesIntegral_mul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateMultiplicationBadPlaces)
    {g h : V.HeightOnePadicCliffordSpinCandidateGroup v}
    (hgc : ∀ s,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (g (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
        v.adicCompletionIntegers ℚ)
    (hgm : ∀ i j,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (g (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
        v.adicCompletionIntegers ℚ)
    (hhc : ∀ s,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (h (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
        v.adicCompletionIntegers ℚ)
    (hhm : ∀ i j,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          (h (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
        v.adicCompletionIntegers ℚ) :
    (∀ u,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
          ((g * h) (V.cliffordSpinCandidateCliffordCoordinate u)) ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ i j,
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g * h) (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
          v.adicCompletionIntegers ℚ) := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro u
    change e.symm
      ((V.cliffordSpinCandidatePointCoordinateMap
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (g * h)).1 u) ∈
        v.adicCompletionIntegers ℚ
    rw [V.cliffordSpinCandidatePointCoordinateMap_mul_fst, map_sum]
    exact Subring.sum_mem _ fun s _ => by
      rw [map_sum]
      exact Subring.sum_mem _ fun t _ => by
        rw [map_mul, map_mul]
        exact Subring.mul_mem _
          (Subring.mul_mem _ (hgc s) (hhc t))
          (V.cliffordMulStructureConstant_integral_of_not_mem_badPlaces
            v hv s t u)
  · intro i j
    change e.symm
      ((V.cliffordSpinCandidatePointCoordinateMap
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (g * h)).2 i j) ∈
        v.adicCompletionIntegers ℚ
    rw [V.cliffordSpinCandidatePointCoordinateMap_mul_snd, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hgm i k) (hhm k j)

theorem heightOnePadicCliffordSpinCandidateIsIntegral_mul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateMultiplicationBadPlaces)
    {g h : V.HeightOnePadicCliffordSpinCandidateGroup v}
    (hg : V.HeightOnePadicCliffordSpinCandidateIsIntegral v g)
    (hh : V.HeightOnePadicCliffordSpinCandidateIsIntegral v h) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v (g * h) := by
  have hforward :=
    V.heightOnePadicCliffordSpinCandidateCoordinatesIntegral_mul v hv
      hg.1 hg.2.1 hh.1 hh.2.1
  have hinverse :=
    V.heightOnePadicCliffordSpinCandidateCoordinatesIntegral_mul v hv
      hh.2.2.1 hh.2.2.2 hg.2.2.1 hg.2.2.2
  refine ⟨hforward.1, hforward.2, ?_, ?_⟩
  · simpa only [mul_inv_rev] using hinverse.1
  · simpa only [mul_inv_rev] using hinverse.2

theorem heightOnePadicCliffordSpinCandidateIsIntegral_inv
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g : V.HeightOnePadicCliffordSpinCandidateGroup v}
    (hg : V.HeightOnePadicCliffordSpinCandidateIsIntegral v g) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v g⁻¹ := by
  exact ⟨hg.2.2.1, hg.2.2.2, by simpa using hg.1, by simpa using hg.2.1⟩

/-- Multiplication sends the `S` and `T` blocks into their union enlarged by
the fixed Clifford-structure-constant bad-prime set. -/
theorem mul_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    {g h : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup}
    (hg : g ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S)
    (hh : h ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock T) :
    g * h ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
        ((S ∪ T) ∪ V.cliffordSpinCandidateMultiplicationBadPlaces) := by
  intro v hv
  have hvST : v ∉ S ∪ T := fun hmem => hv (Finset.mem_union_left _ hmem)
  have hvS : v ∉ S := fun hmem => hvST (Finset.mem_union_left _ hmem)
  have hvT : v ∉ T := fun hmem => hvST (Finset.mem_union_right _ hmem)
  have hvbad : v ∉ V.cliffordSpinCandidateMultiplicationBadPlaces :=
    fun hmem => hv (Finset.mem_union_right _ hmem)
  exact V.heightOnePadicCliffordSpinCandidateIsIntegral_mul v hvbad
    (hg v hvS) (hh v hvT)

/-- Inversion preserves every principal block exactly. -/
theorem inv_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    {g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup}
    (hg : g ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S) :
    g⁻¹ ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S := by
  intro v hv
  exact V.heightOnePadicCliffordSpinCandidateIsIntegral_inv v (hg v hv)

/-! ## Exact finite-adelic coordinate comparison -/

/-- Every finite-adelic coordinate of a point and its inverse is integral
outside `S`. -/
def IsFiniteAdelicCliffordSpinCandidateIntegralOutside
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) : Prop :=
  (∀ s, finiteAdeleNonintegralPlaces
      (a (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S) ∧
    (∀ i j, finiteAdeleNonintegralPlaces
      (a (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S) ∧
    (∀ s, finiteAdeleNonintegralPlaces
      (a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S) ∧
    (∀ i j, finiteAdeleNonintegralPlaces
      (a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S)

theorem isFiniteAdelicCliffordSpinCandidateIntegralOutside_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside S a ↔
      ∀ v, v ∉ S →
        (∀ s, a (V.cliffordSpinCandidateCliffordCoordinate s) v ∈
          v.adicCompletionIntegers ℚ) ∧
        (∀ i j, a (V.cliffordSpinCandidateMatrixCoordinate i j) v ∈
          v.adicCompletionIntegers ℚ) ∧
        (∀ s, a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) v ∈
          v.adicCompletionIntegers ℚ) ∧
        (∀ i j, a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) v ∈
          v.adicCompletionIntegers ℚ) := by
  constructor
  · rintro ⟨hc, hm, hci, hmi⟩ v hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s
      by_contra hnot
      exact hv (hc s ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot))
    · intro i j
      by_contra hnot
      exact hv (hm i j ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot))
    · intro s
      by_contra hnot
      exact hv (hci s ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot))
    · intro i j
      by_contra hnot
      exact hv (hmi i j ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot))
  · intro ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s v hv
      by_contra hnot
      exact ((mem_finiteAdeleNonintegralPlaces_iff _ _).1 hv)
        ((ha v hnot).1 s)
    · intro i j v hv
      by_contra hnot
      exact ((mem_finiteAdeleNonintegralPlaces_iff _ _).1 hv)
        ((ha v hnot).2.1 i j)
    · intro s v hv
      by_contra hnot
      exact ((mem_finiteAdeleNonintegralPlaces_iff _ _).1 hv)
        ((ha v hnot).2.2.1 s)
    · intro i j v hv
      by_contra hnot
      exact ((mem_finiteAdeleNonintegralPlaces_iff _ _).1 hv)
        ((ha v hnot).2.2.2 i j)

private theorem finiteAdelicCliffordSpinCandidateHeightOneComponent_apply_symm
    (a : V.FiniteAdelicCliffordSpinCandidateGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (c : V.cliffordSpinCandidateCoordinateRing) :
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v a) c) =
      a c v := by
  rw [V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply]
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm_apply_apply _

private theorem finiteAdelicCliffordSpinCandidateHeightOneComponent_inv_apply_symm
    (a : V.FiniteAdelicCliffordSpinCandidateGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (c : V.cliffordSpinCandidateCoordinateRing) :
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v a)⁻¹ c) =
      a⁻¹ c v := by
  rw [← (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_inv]
  exact V.finiteAdelicCliffordSpinCandidateHeightOneComponent_apply_symm a⁻¹ v c

/-- Local evaluation is integral exactly when all four finite-adelic
coordinate families are integral at that place. -/
theorem finiteAdelicCliffordSpinCandidateHeightOneComponent_isIntegral_iff
    (a : V.FiniteAdelicCliffordSpinCandidateGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v a) ↔
      (∀ s, a (V.cliffordSpinCandidateCliffordCoordinate s) v ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ i j, a (V.cliffordSpinCandidateMatrixCoordinate i j) v ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ s, a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) v ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ i j, a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) v ∈
        v.adicCompletionIntegers ℚ) := by
  unfold HeightOnePadicCliffordSpinCandidateIsIntegral
  simp only [V.finiteAdelicCliffordSpinCandidateHeightOneComponent_apply_symm,
    V.finiteAdelicCliffordSpinCandidateHeightOneComponent_inv_apply_symm]

/-- The finite-adelic/local multiplicative equivalence belongs to the
`S`-block exactly when every global coordinate is integral outside `S`. -/
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_mem_principalBlock_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a ∈
        V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock S ↔
      V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside S a := by
  rw [V.isFiniteAdelicCliffordSpinCandidateIntegralOutside_iff]
  constructor
  · intro ha v hv
    exact
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponent_isIntegral_iff
        a v).1 (ha v hv)
  · intro ha v hv
    exact
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponent_isIntegral_iff
        a v).2 (ha v hv)

end RationalQuadraticSpaceMatrix
