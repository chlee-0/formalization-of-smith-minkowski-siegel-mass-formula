import SMSFormula.RationalSpecialOrthogonalFiniteAdelicRestrictedFamilyCarrier

/-!
# Principal blocks of finite-adelic special-orthogonal restricted families

For an arbitrary rational quadratic-space matrix `V` and a finite set `S` of
height-one places, this module defines the principal block of restricted local
special-orthogonal families whose matrix and inverse matrix are integral at
every place outside `S`.

Every restricted family belongs to one such block.  The blocks are monotone,
cover the whole restricted-family carrier, multiply into the union block, and
are stable under inverse.  On the finite-adelic side, the corresponding
condition is stated literally using the finite sets of nonintegral places of
every matrix and inverse-matrix entry.  Simultaneous evaluation identifies
that entrywise condition with membership in the local principal block.

This module is set- and carrier-level.  It does not put the unrestricted
product subtype topology on the restricted family, transport a measure, or
assert reverse continuity.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicPrincipalBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicPrincipalBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## Restricted-family principal blocks -/

/-- The principal block with exceptional set `S`: both the local matrix and
its inverse are integral at every height-one place outside `S`. -/
def finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FiniteAdelicSpecialOrthogonalRestrictedFamily :=
  {g | ∀ v, v ∉ S →
    V.HeightOnePadicSpecialOrthogonalIsIntegral v (g.1 v)}

@[simp]
theorem mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock_iff
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    g ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S ↔
      ∀ v, v ∉ S →
        V.HeightOnePadicSpecialOrthogonalIsIntegral v (g.1 v) :=
  Iff.rfl

/-- Every restricted family is integral outside some finite exceptional
set. -/
theorem exists_mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      g ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S := by
  have hfinite :
      {v : IsDedekindDomain.HeightOneSpectrum ℤ |
        ¬V.HeightOnePadicSpecialOrthogonalIsIntegral v (g.1 v)}.Finite :=
    Filter.eventually_cofinite.mp
      (show V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g.1 from g.2)
  refine ⟨hfinite.toFinset, ?_⟩
  intro v hv
  by_contra hnot
  exact hv (by simpa using hnot)

/-- Principal blocks are monotone in their exceptional set. -/
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S ⊆
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock T := by
  intro g hg v hvT
  exact hg v fun hvS => hvT (hST hvS)

/-- The union of all finite-exceptional principal blocks is the entire
restricted-family carrier. -/
theorem iUnion_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n) :
    (⋃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨S, hg⟩ :=
    V.exists_mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock g
  exact Set.mem_iUnion.2 ⟨S, hg⟩

private theorem heightOnePadicSpecialOrthogonalIsIntegral_mul_of_principalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g h : V.HeightOnePadicSpecialOrthogonalGroup v}
    (hg : V.HeightOnePadicSpecialOrthogonalIsIntegral v g)
    (hh : V.HeightOnePadicSpecialOrthogonalIsIntegral v h) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v (g * h) := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro i j
    change e.symm ((g.1.1.1 * h.1.1.1) i j) ∈
      v.adicCompletionIntegers ℚ
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hg.1 i k) (hh.1 k j)
  · intro i j
    change e.symm (((h.1.1⁻¹).1 * (g.1.1⁻¹).1) i j) ∈
      v.adicCompletionIntegers ℚ
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hh.2 i k) (hg.2 k j)

private theorem heightOnePadicSpecialOrthogonalIsIntegral_inv_of_principalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g : V.HeightOnePadicSpecialOrthogonalGroup v}
    (hg : V.HeightOnePadicSpecialOrthogonalIsIntegral v g) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v g⁻¹ := by
  constructor
  · exact hg.2
  · simpa using hg.1

/-- Multiplication sends the `S` and `T` principal blocks into the
`S ∪ T` block. -/
theorem mul_mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    {g h : V.FiniteAdelicSpecialOrthogonalRestrictedFamily}
    (hg :
      g ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S)
    (hh :
      h ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock T) :
    g * h ∈
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
        (S ∪ T) := by
  classical
  intro v hv
  have hvS : v ∉ S := fun hmem => hv (Finset.mem_union_left T hmem)
  have hvT : v ∉ T := fun hmem => hv (Finset.mem_union_right S hmem)
  exact
    heightOnePadicSpecialOrthogonalIsIntegral_mul_of_principalBlock
      V v (hg v hvS) (hh v hvT)

/-- Inverse preserves each principal block. -/
theorem inv_mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    {g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily}
    (hg :
      g ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S) :
    g⁻¹ ∈
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S := by
  intro v hv
  exact
    heightOnePadicSpecialOrthogonalIsIntegral_inv_of_principalBlock
      V v (hg v hv)

/-! ## The exact finite-adelic entrywise bound -/

/-- Every matrix and inverse-matrix entry of `a` has all of its nonintegral
places in the finite exceptional set `S`. -/
def IsFiniteAdelicSpecialOrthogonalIntegralOutside
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicSpecialOrthogonalGroup) : Prop :=
  (∀ i j,
      finiteAdeleNonintegralPlaces (a.1.1.1 i j) ⊆ S) ∧
    (∀ i j,
      finiteAdeleNonintegralPlaces ((a.1.1⁻¹).1 i j) ⊆ S)

theorem isFiniteAdelicSpecialOrthogonalIntegralOutside_iff
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a ↔
      ∀ v, v ∉ S →
        (∀ i j, a.1.1.1 i j v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ i j, (a.1.1⁻¹).1 i j v ∈
            v.adicCompletionIntegers ℚ) := by
  constructor
  · intro ha v hv
    constructor
    · intro i j
      by_contra hnot
      exact hv (ha.1 i j ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot))
    · intro i j
      by_contra hnot
      exact hv (ha.2 i j ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot))
  · intro ha
    constructor
    · intro i j v hv
      by_contra hnot
      exact
        ((mem_finiteAdeleNonintegralPlaces_iff _ _).1 hv)
          ((ha v hnot).1 i j)
    · intro i j v hv
      by_contra hnot
      exact
        ((mem_finiteAdeleNonintegralPlaces_iff _ _).1 hv)
          ((ha v hnot).2 i j)

/-- Local evaluation is integral exactly when the original finite-adelic
matrix and inverse entries are integral at that place. -/
theorem finiteAdelicSpecialOrthogonalHeightOneComponent_isIntegral_iff
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v
        (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a) ↔
      (∀ i j, a.1.1.1 i j v ∈ v.adicCompletionIntegers ℚ) ∧
        (∀ i j, (a.1.1⁻¹).1 i j v ∈
          v.adicCompletionIntegers ℚ) := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hmatrix (b : V.FiniteAdelicSpecialOrthogonalGroup) (i j : Fin n) :
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v b).1.1.1 i j =
        e (b.1.1.1 i j v) := by
    exact congr_fun (congr_fun
      (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix b v) i) j
  have hinverse (i j : Fin n) :
      ((V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1⁻¹).1
          i j =
        e ((a.1.1⁻¹).1 i j v) := by
    have hmapinv :=
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v).map_inv a
    rw [← show
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v (a⁻¹)).1.1 =
          (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1⁻¹ by
        exact congrArg (fun z => z.1.1) hmapinv]
    exact hmatrix (a⁻¹) i j
  constructor
  · intro ha
    constructor
    · intro i j
      have hij := ha.1 i j
      change e.symm
        ((V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1.1
          i j) ∈ v.adicCompletionIntegers ℚ at hij
      rw [hmatrix a i j] at hij
      simpa using hij
    · intro i j
      have hij := ha.2 i j
      change e.symm
        (((V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1⁻¹).1
          i j) ∈ v.adicCompletionIntegers ℚ at hij
      rw [hinverse i j] at hij
      simpa using hij
  · intro ha
    constructor
    · intro i j
      change e.symm
        ((V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1.1
          i j) ∈ v.adicCompletionIntegers ℚ
      rw [hmatrix a i j]
      simpa using ha.1 i j
    · intro i j
      change e.symm
        (((V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1⁻¹).1
          i j) ∈ v.adicCompletionIntegers ℚ
      rw [hinverse i j]
      simpa using ha.2 i j

/-- Simultaneous finite-adelic evaluation belongs to the principal block
exactly when every finite-adele matrix and inverse entry is integral outside
the same exceptional set. -/
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_mem_principalBlock_iff
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv a ∈
        V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S ↔
      V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a := by
  rw [V.isFiniteAdelicSpecialOrthogonalIntegralOutside_iff]
  constructor
  · intro ha v hv
    exact
      (V.finiteAdelicSpecialOrthogonalHeightOneComponent_isIntegral_iff
        a v).1 (ha v hv)
  · intro ha v hv
    exact
      (V.finiteAdelicSpecialOrthogonalHeightOneComponent_isIntegral_iff
        a v).2 (ha v hv)

/-- The inverse image of a restricted-family principal block under the
finite-adelic carrier equivalence is exactly the literal entrywise
finite-adele exceptional-place bound. -/
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_preimage_principalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv :
        V.FiniteAdelicSpecialOrthogonalGroup →
          V.FiniteAdelicSpecialOrthogonalRestrictedFamily) ⁻¹'
        V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S =
      {a | V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a} := by
  ext a
  exact
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_mem_principalBlock_iff
      S a

private theorem isOpen_finiteAdeleNonintegralPlaces_subset
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      {a : RationalFiniteAdele | finiteAdeleNonintegralPlaces a ⊆ S} := by
  have hopen :
      IsOpen
        {a : RationalFiniteAdele |
          ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_imp_mem
      (fun _v => Valued.isOpen_valuationSubring _)
  convert hopen using 1
  ext a
  constructor
  · intro ha v hvS
    by_contra hnot
    exact hvS (ha ((mem_finiteAdeleNonintegralPlaces_iff a v).2 hnot))
  · intro ha v hv
    by_contra hvS
    exact
      ((mem_finiteAdeleNonintegralPlaces_iff a v).1 hv)
        (ha v hvS)

private theorem isOpen_isFiniteAdelicSpecialOrthogonalIntegralOutside
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      {a : V.FiniteAdelicSpecialOrthogonalGroup |
        V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a} := by
  change IsOpen
    ({a : V.FiniteAdelicSpecialOrthogonalGroup |
        ∀ i j, finiteAdeleNonintegralPlaces (a.1.1.1 i j) ⊆ S} ∩
      {a : V.FiniteAdelicSpecialOrthogonalGroup |
        ∀ i j, finiteAdeleNonintegralPlaces ((a.1.1⁻¹).1 i j) ⊆ S})
  apply IsOpen.inter
  · rw [show
      {a : V.FiniteAdelicSpecialOrthogonalGroup |
        ∀ i j, finiteAdeleNonintegralPlaces (a.1.1.1 i j) ⊆ S} =
        ⋂ i, ⋂ j,
          {a : V.FiniteAdelicSpecialOrthogonalGroup |
            finiteAdeleNonintegralPlaces (a.1.1.1 i j) ⊆ S} by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_finiteAdeleNonintegralPlaces_subset S |>.preimage
    have hu : Continuous
        (fun a : V.FiniteAdelicSpecialOrthogonalGroup =>
          (a.1.1 : GL (Fin n) RationalFiniteAdele)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hm : Continuous
        (fun a : V.FiniteAdelicSpecialOrthogonalGroup =>
          (a.1.1.1 : Matrix (Fin n) (Fin n) RationalFiniteAdele)) :=
      Units.continuous_val.comp hu
    exact (continuous_apply j).comp ((continuous_apply i).comp hm)
  · rw [show
      {a : V.FiniteAdelicSpecialOrthogonalGroup |
        ∀ i j, finiteAdeleNonintegralPlaces ((a.1.1⁻¹).1 i j) ⊆ S} =
        ⋂ i, ⋂ j,
          {a : V.FiniteAdelicSpecialOrthogonalGroup |
            finiteAdeleNonintegralPlaces ((a.1.1⁻¹).1 i j) ⊆ S} by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_finiteAdeleNonintegralPlaces_subset S |>.preimage
    have hu : Continuous
        (fun a : V.FiniteAdelicSpecialOrthogonalGroup =>
          (a.1.1 : GL (Fin n) RationalFiniteAdele)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hmui : Continuous
        (fun a : V.FiniteAdelicSpecialOrthogonalGroup =>
          ((a.1.1⁻¹).1 :
            Matrix (Fin n) (Fin n) RationalFiniteAdele)) :=
      Units.continuous_val.comp (continuous_inv.comp hu)
    exact (continuous_apply j).comp ((continuous_apply i).comp hmui)

/-- The finite-adelic preimage of a principal block is open in the actual
restricted-product topology.  This statement does not assert that the block
is open in the subtype topology inherited from the unrestricted local
product. -/
theorem isOpen_finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_preimage_principalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      ((V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv :
          V.FiniteAdelicSpecialOrthogonalGroup →
            V.FiniteAdelicSpecialOrthogonalRestrictedFamily) ⁻¹'
        V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S) := by
  rw [
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_preimage_principalBlock]
  exact isOpen_isFiniteAdelicSpecialOrthogonalIntegralOutside V S

end RationalQuadraticSpaceMatrix
