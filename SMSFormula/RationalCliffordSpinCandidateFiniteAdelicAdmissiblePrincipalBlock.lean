import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicPrincipalBlock

/-!
# Admissible principal blocks for finite-adelic Clifford--Spin points

The raw Clifford--Spin principal blocks are not subgroups at an arbitrary
finite exceptional set: multiplication may introduce denominators from the
rational Clifford structure constants, and the chosen finite-coordinate
presentation need not make the identity integral at every place.  This file
adjoins both finite bad sets once and for all.  The resulting normalized
blocks are subgroups.

Their inverse images in the genuine finite-adelic point group are literal
finite-coordinate integrality sets and are open.  We also package the
normalized block as a mixed dependent product of full local groups at the
exceptional places and integral local subgroups elsewhere.  The final mixed
comparison is algebraic only; reverse continuity and local compactness are
left to later files.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicSpinAdmissibleBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinAdmissibleBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## Canonical bad places and normalized blocks -/

/-- The union of the nonintegral places of every displayed coordinate of a
finite-adelic candidate point and its inverse. -/
def finiteAdelicCliffordSpinCandidateCoordinateBadPlaces
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (Finset.univ.biUnion fun s : Finset (Fin n) =>
      finiteAdeleNonintegralPlaces
        (a (V.cliffordSpinCandidateCliffordCoordinate s))) ∪
    (Finset.univ.biUnion fun i : Fin n =>
      Finset.univ.biUnion fun j : Fin n =>
        finiteAdeleNonintegralPlaces
          (a (V.cliffordSpinCandidateMatrixCoordinate i j))) ∪
    (Finset.univ.biUnion fun s : Finset (Fin n) =>
      finiteAdeleNonintegralPlaces
        (a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s))) ∪
    (Finset.univ.biUnion fun i : Fin n =>
      Finset.univ.biUnion fun j : Fin n =>
        finiteAdeleNonintegralPlaces
          (a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)))

/-- A point is integral outside the finite union of its own coordinate bad
places. -/
theorem isFiniteAdelicCliffordSpinCandidateIntegralOutside_coordinateBadPlaces
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside
      (V.finiteAdelicCliffordSpinCandidateCoordinateBadPlaces a) a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s v hv
    have hs : v ∈ Finset.univ.biUnion fun t : Finset (Fin n) =>
        finiteAdeleNonintegralPlaces
          (a (V.cliffordSpinCandidateCliffordCoordinate t)) :=
      Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, hv⟩
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hs))
  · intro i j v hv
    have hij : v ∈ Finset.univ.biUnion fun k : Fin n =>
        Finset.univ.biUnion fun l : Fin n =>
          finiteAdeleNonintegralPlaces
            (a (V.cliffordSpinCandidateMatrixCoordinate k l)) :=
      Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hv⟩⟩
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hij))
  · intro s v hv
    have hs : v ∈ Finset.univ.biUnion fun t : Finset (Fin n) =>
        finiteAdeleNonintegralPlaces
          (a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate t)) :=
      Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, hv⟩
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hs)
  · intro i j v hv
    have hij : v ∈ Finset.univ.biUnion fun k : Fin n =>
        Finset.univ.biUnion fun l : Fin n =>
          finiteAdeleNonintegralPlaces
            (a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate k l)) :=
      Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hv⟩⟩
    exact Finset.mem_union_right _ hij

/-- Enlarging the exceptional set preserves the global coordinate-integrality
condition. -/
theorem isFiniteAdelicCliffordSpinCandidateIntegralOutside_mono
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T)
    {a : V.FiniteAdelicCliffordSpinCandidateGroup}
    (ha : V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside S a) :
    V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside T a :=
  ⟨fun s => (ha.1 s).trans hST,
    fun i j => (ha.2.1 i j).trans hST,
    fun s => (ha.2.2.1 s).trans hST,
    fun i j => (ha.2.2.2 i j).trans hST⟩

/-- The fixed admissibility set: Clifford multiplication denominators and
all displayed coordinate denominators of the identity point. -/
def cliffordSpinCandidateAdmissibleBadPlaces :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.cliffordSpinCandidateMultiplicationBadPlaces ∪
    V.finiteAdelicCliffordSpinCandidateCoordinateBadPlaces
      (1 : V.FiniteAdelicCliffordSpinCandidateGroup)

/-- Normalize an exceptional set by adjoining every fixed bad place needed
for the chosen Clifford coordinate presentation. -/
def cliffordSpinCandidateAdmissibleExceptionalPlaces
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  S ∪ V.cliffordSpinCandidateAdmissibleBadPlaces

/-! ## Subgroups and the genuine finite-adelic open preimage -/

/-- The normalized `S`-block is a subgroup of the restricted local-family
group. -/
def finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Subgroup V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup where
  carrier :=
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)
  one_mem' := by
    have hglobal :=
      V.isFiniteAdelicCliffordSpinCandidateIntegralOutside_coordinateBadPlaces
        (1 : V.FiniteAdelicCliffordSpinCandidateGroup)
    have hsubset :
        V.finiteAdelicCliffordSpinCandidateCoordinateBadPlaces
            (1 : V.FiniteAdelicCliffordSpinCandidateGroup) ⊆
          V.cliffordSpinCandidateAdmissibleExceptionalPlaces S := by
      intro v hv
      simp [cliffordSpinCandidateAdmissibleExceptionalPlaces,
        cliffordSpinCandidateAdmissibleBadPlaces, hv]
    have hone :=
      (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_mem_principalBlock_iff
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)
        (1 : V.FiniteAdelicCliffordSpinCandidateGroup)).2
          (V.isFiniteAdelicCliffordSpinCandidateIntegralOutside_mono
            hsubset hglobal)
    simpa only [map_one] using hone
  mul_mem' := by
    intro g h hg hh
    have hmul :=
      V.mul_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
        hg hh
    simpa [cliffordSpinCandidateAdmissibleExceptionalPlaces,
      cliffordSpinCandidateAdmissibleBadPlaces, Finset.union_assoc,
      Finset.union_left_comm, Finset.union_comm] using hmul
  inv_mem' := by
    intro g hg
    exact
      V.inv_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock hg

@[simp]
theorem mem_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup) :
    g ∈ V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup S ↔
      g ∈ V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :=
  Iff.rfl

/-- The carrier of the normalized restricted-family principal block. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup S

/-- The corresponding subgroup in the genuine finite-adelic candidate group. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Subgroup V.FiniteAdelicCliffordSpinCandidateGroup :=
  (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup S).comap
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv.toMonoidHom

@[simp]
theorem
    mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) :
    a ∈ V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup S ↔
      V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) a := by
  exact
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_mem_principalBlock_iff
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) a

private theorem isOpen_finiteAdeleNonintegralPlaces_subset_spin
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

private theorem isOpen_isFiniteAdelicCliffordSpinCandidateIntegralOutside
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      {a : V.FiniteAdelicCliffordSpinCandidateGroup |
        V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside S a} := by
  rw [show
    {a : V.FiniteAdelicCliffordSpinCandidateGroup |
      V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside S a} =
    ({a : V.FiniteAdelicCliffordSpinCandidateGroup |
        ∀ s, finiteAdeleNonintegralPlaces
          (a (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S} ∩
      ({a : V.FiniteAdelicCliffordSpinCandidateGroup |
        ∀ i j, finiteAdeleNonintegralPlaces
          (a (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S} ∩
      ({a : V.FiniteAdelicCliffordSpinCandidateGroup |
        ∀ s, finiteAdeleNonintegralPlaces
          (a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S} ∩
      {a : V.FiniteAdelicCliffordSpinCandidateGroup |
        ∀ i j, finiteAdeleNonintegralPlaces
          (a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S}))) by
      ext a
      rfl]
  apply IsOpen.inter
  · rw [show
      {a : V.FiniteAdelicCliffordSpinCandidateGroup |
        ∀ s, finiteAdeleNonintegralPlaces
          (a (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S} =
        ⋂ s, {a : V.FiniteAdelicCliffordSpinCandidateGroup |
          finiteAdeleNonintegralPlaces
            (a (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S} by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    apply isOpen_iInter_of_finite
    intro s
    exact (isOpen_finiteAdeleNonintegralPlaces_subset_spin S).preimage
      (V.continuous_cliffordSpinCandidateCliffordCoordinate RationalFiniteAdele s)
  · apply IsOpen.inter
    · rw [show
        {a : V.FiniteAdelicCliffordSpinCandidateGroup |
          ∀ i j, finiteAdeleNonintegralPlaces
            (a (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S} =
          ⋂ i, ⋂ j, {a : V.FiniteAdelicCliffordSpinCandidateGroup |
            finiteAdeleNonintegralPlaces
              (a (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S} by
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_iInter]]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      exact (isOpen_finiteAdeleNonintegralPlaces_subset_spin S).preimage
        (V.continuous_cliffordSpinCandidateMatrixCoordinate RationalFiniteAdele i j)
    · apply IsOpen.inter
      · rw [show
          {a : V.FiniteAdelicCliffordSpinCandidateGroup |
            ∀ s, finiteAdeleNonintegralPlaces
              (a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S} =
            ⋂ s, {a : V.FiniteAdelicCliffordSpinCandidateGroup |
              finiteAdeleNonintegralPlaces
                (a⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)) ⊆ S} by
            ext a
            simp only [Set.mem_setOf_eq, Set.mem_iInter]]
        apply isOpen_iInter_of_finite
        intro s
        exact (isOpen_finiteAdeleNonintegralPlaces_subset_spin S).preimage
          ((V.continuous_cliffordSpinCandidateCliffordCoordinate
            RationalFiniteAdele s).comp continuous_inv)
      · rw [show
          {a : V.FiniteAdelicCliffordSpinCandidateGroup |
            ∀ i j, finiteAdeleNonintegralPlaces
              (a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S} =
            ⋂ i, ⋂ j, {a : V.FiniteAdelicCliffordSpinCandidateGroup |
              finiteAdeleNonintegralPlaces
                (a⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)) ⊆ S} by
            ext a
            simp only [Set.mem_setOf_eq, Set.mem_iInter]]
        apply isOpen_iInter_of_finite
        intro i
        apply isOpen_iInter_of_finite
        intro j
        exact (isOpen_finiteAdeleNonintegralPlaces_subset_spin S).preimage
          ((V.continuous_cliffordSpinCandidateMatrixCoordinate
            RationalFiniteAdele i j).comp continuous_inv)

/-- The normalized principal-block subgroup is open in the genuine
finite-adele topology. -/
theorem isOpen_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
        S : Set V.FiniteAdelicCliffordSpinCandidateGroup) := by
  rw [show
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
        S : Set V.FiniteAdelicCliffordSpinCandidateGroup) =
        {a | V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside
          (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) a} by
      ext a
      exact
        V.mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup_iff
          S a]
  exact V.isOpen_isFiniteAdelicCliffordSpinCandidateIntegralOutside
    (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)

/-! ## Local factors and the mixed product -/

private theorem heightOnePadicCliffordSpinCandidateIsIntegral_one_of_admissible
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleBadPlaces) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v 1 := by
  have hone :
      (1 : V.FiniteAdelicCliffordSpinCandidateRestrictedFamilyGroup) ∈
        V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup ∅ :=
    Subgroup.one_mem _
  have hv' : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ := by
    simpa [cliffordSpinCandidateAdmissibleExceptionalPlaces] using hv
  exact hone v hv'

/-- The local factor of a normalized principal block. -/
def finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Subgroup (V.HeightOnePadicCliffordSpinCandidateGroup v) where
  carrier :=
    {g | v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S →
      V.HeightOnePadicCliffordSpinCandidateIsIntegral v g}
  one_mem' := by
    intro hv
    exact V.heightOnePadicCliffordSpinCandidateIsIntegral_one_of_admissible
      v (fun hbad => hv (by
        simp [cliffordSpinCandidateAdmissibleExceptionalPlaces, hbad]))
  mul_mem' := by
    intro g h hg hh hv
    have hvbad : v ∉ V.cliffordSpinCandidateMultiplicationBadPlaces := by
      intro hbad
      exact hv (by
        simp [cliffordSpinCandidateAdmissibleExceptionalPlaces,
          cliffordSpinCandidateAdmissibleBadPlaces, hbad])
    exact V.heightOnePadicCliffordSpinCandidateIsIntegral_mul v hvbad
      (hg hv) (hh hv)
  inv_mem' := by
    intro g hg hv
    exact V.heightOnePadicCliffordSpinCandidateIsIntegral_inv v (hg hv)

@[simp]
theorem
    mem_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicCliffordSpinCandidateGroup v) :
    g ∈ V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v ↔
      (v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S →
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v g) :=
  Iff.rfl

/-- At a normalized exceptional place, the local factor is the full group. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup_eq_top
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v = ⊤ := by
  ext g
  simp [hv]

/-- The displayed carrier of the normalized local factor. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup S v

/-- The mixed dependent product of normalized local factors. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v

/-- Componentwise inclusion into the unrestricted local product. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S →*
      V.HeightOnePadicCliffordSpinCandidateGroupProduct where
  toFun g v := (g v).1
  map_one' := by
    funext v
    rfl
  map_mul' := by
    intro g h
    funext v
    rfl

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom S g v =
      (g v).1 :=
  rfl

/-- Componentwise inclusion of the mixed carrier is continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom S) :=
  continuous_pi fun v =>
    continuous_subtype_val.comp (continuous_apply v)

/-- The mixed product has exactly the normalized outside-integrality image. -/
theorem
    range_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set.range
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom S) =
      {g : V.HeightOnePadicCliffordSpinCandidateGroupProduct |
        ∀ v, v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S →
          V.HeightOnePadicCliffordSpinCandidateIsIntegral v (g v)} := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    intro v hv
    exact (x v).2 hv
  · intro hg
    let x : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S :=
      fun v => ⟨g v, hg v⟩
    refine ⟨x, ?_⟩
    funext v
    rfl

/-- A mixed family, viewed as a restricted family in the normalized block. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlock S where
  toFun g := by
    have hrestricted :
        V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily
          (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom
            S g) :=
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S).eventually_cofinite_notMem.mono
        fun v hv => (g v).2 hv
    exact
      ⟨⟨V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom
          S g, hrestricted⟩,
        fun v hv => (g v).2 hv⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl
  map_mul' := by
    intro g h
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom_apply_component
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
      S g).1.1 v = (g v).1 :=
  rfl

/-- A normalized restricted-family block, viewed in the mixed product. -/
def finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockToMixedHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toFun g v := ⟨g.1.1 v, fun hv => g.2 v hv⟩
  map_one' := by
    funext v
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    funext v
    apply Subtype.ext
    rfl

/-- The normalized principal block is algebraically the mixed product of its
local factors. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S ≃*
      V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlock S where
  toFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom S
  invFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockToMixedHom S
  left_inv := by
    intro g
    funext v
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl
  map_mul' :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
      S).map_mul

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockMulEquiv_apply_component
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockMulEquiv
      S g).1.1 v = (g v).1 :=
  rfl

end RationalQuadraticSpaceMatrix
