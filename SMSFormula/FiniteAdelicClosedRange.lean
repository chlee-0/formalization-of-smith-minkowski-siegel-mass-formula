import SMSFormula.FiniteAdelicEntryMap

/-!
# The pair map's range is closed, and the compact open subgroup exists

`FiniteAdelicEntryMap` needs one hypothesis in the orbital line: that the pair map
`g |-> (g, g^-1)` of the finite-adelic special orthogonal group has closed range.  This file
proves it and, with it, the existence of a compact open subgroup.

The range is the graph cut down by the defining conditions.  The inversion graph is closed, but the
pair map's range is generally a strict subset of it.  The range is the graph met with the condition
defining the subgroup, read on the first coordinate alone.  So the identification is an algebraic
statement -- a pair with `A B = B A = 1` reassembles into a unit, and that unit lies in the subgroup
precisely when `A` satisfies the defining condition -- and closedness then costs only closedness of
that condition.

Concretely the condition is `Aᵀ F A = F` together with `det A = 1`: each is the preimage of a point
under a continuous matrix map, so each is closed, and nothing beyond continuity of multiplication,
transposition and the determinant is used.

Chaining with the integral matrices as a compact open submonoid, the graph criterion and the
reduction to the finite factor, the full adelic acting group has a compact open subgroup, with no
further hypothesis.

Scope.  This is the subgroup statement alone.  It exhibits no orbit, performs no averaging, and
says nothing about the number `Lambda(1_U) = mu_nat(U)`.
-/

namespace SMSFormula.CompactOpenCriterion

open Matrix

/-! ## The range of the pair map, identified -/

/-- The range of the pair map is the inversion graph cut down by the defining condition.  A pair
with `A B = B A = 1` reassembles into a unit, and that unit lies in the nested subgroup precisely
when `A` lies in the defining set -- so the containment recorded earlier becomes an equality as soon
as the subgroup is cut out by a condition on the underlying element. -/
theorem range_nestedEntryPair_eq {M : Type*} [Monoid M] {K : Subgroup Mˣ} (J : Subgroup K)
    (S : Set M) (hmem : ∀ u : Mˣ, (u : M) ∈ S ↔ ∃ h : u ∈ K, (⟨u, h⟩ : K) ∈ J) :
    (Set.range fun g : J ↦ (nestedEntryHom J g, nestedEntryHom J g⁻¹)) =
      {p : M × M | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ p.1 ∈ S} := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
    · exact (hmem _).mpr ⟨(g : K).2, g.2⟩
  · obtain ⟨A, B⟩ := p
    rintro ⟨hab, hba, hS⟩
    obtain ⟨h, hJ⟩ := (hmem ⟨A, B, hab, hba⟩).mp hS
    exact ⟨⟨⟨⟨A, B, hab, hba⟩, h⟩, hJ⟩, rfl⟩

/-- Hence the range is closed whenever the defining set is.  The inversion graph is closed in a
Hausdorff topological monoid, and the extra condition is a preimage under the first projection. -/
theorem isClosed_range_nestedEntryPair {M : Type*} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {K : Subgroup Mˣ} (J : Subgroup K) (S : Set M)
    (hS : IsClosed S) (hmem : ∀ u : Mˣ, (u : M) ∈ S ↔ ∃ h : u ∈ K, (⟨u, h⟩ : K) ∈ J) :
    IsClosed (Set.range fun g : J ↦ (nestedEntryHom J g, nestedEntryHom J g⁻¹)) := by
  rw [range_nestedEntryPair_eq J S hmem]
  have hsplit : {p : M × M | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ p.1 ∈ S} =
      {p : M × M | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} ∩ (Prod.fst ⁻¹' S) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hsplit]
  exact (isClosed_inverseGraph M).inter (hS.preimage continuous_fst)

/-- And the packaged criterion now has no closed-range hypothesis either: a defining closed set for
the nested subgroup supplies it, leaving only the compact open submonoid. -/
theorem isCompact_isOpen_integralSubgroup_of_definingSet {M : Type*} [Monoid M]
    [TopologicalSpace M] [ContinuousMul M] [T2Space M] {K : Subgroup Mˣ} (J : Subgroup K)
    [TopologicalSpace J] [IsTopologicalGroup J]
    (hiota : Continuous (nestedEntryHom J))
    (hemb : Topology.IsEmbedding fun g : J ↦ (nestedEntryHom J g, nestedEntryHom J g⁻¹))
    (S : Set M) (hS : IsClosed S)
    (hmem : ∀ u : Mˣ, (u : M) ∈ S ↔ ∃ h : u ∈ K, (⟨u, h⟩ : K) ∈ J)
    {C : Submonoid M} (hCcompact : IsCompact (C : Set M)) (hCopen : IsOpen (C : Set M)) :
    IsCompact ((integralSubgroup (nestedEntryHom J) C : Subgroup J) : Set J) ∧
      IsOpen ((integralSubgroup (nestedEntryHom J) C : Subgroup J) : Set J) :=
  isCompact_isOpen_integralSubgroup_of_closedGraph (nestedEntryHom J) hiota hemb
    (isClosed_range_nestedEntryPair J S hS hmem) hCcompact hCopen

end SMSFormula.CompactOpenCriterion

namespace PositiveDefiniteIntegralLattice

open SMSFormula.CompactOpenCriterion Matrix

variable {n : ℕ}

/-- The defining set of the finite-adelic special orthogonal group, as a set of matrices: form
preserving and of determinant one. -/
def finiteAdelicSpecialOrthogonalMatrixSet (L : PositiveDefiniteIntegralLattice n) :
    Set (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
  {A | Aᵀ * L.finiteAdelicFormMatrix * A = L.finiteAdelicFormMatrix ∧ A.det = 1}

/-- It is closed: each condition is the preimage of a point under a continuous matrix map, using
only continuity of multiplication, transposition and the determinant. -/
theorem isClosed_finiteAdelicSpecialOrthogonalMatrixSet (L : PositiveDefiniteIntegralLattice n) :
    IsClosed L.finiteAdelicSpecialOrthogonalMatrixSet := by
  letI : T2Space RationalFiniteAdele := t2Space_rationalFiniteAdele
  letI : T2Space (Matrix (Fin n) (Fin n) RationalFiniteAdele) := inferInstance
  have hform : IsClosed {A : Matrix (Fin n) (Fin n) RationalFiniteAdele |
      Aᵀ * L.finiteAdelicFormMatrix * A = L.finiteAdelicFormMatrix} :=
    isClosed_eq
      ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have hdet : IsClosed {A : Matrix (Fin n) (Fin n) RationalFiniteAdele | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  exact hform.inter hdet

/-- And it does cut out the group: a unit's underlying matrix lies in the set exactly when the unit
is orthogonal and its image in the orthogonal group is special. -/
theorem mem_finiteAdelicSpecialOrthogonalMatrixSet_iff (L : PositiveDefiniteIntegralLattice n)
    (u : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) :
    (u : Matrix (Fin n) (Fin n) RationalFiniteAdele) ∈
        L.finiteAdelicSpecialOrthogonalMatrixSet ↔
      ∃ h : u ∈ L.finiteAdelicOrthogonalMatrixSubgroup,
        (⟨u, h⟩ : L.ConcreteFiniteAdelicOrthogonalGroup) ∈
          L.finiteAdelicSpecialOrthogonalMatrixSubgroup := by
  constructor
  · rintro ⟨hform, hdet⟩
    refine ⟨(L.mem_finiteAdelicOrthogonalMatrixSubgroup_iff u).mpr hform, ?_⟩
    exact (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff _).mpr hdet
  · rintro ⟨h, hJ⟩
    exact ⟨(L.mem_finiteAdelicOrthogonalMatrixSubgroup_iff u).mp h,
      (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff _).mp hJ⟩

/-- The last hypothesis is discharged: the pair map of the repository's own finite-adelic special
orthogonal group has closed range. -/
theorem isClosed_range_finiteAdelicSpecialOrthogonalEntryPair (L : PositiveDefiniteIntegralLattice n) :
    IsClosed (Set.range fun g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup ↦
      (L.finiteAdelicSpecialOrthogonalEntryHom g,
        L.finiteAdelicSpecialOrthogonalEntryHom g⁻¹)) := by
  letI : T2Space RationalFiniteAdele := t2Space_rationalFiniteAdele
  letI : T2Space (Matrix (Fin n) (Fin n) RationalFiniteAdele) := inferInstance
  exact isClosed_range_nestedEntryPair L.finiteAdelicSpecialOrthogonalMatrixSubgroup
    L.finiteAdelicSpecialOrthogonalMatrixSet
    L.isClosed_finiteAdelicSpecialOrthogonalMatrixSet
    (L.mem_finiteAdelicSpecialOrthogonalMatrixSet_iff)

/-- The finite factor has a compact open subgroup, unconditionally: the integral matrices are a
compact open submonoid and the pair map is a closed embedding. -/
theorem exists_compactOpen_finiteAdelicSpecialOrthogonal (L : PositiveDefiniteIntegralLattice n) :
    ∃ K : Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup,
      IsCompact (K : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) ∧
        IsOpen (K : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
  letI : T2Space RationalFiniteAdele := t2Space_rationalFiniteAdele
  letI : T2Space (Matrix (Fin n) (Fin n) RationalFiniteAdele) := inferInstance
  refine ⟨integralSubgroup L.finiteAdelicSpecialOrthogonalEntryHom
    (matrixSubmonoid integralFiniteAdeleSubring), ?_⟩
  exact isCompact_isOpen_integralSubgroup_of_closedGraph
    L.finiteAdelicSpecialOrthogonalEntryHom
    L.continuous_finiteAdelicSpecialOrthogonalEntryHom
    L.isEmbedding_finiteAdelicSpecialOrthogonalEntryPair
    L.isClosed_range_finiteAdelicSpecialOrthogonalEntryPair
    (isCompact_matrixSubmonoid isCompact_integralFiniteAdeleSubring)
    (isOpen_matrixSubmonoid isOpen_integralFiniteAdeleSubring)

/-- And SO does the full adelic acting group, with no hypothesis: the archimedean factor is compact
by positive definiteness, so the finite witness transports. -/
theorem exists_compactOpen_fullAdelicSpecialOrthogonal_unconditional (L : PositiveDefiniteIntegralLattice n) :
    ∃ K : Subgroup L.ConcreteFullAdelicSpecialOrthogonalGroup,
      IsCompact (K : Set L.ConcreteFullAdelicSpecialOrthogonalGroup) ∧
        IsOpen (K : Set L.ConcreteFullAdelicSpecialOrthogonalGroup) := by
  obtain ⟨K, hcompact, hopen⟩ := L.exists_compactOpen_finiteAdelicSpecialOrthogonal
  exact L.exists_compactOpen_fullAdelicSpecialOrthogonal hcompact hopen

end PositiveDefiniteIntegralLattice

namespace SMSFormula.CompactOpenCriterion

/-! ## What the subgroup buys the ambient group

The orbital chain asks two things of the acting group that are not about any orbit: local
compactness, which the Haar and Riesz layers consume, and sigma-compactness, which is the hypothesis
of mathlib's open-orbit-map Baire argument.  A compact open subgroup supplies the first outright and
the second together with second countability. -/

/-- A compact open subgroup makes the ambient group locally compact: it is a compact neighbourhood
of the identity, which is all mathlib's group criterion needs. -/
theorem locallyCompactSpace_of_compactOpen_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {K : Subgroup G} (hcompact : IsCompact (K : Set G))
    (hopen : IsOpen (K : Set G)) : LocallyCompactSpace G :=
  hcompact.locallyCompactSpace_of_mem_nhds_of_group (hopen.mem_nhds K.one_mem)

/-- And with second countability, sigma-compact -- the hypothesis the open-orbit-map argument takes.
Second countability is a real hypothesis here and is not supplied by the subgroup. -/
theorem sigmaCompactSpace_of_compactOpen_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] {K : Subgroup G}
    (hcompact : IsCompact (K : Set G)) (hopen : IsOpen (K : Set G)) : SigmaCompactSpace G := by
  letI : LocallyCompactSpace G := locallyCompactSpace_of_compactOpen_subgroup hcompact hopen
  infer_instance

end SMSFormula.CompactOpenCriterion

namespace PositiveDefiniteIntegralLattice

open SMSFormula.CompactOpenCriterion

variable {n : ℕ}

/-- Hence the full adelic acting group is locally compact, unconditionally. -/
theorem locallyCompactSpace_fullAdelicSpecialOrthogonal (L : PositiveDefiniteIntegralLattice n) :
    LocallyCompactSpace L.ConcreteFullAdelicSpecialOrthogonalGroup := by
  obtain ⟨K, hcompact, hopen⟩ := L.exists_compactOpen_fullAdelicSpecialOrthogonal_unconditional
  exact locallyCompactSpace_of_compactOpen_subgroup hcompact hopen

/-- And sigma-compact once it is second countable.  Second countability stays an explicit input to this criterion. The concrete lattice
group already has that instance; `AdelicGaussianFiberOrbitalComparison` transports it through the
existing equivalence and discharges this input for the actual fiber action. -/
theorem sigmaCompactSpace_fullAdelicSpecialOrthogonal (L : PositiveDefiniteIntegralLattice n)
    [SecondCountableTopology L.ConcreteFullAdelicSpecialOrthogonalGroup] :
    SigmaCompactSpace L.ConcreteFullAdelicSpecialOrthogonalGroup := by
  obtain ⟨K, hcompact, hopen⟩ := L.exists_compactOpen_fullAdelicSpecialOrthogonal_unconditional
  exact sigmaCompactSpace_of_compactOpen_subgroup hcompact hopen

end PositiveDefiniteIntegralLattice
