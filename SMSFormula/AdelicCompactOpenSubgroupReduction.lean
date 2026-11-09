import SMSFormula.AdelicProperFullPresentation

/-!
# The compact open subgroup reduces to the finite factor

`RieszOrbitalComparison` left exactly two items in the orbital line, the first being: exhibit a
concrete compact open subgroup of the adelic acting group.  This file narrows that item to the
finite factor alone, and exhibits the reason.

The product step.  In a product group whose first factor is compact, the whole first factor paired
with a compact open subgroup of the second is again a compact open subgroup.  Transported along a
topological group isomorphism -- which is what the repository's own splitting of the full-adelic
special orthogonal group into its real and finite-adelic factors is -- that turns a compact open
subgroup of the finite factor into one of the full adelic group, with nothing asked of the
archimedean side beyond compactness.

And compactness of the archimedean side is not a convenience but a necessity.  A connected group
that has a compact open subgroup is compact: an open subgroup is closed, so it is a nonempty clopen
set and connectedness makes it everything.  Hence a group like the additive reals -- connected and
noncompact -- has no compact open subgroup at all, and the archimedean factor must be compact for
the route's subgroup to exist.  What supplies that here is positive definiteness: the repository
already proves the real special orthogonal group of the lattice is a compact space, and for an
indefinite form it would not be.

Negative scope.  No compact open subgroup is constructed -- the finite-adelic one is a hypothesis
throughout, and this file only shows that it is the only thing missing.  Nothing is said about the
one number, about transitivity, or about the orbit; and a compact open subgroup is not by itself a
measure comparison.
-/

namespace SMSFormula.AdelicCompactOpen

open Set

/-! ## The product step -/

/-- A compact open subgroup of the second factor, paired with the whole first factor, is compact and
open in the product -- provided the first factor is compact. -/
theorem isCompact_isOpen_prod_top {G₁ G₂ : Type*} [Group G₁] [Group G₂] [TopologicalSpace G₁]
    [TopologicalSpace G₂] [CompactSpace G₁] {K : Subgroup G₂} (hcompact : IsCompact (K : Set G₂))
    (hopen : IsOpen (K : Set G₂)) :
    IsCompact (((⊤ : Subgroup G₁).prod K : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) ∧
      IsOpen (((⊤ : Subgroup G₁).prod K : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
  have hcoe : (((⊤ : Subgroup G₁).prod K : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) =
      (univ : Set G₁) ×ˢ (K : Set G₂) := by
    rw [Subgroup.coe_prod, Subgroup.coe_top]
  rw [hcoe]
  exact ⟨isCompact_univ.prod hcompact, isOpen_univ.prod hopen⟩

/-- Transport along a topological group isomorphism.  Pulling back a compact open subgroup along a
continuous group isomorphism gives a compact open subgroup, the preimage of a compact set under a
homeomorphism being compact. -/
theorem isCompact_isOpen_comap {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] (e : G ≃ₜ* H) {K : Subgroup H} (hcompact : IsCompact (K : Set H))
    (hopen : IsOpen (K : Set H)) :
    IsCompact ((K.comap e.toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((K.comap e.toMonoidHom : Subgroup G) : Set G) := by
  have hcoe : ((K.comap e.toMonoidHom : Subgroup G) : Set G) = e.toHomeomorph ⁻¹' (K : Set H) := rfl
  rw [hcoe]
  exact ⟨e.toHomeomorph.isCompact_preimage.mpr hcompact,
    hopen.preimage e.toHomeomorph.continuous⟩

/-- The reduction, abstractly: with a compact first factor, a compact open subgroup of the second
factor already produces one of any group topologically isomorphic to the product. -/
theorem exists_compactOpen_of_prodEquiv {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂]
    [TopologicalSpace G] [TopologicalSpace G₁] [TopologicalSpace G₂] [CompactSpace G₁]
    (e : G ≃ₜ* G₁ × G₂) {K : Subgroup G₂} (hcompact : IsCompact (K : Set G₂))
    (hopen : IsOpen (K : Set G₂)) :
    ∃ K' : Subgroup G, IsCompact (K' : Set G) ∧ IsOpen (K' : Set G) := by
  obtain ⟨hc, ho⟩ := isCompact_isOpen_prod_top (G₁ := G₁) hcompact hopen
  exact ⟨_, isCompact_isOpen_comap e hc ho⟩

/-! ## Why the archimedean factor must be compact -/

/-- The decisive negative.  A connected group with a compact open subgroup is compact: an open
subgroup is closed, hence a nonempty clopen set, and connectedness makes it everything.  So no
connected noncompact group has a compact open subgroup, and the archimedean factor's compactness is
a necessity rather than a convenience. -/
@[to_additive compactSpace_of_connected_of_isCompact_isOpen_addSubgroup]
theorem compactSpace_of_connected_of_isCompact_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [ConnectedSpace G] {K : Subgroup G} (hcompact : IsCompact (K : Set G))
    (hopen : IsOpen (K : Set G)) : CompactSpace G := by
  have hclopen : IsClopen (K : Set G) := ⟨K.isClosed_of_isOpen hopen, hopen⟩
  have huniv : (K : Set G) = univ := hclopen.eq_univ ⟨1, K.one_mem⟩
  rw [huniv] at hcompact
  exact ⟨hcompact⟩

end SMSFormula.AdelicCompactOpen

namespace PositiveDefiniteIntegralLattice

open SMSFormula.AdelicCompactOpen

variable {n : ℕ}

/-- The payoff on the repository's own group: a compact open subgroup of the finite-adelic special
orthogonal group already gives one of the full adelic acting group, because the real factor is a
compact space -- which is where positive definiteness of the lattice's form is consumed.  So the
route's first orbital item is reduced to the finite factor alone. -/
theorem exists_compactOpen_fullAdelicSpecialOrthogonal (L : PositiveDefiniteIntegralLattice n)
    {K : Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup}
    (hcompact : IsCompact (K : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup))
    (hopen : IsOpen (K : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup)) :
    ∃ K' : Subgroup L.ConcreteFullAdelicSpecialOrthogonalGroup,
      IsCompact (K' : Set L.ConcreteFullAdelicSpecialOrthogonalGroup) ∧
        IsOpen (K' : Set L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
  exists_compactOpen_of_prodEquiv L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
    hcompact hopen

end PositiveDefiniteIntegralLattice
