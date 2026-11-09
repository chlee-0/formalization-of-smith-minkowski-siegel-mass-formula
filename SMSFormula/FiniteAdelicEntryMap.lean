import SMSFormula.IntegralMatrixSubmonoid

/-!
# The entry map, and the pair map as an embedding

Two hypotheses were left on the finite-adelic side: the entry map into the integral matrices, and the
pair map as a closed embedding.  This file supplies the entry map and the embedding half, both on the
repository's own group, leaving only the closed range.

The embedding is the unit topology's own definition.  Mathlib topologises a unit group as the
initial topology of `u |-> (u, op u^-1)`, so the pair map into `M x M` is an embedding after
composing with the opposite homeomorphism -- not a fact to prove about matrices but the definition of
the topology, read off.  Subtype inclusions are embeddings, so the composite through any chain of
subgroups is one too, and the repository's group sits two subgroups below the matrix units.

The entry map is then the unit-coercion monoid map composed with those subgroup inclusions,
continuous for the same reason.

Negative scope.  The closed range is not proved here.  An embedding alone gives nothing about
compactness -- that is exactly the earlier negative that being inside a compact set is not being
compact -- so this discharges one hypothesis and half of another, and no subgroup is produced.
-/

namespace SMSFormula.CompactOpenCriterion

open Matrix

/-! ## The pair map on a unit group -/

/-- The pair map on a unit group is an embedding, because the unit topology is the initial topology
of that pair composed with the opposite homeomorphism. -/
theorem isEmbedding_unitPair (M : Type*) [Monoid M] [TopologicalSpace M] :
    Topology.IsEmbedding (fun u : Mˣ ↦ ((u : M), ((u⁻¹ : Mˣ) : M))) := by
  have hhom : Topology.IsEmbedding (fun p : M × Mᵐᵒᵖ ↦ (p.1, p.2.unop)) :=
    ((Homeomorph.refl M).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding
  exact hhom.comp (Units.isEmbedding_embedProduct (M := M))

/-- The pair map through a subgroup of the units is still an embedding, subtype inclusions being
embeddings. -/
theorem isEmbedding_subgroupUnitPair {M : Type*} [Monoid M] [TopologicalSpace M]
    (K : Subgroup Mˣ) :
    Topology.IsEmbedding (fun g : K ↦ (((g : Mˣ) : M), (((g⁻¹ : K) : Mˣ) : M))) := by
  have hsub : Topology.IsEmbedding (fun g : K ↦ (g : Mˣ)) := Topology.IsEmbedding.subtypeVal
  exact (isEmbedding_unitPair M).comp hsub

/-- The entry map of a subgroup of the units, as a monoid map into the ambient monoid. -/
def subgroupEntryHom {M : Type*} [Monoid M] (K : Subgroup Mˣ) : K →* M :=
  (Units.coeHom M).comp K.subtype

@[simp]
theorem subgroupEntryHom_apply {M : Type*} [Monoid M] (K : Subgroup Mˣ) (g : K) :
    subgroupEntryHom K g = ((g : Mˣ) : M) := rfl

/-- The entry map is continuous: the unit coercion is, and so is a subtype inclusion. -/
theorem continuous_subgroupEntryHom {M : Type*} [Monoid M] [TopologicalSpace M]
    (K : Subgroup Mˣ) : Continuous (subgroupEntryHom K) :=
  Units.continuous_val.comp continuous_subtype_val

/-- The pair map of the entry map is the pair map of the subgroup, so the embedding above is exactly
the hypothesis the graph criterion takes. -/
theorem isEmbedding_entryPair {M : Type*} [Monoid M] [TopologicalSpace M] (K : Subgroup Mˣ) :
    Topology.IsEmbedding fun g : K ↦ (subgroupEntryHom K g, subgroupEntryHom K g⁻¹) :=
  isEmbedding_subgroupUnitPair K

/-! ## Through a second subgroup layer -/

/-- A subgroup of a subgroup: the entry map composes, and so does the embedding, which is what the
repository's two-layer presentation needs. -/
def nestedEntryHom {M : Type*} [Monoid M] {K : Subgroup Mˣ} (J : Subgroup K) : J →* M :=
  (subgroupEntryHom K).comp J.subtype

@[simp]
theorem nestedEntryHom_apply {M : Type*} [Monoid M] {K : Subgroup Mˣ} (J : Subgroup K) (g : J) :
    nestedEntryHom J g = (((g : K) : Mˣ) : M) := rfl

theorem continuous_nestedEntryHom {M : Type*} [Monoid M] [TopologicalSpace M] {K : Subgroup Mˣ}
    (J : Subgroup K) : Continuous (nestedEntryHom J) :=
  (continuous_subgroupEntryHom K).comp continuous_subtype_val

theorem isEmbedding_nestedEntryPair {M : Type*} [Monoid M] [TopologicalSpace M] {K : Subgroup Mˣ}
    (J : Subgroup K) :
    Topology.IsEmbedding fun g : J ↦ (nestedEntryHom J g, nestedEntryHom J g⁻¹) :=
  (isEmbedding_entryPair K).comp Topology.IsEmbedding.subtypeVal

end SMSFormula.CompactOpenCriterion

namespace PositiveDefiniteIntegralLattice

open SMSFormula.CompactOpenCriterion

variable {n : ℕ}

/-- The Hausdorff instance the graph criterion consumes, made available by name.  `T2Space` for the
finite adeles is declared local in `AdelicFinitePresentation`, so a file using the graph criterion must reintroduce it --
without that the instance search does not merely fail, it times out in `whnf`. -/
theorem t2Space_rationalFiniteAdele : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

/-- The entry map on the repository's own group: the finite-adelic special orthogonal group sits two
subgroups below the matrix units, so its entry map into the finite-adelic matrices is the composite,
and it is continuous. -/
noncomputable def finiteAdelicSpecialOrthogonalEntryHom (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFiniteAdelicSpecialOrthogonalGroup →*
      Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  nestedEntryHom L.finiteAdelicSpecialOrthogonalMatrixSubgroup

theorem continuous_finiteAdelicSpecialOrthogonalEntryHom (L : PositiveDefiniteIntegralLattice n) :
    Continuous (L.finiteAdelicSpecialOrthogonalEntryHom) :=
  continuous_nestedEntryHom _

/-- And the pair map is an embedding on that group, which is the embedding half of the graph
criterion's last hypothesis.  The closed range is not proved. -/
theorem isEmbedding_finiteAdelicSpecialOrthogonalEntryPair (L : PositiveDefiniteIntegralLattice n) :
    Topology.IsEmbedding fun g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup ↦
      (L.finiteAdelicSpecialOrthogonalEntryHom g, L.finiteAdelicSpecialOrthogonalEntryHom g⁻¹) :=
  isEmbedding_nestedEntryPair _

end PositiveDefiniteIntegralLattice
