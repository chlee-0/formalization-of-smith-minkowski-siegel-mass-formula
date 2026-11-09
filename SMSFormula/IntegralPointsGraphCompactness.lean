import SMSFormula.FiniteAdelicCompactOpenCriterion

/-!
# The integral points are compact by the graph of the inverse

`FiniteAdelicCompactOpenCriterion` left the finite-adelic construction three hypotheses: the entry
map, the integral matrices as an open submonoid, and a compact set containing the integral points.
The third is the awkward one, because it asks for a compact set inside the group while what the
integral adeles supply is a compact set of matrices.  This file closes that gap structurally.

The graph.  A matrix group carries the topology of the pair `g |-> (g, g^-1)`, and the integral
points are exactly the preimage of `C x C` under that pair map.  If the pair map is a topological
embedding with closed range then the preimage of a compact square is compact: its image is the
range met with that square, closed inside a compact set, and an embedding reflects compactness.
So the containment hypothesis is replaced by a structural property of the group's own topology.

And the candidate for that range is already closed.  In a Hausdorff topological monoid the set of
pairs `(A, B)` with `A B = 1` and `B A = 1` is closed -- the preimage of the point `(1,1)` under a
continuous map.  So the closed-range hypothesis is not an extra analytic condition: what the
concrete construction owes is that the pair map's range is that set, an algebraic identification,
and not a topological estimate.  Nothing here proves that identification.

Negative scope.  Being inside a compact set is not compactness -- the open unit interval sits inside
the closed one -- which is exactly why closedness, of the range here or of the subgroup in the
earlier criterion, cannot be dropped.  Nothing is adelic: the embedding is a hypothesis about the
group's topology, and no matrix group is exhibited.
-/

namespace SMSFormula.CompactOpenCriterion

open Set

/-! ## The graph of the inverse is closed -/

/-- In a Hausdorff topological monoid the inversion graph is closed: it is the preimage of the
single point `(1,1)` under the continuous map `(A,B) |-> (A B, B A)`. -/
theorem isClosed_inverseGraph (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [T2Space M] : IsClosed {p : M × M | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} := by
  have hcont : Continuous fun p : M × M ↦ (p.1 * p.2, p.2 * p.1) :=
    (continuous_fst.mul continuous_snd).prodMk (continuous_snd.mul continuous_fst)
  have hpre : {p : M × M | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} =
      (fun p : M × M ↦ (p.1 * p.2, p.2 * p.1)) ⁻¹' {((1 : M), (1 : M))} := by
    ext p
    simp [Prod.ext_iff]
  rw [hpre]
  exact (isClosed_singleton).preimage hcont

/-! ## Compactness from a closed graph embedding -/

/-- The preimage of a compact square under a closed embedding is compact.  The image is the range
met with the square -- closed inside a compact set, hence compact -- and an embedding reflects
compactness. -/
theorem isCompact_preimage_prod_of_isClosed_range {G X : Type*} [TopologicalSpace G]
    [TopologicalSpace X] [T2Space X] {e : G → X × X} (hemb : Topology.IsEmbedding e)
    (hrange : IsClosed (Set.range e)) {C : Set X} (hC : IsCompact C) :
    IsCompact (e ⁻¹' (C ×ˢ C)) := by
  have hCclosed : IsClosed C := hC.isClosed
  have hsq : IsCompact (C ×ˢ C) := hC.prod hC
  have himage : e '' (e ⁻¹' (C ×ˢ C)) = Set.range e ∩ (C ×ˢ C) := by
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  have hclosed : IsClosed (Set.range e ∩ (C ×ˢ C)) :=
    hrange.inter (hCclosed.prod hCclosed)
  have : IsCompact (e '' (e ⁻¹' (C ×ˢ C))) := by
    rw [himage]
    exact hsq.of_isClosed_subset hclosed Set.inter_subset_right
  exact hemb.isCompact_iff.mpr this

/-- The integral points are compact, with the containment hypothesis replaced by a property of the
group's own topology: the pair map onto a matrix and its inverse is a closed embedding. -/
theorem isCompact_integralSubgroup_of_closedGraph {G M : Type*} [Group G] [Monoid M]
    [TopologicalSpace G] [TopologicalSpace M] [T2Space M] (iota : G →* M)
    (hemb : Topology.IsEmbedding fun g : G ↦ (iota g, iota g⁻¹))
    (hrange : IsClosed (Set.range fun g : G ↦ (iota g, iota g⁻¹)))
    {C : Submonoid M} (hC : IsCompact (C : Set M)) :
    IsCompact ((integralSubgroup iota C : Subgroup G) : Set G) := by
  have hset : ((integralSubgroup iota C : Subgroup G) : Set G) =
      (fun g : G ↦ (iota g, iota g⁻¹)) ⁻¹' ((C : Set M) ×ˢ (C : Set M)) := rfl
  rw [hset]
  exact isCompact_preimage_prod_of_isClosed_range hemb hrange hC

/-- The packaged criterion, with no containment left: a continuous monoid map whose inversion pair
is a closed embedding, together with a submonoid that is compact and open, gives a compact open
subgroup. -/
theorem isCompact_isOpen_integralSubgroup_of_closedGraph {G M : Type*} [Group G] [Monoid M]
    [TopologicalSpace G] [TopologicalSpace M] [T2Space M] [IsTopologicalGroup G] (iota : G →* M)
    (hiota : Continuous iota) (hemb : Topology.IsEmbedding fun g : G ↦ (iota g, iota g⁻¹))
    (hrange : IsClosed (Set.range fun g : G ↦ (iota g, iota g⁻¹)))
    {C : Submonoid M} (hCcompact : IsCompact (C : Set M)) (hCopen : IsOpen (C : Set M)) :
    IsCompact ((integralSubgroup iota C : Subgroup G) : Set G) ∧
      IsOpen ((integralSubgroup iota C : Subgroup G) : Set G) :=
  ⟨isCompact_integralSubgroup_of_closedGraph iota hemb hrange hCcompact,
    isOpen_integralSubgroup iota hiota hCopen⟩

end SMSFormula.CompactOpenCriterion
