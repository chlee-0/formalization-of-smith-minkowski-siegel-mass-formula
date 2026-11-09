import SMSFormula.AdelicCompactOpenSubgroupReduction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The criterion for the finite-adelic compact open subgroup

`AdelicCompactOpenSubgroupReduction` narrowed the orbital line's first item to the finite factor.
This file supplies the shape that construction has to fill, and removes one of its two conditions
outright.

The integral subgroup.  A continuous monoid map `iota` into a topological monoid and a submonoid `C`
of the target give a subgroup `{g | iota g in C and iota g^-1 in C}` -- the integral points of the
group, with the inverse condition carried separately because a submonoid is not closed under
inversion.  It is open as soon as `C` is, both conditions being preimages of an open set under
continuous maps.

Compactness is then a containment, not a closedness.  An open subgroup is closed, so an open
subgroup contained in any compact subset of the group is compact -- a closed subset of a compact set.
So the construction never has to prove its integral points closed: it only has to put them inside
something compact, which is what compactness of the integral finite adeles supplies.

And the inverse condition is free in the special orthogonal case.  Over a commutative ring a matrix
of determinant one has `A⁻¹ = adjugate A`, and the adjugate's entries are determinants of matrices
whose entries are entries of `A` together with `0` and `1` -- so if the entries of `A` lie in a
subring, so do the entries of `A⁻¹`.  For a group cut out by `det = 1` the two-sided integrality
condition therefore collapses to the one-sided one.

Negative scope.  Nothing is adelic here and no subgroup is constructed: the compact set containing
the integral points is a hypothesis, and it is exactly what the finite-adelic construction still owes.
The determinant hypothesis is `det = 1` and not `det` a unit -- at a unit determinant the inverse
picks up its reciprocal, which need not lie in the subring.
-/

namespace SMSFormula.CompactOpenCriterion

open Matrix

/-! ## Compactness of an open subgroup -/

/-- An open subgroup contained in a compact set is compact.  An open subgroup is closed, and a
closed subset of a compact set is compact -- so the construction owes a containment, never a
closedness. -/
@[to_additive isCompact_of_isOpen_of_subset_addSubgroup]
theorem isCompact_of_isOpen_of_subset {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {K : Subgroup G} (hopen : IsOpen (K : Set G)) {C : Set G}
    (hC : IsCompact C) (hsub : (K : Set G) ⊆ C) : IsCompact (K : Set G) :=
  hC.of_isClosed_subset (K.isClosed_of_isOpen hopen) hsub

/-! ## The integral subgroup of a continuous monoid map -/

/-- The integral points of a continuous monoid map at a submonoid of the target: the inverse
condition is carried separately because a submonoid need not be closed under inversion. -/
def integralSubgroup {G M : Type*} [Group G] [Monoid M] (iota : G →* M) (C : Submonoid M) :
    Subgroup G where
  carrier := {g | iota g ∈ C ∧ iota g⁻¹ ∈ C}
  one_mem' := by simp [C.one_mem]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul]; exact C.mul_mem ha hb
    · rw [_root_.mul_inv_rev, map_mul]; exact C.mul_mem hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

theorem mem_integralSubgroup {G M : Type*} [Group G] [Monoid M] (iota : G →* M) (C : Submonoid M)
    (g : G) : g ∈ integralSubgroup iota C ↔ iota g ∈ C ∧ iota g⁻¹ ∈ C := Iff.rfl

/-- The integral points are open as soon as the target submonoid is: both conditions are preimages
of an open set under continuous maps. -/
theorem isOpen_integralSubgroup {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G]
    [TopologicalSpace M] [IsTopologicalGroup G] (iota : G →* M) (hiota : Continuous iota)
    {C : Submonoid M} (hC : IsOpen (C : Set M)) :
    IsOpen ((integralSubgroup iota C : Subgroup G) : Set G) := by
  have h1 : IsOpen {g : G | iota g ∈ C} := hC.preimage hiota
  have h2 : IsOpen {g : G | iota g⁻¹ ∈ C} := hC.preimage (hiota.comp continuous_inv)
  exact h1.inter h2

/-- The packaged criterion: an open target submonoid and a compact set containing the integral
points give a compact open subgroup. -/
theorem isCompact_isOpen_integralSubgroup {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G]
    [TopologicalSpace M] [IsTopologicalGroup G] (iota : G →* M) (hiota : Continuous iota)
    {C : Submonoid M} (hC : IsOpen (C : Set M)) {S : Set G} (hS : IsCompact S)
    (hsub : ((integralSubgroup iota C : Subgroup G) : Set G) ⊆ S) :
    IsCompact ((integralSubgroup iota C : Subgroup G) : Set G) ∧
      IsOpen ((integralSubgroup iota C : Subgroup G) : Set G) :=
  ⟨isCompact_of_isOpen_of_subset (isOpen_integralSubgroup iota hiota hC) hS hsub,
    isOpen_integralSubgroup iota hiota hC⟩

/-! ## At determinant one the inverse condition is free -/

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A determinant of integral entries is integral: the Leibniz expansion is a signed sum of products
of entries, and a subring is closed under all three operations. -/
theorem det_mem_of_entries_mem (S : Subring R) {A : Matrix ι ι R} (hA : ∀ i j, A i j ∈ S) :
    A.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ ↦ ?_
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ ↦ hA _ _) _

/-- The adjugate of an integral matrix is integral: each entry is the determinant of `A` with one
row replaced by a standard basis vector, whose entries are `0` or `1`. -/
theorem adjugate_mem_of_entries_mem (S : Subring R) {A : Matrix ι ι R} (hA : ∀ i j, A i j ∈ S)
    (i j : ι) : A.adjugate i j ∈ S := by
  rw [Matrix.adjugate_apply]
  refine det_mem_of_entries_mem S fun k l ↦ ?_
  rw [Matrix.updateRow_apply]
  split_ifs with hk
  · rw [Pi.single_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · exact hA k l

/-- At determinant one the inverse is the adjugate, so integrality of the entries passes to the
inverse with no second hypothesis -- which is why the special orthogonal group needs only the
one-sided condition. -/
theorem inv_entries_mem_of_det_one (S : Subring R) {A : Matrix ι ι R} (hA : ∀ i j, A i j ∈ S)
    (hdet : A.det = 1) (i j : ι) : A⁻¹ i j ∈ S := by
  have hinv : A⁻¹ = A.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [hinv]
  exact adjugate_mem_of_entries_mem S hA i j

end SMSFormula.CompactOpenCriterion
