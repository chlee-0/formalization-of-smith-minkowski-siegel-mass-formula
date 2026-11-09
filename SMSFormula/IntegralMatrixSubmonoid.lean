import SMSFormula.IntegralPointsGraphCompactness

/-!
# The integral matrices are a compact open submonoid

`FiniteAdelicCompactOpenCriterion` and `IntegralPointsGraphCompactness` reduced the orbital line's
subgroup item to three hypotheses on the finite-adelic group: the entry map, the integral matrices
as a compact open submonoid, and the pair map as a closed embedding.  This file discharges the
second of those, and discharges it on the repository's own object.

Abstractly.  Over a topological ring, the matrices with all entries in a subring form a submonoid --
the identity's entries are `0` and `1`, and a product entry is a finite sum of products, so all three
closure properties of a subring are used and nothing else.  That submonoid is the square Pi-set of
the subring's carrier, so it is compact when the subring is compact and open when the subring is
open, the index being finite in both directions.

Concretely.  The repository already proves the everywhere-integral finite adeles compact and open in
the finite adele ring, so the integral matrices over them are a compact open submonoid with no
further input -- the second hypothesis is discharged on the actual target.

Negative scope.  This is the target submonoid alone.  The entry map out of the finite-adelic special
orthogonal group and the closed embedding of the pair map are untouched, so no subgroup is produced
here; and openness genuinely needs the finite index, an infinite product of proper open sets not
being open.
-/

namespace SMSFormula.CompactOpenCriterion

open Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The submonoid of integral matrices -/

/-- The matrices with entries in a subring form a submonoid: the identity's entries are `0` and `1`,
and a product entry is a finite sum of products. -/
def matrixSubmonoid (S : Subring R) : Submonoid (Matrix ι ι R) where
  carrier := {A | ∀ i j, A i j ∈ S}
  one_mem' := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  mul_mem' := by
    intro A B hA hB i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ ↦ S.mul_mem (hA i k) (hB k j)

theorem mem_matrixSubmonoid (S : Subring R) (A : Matrix ι ι R) :
    A ∈ matrixSubmonoid (ι := ι) S ↔ ∀ i j, A i j ∈ S := Iff.rfl

/-- The carrier is the square pi-set of the subring's carrier, which is what makes both topological
statements a product computation. -/
theorem coe_matrixSubmonoid (S : Subring R) :
    ((matrixSubmonoid (ι := ι) S : Submonoid (Matrix ι ι R)) : Set (Matrix ι ι R)) =
      Set.univ.pi fun _ : ι ↦ Set.univ.pi fun _ : ι ↦ (S : Set R) :=
  Set.ext fun _ ↦
    ⟨fun h i _ j _ ↦ h i j, fun h i j ↦ h i (Set.mem_univ i) j (Set.mem_univ j)⟩

/-- Compactness, from compactness of the subring in both directions of the finite index. -/
theorem isCompact_matrixSubmonoid [TopologicalSpace R] {S : Subring R}
    (hS : IsCompact (S : Set R)) :
    IsCompact ((matrixSubmonoid (ι := ι) S : Submonoid (Matrix ι ι R)) : Set (Matrix ι ι R)) := by
  rw [coe_matrixSubmonoid]
  exact isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ hS

/-- Openness, where the finite index is what is consumed: an infinite product of proper open sets is
not open. -/
theorem isOpen_matrixSubmonoid [TopologicalSpace R] {S : Subring R} (hS : IsOpen (S : Set R)) :
    IsOpen ((matrixSubmonoid (ι := ι) S : Submonoid (Matrix ι ι R)) : Set (Matrix ι ι R)) := by
  rw [coe_matrixSubmonoid]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_set_pi Set.finite_univ fun _ _ ↦ hS

/-- The second hypothesis, abstractly: over a compact open subring the integral matrices are a
compact open submonoid. -/
theorem isCompact_isOpen_matrixSubmonoid [TopologicalSpace R] {S : Subring R}
    (hcompact : IsCompact (S : Set R)) (hopen : IsOpen (S : Set R)) :
    IsCompact ((matrixSubmonoid (ι := ι) S : Submonoid (Matrix ι ι R)) : Set (Matrix ι ι R)) ∧
      IsOpen ((matrixSubmonoid (ι := ι) S : Submonoid (Matrix ι ι R)) : Set (Matrix ι ι R)) :=
  ⟨isCompact_matrixSubmonoid hcompact, isOpen_matrixSubmonoid hopen⟩

end SMSFormula.CompactOpenCriterion

namespace PositiveDefiniteIntegralLattice

open SMSFormula.CompactOpenCriterion

/-- The second hypothesis on the repository's own object: the everywhere-integral finite adeles are
compact and open, so the integral finite-adelic matrices are a compact open submonoid, with no
further input. -/
theorem isCompact_isOpen_integralFiniteAdeleMatrixSubmonoid (n : ℕ) :
    IsCompact ((matrixSubmonoid (ι := Fin n) integralFiniteAdeleSubring :
        Submonoid (Matrix (Fin n) (Fin n) RationalFiniteAdele)) :
        Set (Matrix (Fin n) (Fin n) RationalFiniteAdele)) ∧
      IsOpen ((matrixSubmonoid (ι := Fin n) integralFiniteAdeleSubring :
        Submonoid (Matrix (Fin n) (Fin n) RationalFiniteAdele)) :
        Set (Matrix (Fin n) (Fin n) RationalFiniteAdele)) :=
  isCompact_isOpen_matrixSubmonoid isCompact_integralFiniteAdeleSubring
    isOpen_integralFiniteAdeleSubring

end PositiveDefiniteIntegralLattice
