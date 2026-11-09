import SMSFormula.BinaryBadDensityProduct

/-!
# The actual finite binary genus norm image

The represented-unit Picard maps are assembled over the original Bad set.
Support off the primitive discriminant identifies this finite map's kernel
with class squares. Its actual image has cardinality #H[2]. The assertion
that this image has index two remains a separate quantitative genus task.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The actual local quotient at one original bad prime. -/
abbrev BinaryBadNormQuotient (K : PositiveDefiniteIntegralLattice 2)
    (p : ↥(massBadPrimeSet K)) :=
  letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
  OrderUnitNormQuotient ℤ_[p.val.val] K.binaryPrimitiveDiscriminant

/-- The literal finite product, including content-only bad primes. -/
abbrev BinaryBadNormProduct (K : PositiveDefiniteIntegralLattice 2) :=
  (p : ↥(massBadPrimeSet K)) → K.BinaryBadNormQuotient p

/-- Each factor is the existing finite p-adic order-unit norm quotient. -/
theorem finite_binaryBadNormQuotient (K : PositiveDefiniteIntegralLattice 2)
    (p : ↥(massBadPrimeSet K)) : Finite (K.BinaryBadNormQuotient p) := by
  letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
  exact finite_orderUnitNormQuotient p.val.val K.binaryPrimitiveDiscriminant

theorem finite_binaryBadNormProduct (K : PositiveDefiniteIntegralLattice 2) :
    Finite K.BinaryBadNormProduct := by
  letI (p : ↥(massBadPrimeSet K)) := K.finite_binaryBadNormQuotient p
  infer_instance

/-- The product carrier has exactly the original norm-index product size. -/
theorem card_binaryBadNormProduct (K : PositiveDefiniteIntegralLattice 2) :
    Nat.card K.BinaryBadNormProduct=K.binaryLocalNormIndexProduct := by
  classical
  rw [binaryLocalNormIndexProduct, Nat.card_pi]
  exact Finset.prod_coe_sort (massBadPrimeSet K) (fun p =>
    letI : Fact p.val.Prime := ⟨p.prop⟩
    Nat.card (OrderUnitNormQuotient ℤ_[p.val] K.binaryPrimitiveDiscriminant))

/-- The native represented-unit Picard maps on the original finite product. -/
def binaryBadLocalNormHom (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      K.BinaryBadNormProduct := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact {
    toFun := fun xi p =>
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      K.binaryIdealLocalNormHom p.val.val xi
    map_one' := by
      funext p
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      exact map_one (K.binaryIdealLocalNormHom p.val.val)
    map_mul' := fun xi eta => by
      funext p
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      exact map_mul (K.binaryIdealLocalNormHom p.val.val) xi eta }

/-- Evaluate a coordinate on the literal represented unit of an actual
same-content, same-discriminant lattice. -/
theorem binaryBadLocalNormHom_apply (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ↥(massBadPrimeSet K)) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    ∀ (v : Fin 2 → ℤ_[p.val.val]) (u : ℤ_[p.val.val]ˣ),
      L.binaryPrimitivePolynomialOver ℤ_[p.val.val] v=(u : ℤ_[p.val.val]) →
      K.binaryBadLocalNormHom (L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD) p=
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
  exact K.binaryIdealLocalNormHom_apply L hg hD p.val.val

/-- Every omitted prime has trivial quotient; restriction loses no kernel
condition. No set of primes is substituted for original Bad. -/
theorem binaryBadLocalNormHom_ker (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormHom.ker=K.binaryIdealLocalNormKernel := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  ext xi
  constructor
  · intro hx p hp
    by_cases hmem : (⟨p, hp.out⟩ : {p : ℕ // p.Prime})∈massBadPrimeSet K
    · exact congrFun hx ⟨⟨p,hp.out⟩,hmem⟩
    · have hnot : ¬(p : ℤ)∣K.binaryPrimitiveDiscriminant := by
        intro hd
        apply hmem
        apply K.binary_mem_bad_of_dvd_primitive
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
      have hc := card_orderUnitNormQuotient_eq_one_of_not_dvd p
        K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four hnot
      letI := (Nat.card_eq_one_iff_unique.mp hc).1
      exact Subsingleton.elim _ _
  · intro hx
    funext p
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    exact hx p.val.val

/-- The actual finite map has precisely the existing class-square kernel. -/
theorem binaryBadLocalNormHom_ker_eq_squares (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormHom.ker=
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.binaryBadLocalNormHom_ker,K.binaryIdealLocalNormKernel_eq_squares]

/-- The actual subgroup represented by native Picard classes. -/
def binaryBadLocalNormImage (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Subgroup K.BinaryBadNormProduct := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact MonoidHom.range (G := ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (N := K.BinaryBadNormProduct) K.binaryBadLocalNormHom

private theorem card_normImage (G A : Type*) [Group G] [Group A] (f : G →* A) :
    Nat.card (MonoidHom.range f)=Nat.card (G ⧸ f.ker) :=
  (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm

/-- The actual represented-unit image has cardinality #H[2]. Its index
is not determined by the principal-genus kernel theorem alone. -/
theorem card_binaryBadLocalNormImage (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card K.binaryBadLocalNormImage=
      Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker := by
  letI := K.binaryDiscriminantOrder_isDomain
  let G := ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)
  let f : G →* K.BinaryBadNormProduct := K.binaryBadLocalNormHom
  have he := card_normImage G K.BinaryBadNormProduct f
  have hq := congrArg (fun S : Subgroup G => Nat.card (G ⧸ S))
    K.binaryBadLocalNormHom_ker_eq_squares
  exact he.trans (hq.trans K.binaryClassSquareQuotient_card_eq_twoTorsion)

/-- The original product splits into the actual image size and its index.
The missing quantitative statement is that this literal index equals two. -/
theorem binaryLocalNormIndexProduct_eq_imageIndex_mul_twoTorsion
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryLocalNormIndexProduct=K.binaryBadLocalNormImage.index *
      Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker := by
  letI := K.binaryDiscriminantOrder_isDomain
  calc
    K.binaryLocalNormIndexProduct=Nat.card K.BinaryBadNormProduct :=
      K.card_binaryBadNormProduct.symm
    _=Nat.card K.binaryBadLocalNormImage*K.binaryBadLocalNormImage.index :=
      K.binaryBadLocalNormImage.card_mul_index.symm
    _=K.binaryBadLocalNormImage.index*Nat.card K.binaryBadLocalNormImage := mul_comm _ _
    _=_ := congrArg (K.binaryBadLocalNormImage.index * ·) K.card_binaryBadLocalNormImage

/-- The full same-K/same-positive-P mass formula is equivalent to the
local norm image having index two. This does not assert that index. -/
theorem binaryMassFormula_iff_localNormImage_index_two (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    (∃ P : ℝ, 0<P ∧ massLocalInverseProductTendsTo K P ∧
      ((ordinaryGenusMass K : ℚ) : ℝ)=archimedeanMassFactor 2*P) ↔
      K.binaryBadLocalNormImage.index=2 := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.finite_binaryClassGroup
  rw [K.binaryMassFormula_iff_normIndexProduct_eq_twoTorsion,
    K.binaryLocalNormIndexProduct_eq_imageIndex_mul_twoTorsion]
  exact mul_left_inj' (Nat.card_pos.ne' :
    Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker≠0)

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryBadNormQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryBadNormProduct
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryBadNormProduct
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormHom
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormHom_ker
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormHom_ker_eq_squares
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormImage
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryBadLocalNormImage
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormIndexProduct_eq_imageIndex_mul_twoTorsion
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryMassFormula_iff_localNormImage_index_two
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormHom_apply
