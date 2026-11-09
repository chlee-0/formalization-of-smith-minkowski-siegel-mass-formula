import SMSFormula.BinaryIdealPatch

/-!
# Principal genus for the actual binary quadratic order

The original finite-place norm kernel is exactly the subgroup of squares
in the canonical arbitrary-order class group. The proof uses the actual
invertible ideal patch, the original conjugation and actual class realization.
-/

open scoped nonZeroDivisors

/-- A principal fractional-ideal unit has trivial class over any domain. -/
theorem ClassGroup.mk_toPrincipalIdeal_eq_one {R : Type*} [CommRing R] [IsDomain R]
    (x : (FractionRing R)ˣ) :
    ClassGroup.mk (FractionRing R) (toPrincipalIdeal R (FractionRing R) x)=1 := by
  rw [← (ClassGroup.mk (FractionRing R)).map_one]
  apply ClassGroup.mk_eq_mk.mpr
  refine ⟨x⁻¹,?_⟩
  rw [← map_mul,mul_inv_cancel,map_one]

namespace BinaryNormIdeal

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The actual fractional-ideal conjugation preserves the principal unit
with the actual conjugated field generator. -/
lemma fractionalConjugation_toPrincipalIdeal
    (x : (FractionRing (CoefficientOrder a b c))ˣ) :
    Units.map (fractionalConjugation a b c).toMonoidHom
        (toPrincipalIdeal (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c)) x)=
      toPrincipalIdeal (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))
        (Units.map (fractionConjugation a b c).toMonoidHom x) := by
  apply Units.ext
  change fractionalConjugation a b c
      (toPrincipalIdeal (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c)) x).val=_
  rw [coe_toPrincipalIdeal,coe_toPrincipalIdeal]
  exact fractionalConjugation_spanSingleton a b c x.val

/-- Equal actual classes have equal conjugated actual classes. This uses
the principal-scaling quotient and does not require a maximal order. -/
lemma mk_fractionalConjugation_eq_of_mk_eq
    (I J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ)
    (h : ClassGroup.mk (FractionRing (CoefficientOrder a b c)) I=
      ClassGroup.mk (FractionRing (CoefficientOrder a b c)) J) :
    ClassGroup.mk (FractionRing (CoefficientOrder a b c))
        (Units.map (fractionalConjugation a b c).toMonoidHom I)=
      ClassGroup.mk (FractionRing (CoefficientOrder a b c))
        (Units.map (fractionalConjugation a b c).toMonoidHom J) := by
  obtain ⟨x,hx⟩ := ClassGroup.mk_eq_mk.mp h
  apply ClassGroup.mk_eq_mk.mpr
  refine ⟨Units.map (fractionConjugation a b c).toMonoidHom x,?_⟩
  have hh := congrArg (Units.map (fractionalConjugation a b c).toMonoidHom) hx
  rw [map_mul,fractionalConjugation_toPrincipalIdeal] at hh
  exact hh

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- Conjugation sends the class of any actual invertible fractional ideal
to its inverse. Actual fixed-(g,D) realization reduces this to the proved
conjugate norm-ideal scale identity. -/
theorem binaryClassGroup_mk_fractionalConjugation (K : PositiveDefiniteIntegralLattice 2)
    (J : K.BinaryDiscriminantFractionalIdealsˣ) :
    letI := K.binaryDiscriminantOrder_isDomain
    ClassGroup.mk (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
        (Units.map (fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)).toMonoidHom J)=
      (ClassGroup.mk (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) J)⁻¹ := by
  letI := K.binaryDiscriminantOrder_isDomain
  let mk := ClassGroup.mk (R := DiscriminantOrder K.binaryPrimitiveDiscriminant)
    (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
  let conj := Units.map (fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)).toMonoidHom
  obtain ⟨L,hg,hD,hclass⟩ := K.exists_lattice_of_binaryIdealClass (mk J)
  let I := L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD
  have hI : mk I=mk J := hclass
  have hconj : mk (conj I)=mk (conj J) :=
    mk_fractionalConjugation_eq_of_mk_eq _ _ _ I J hI
  let gamma : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ :=
    Units.mk0 ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) :
      FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
      (by exact_mod_cast (ne_of_gt L.binaryPrimitivePolynomial_leading_pos))
  have hprod : I*conj I=toPrincipalIdeal (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) gamma := by
    apply Units.ext
    rw [Units.val_mul,coe_toPrincipalIdeal]
    exact binaryFractionalNormIdealUnitAt_mul_fractionalConjugation L _ hD
  have hm : mk I*mk (conj I)=1 := by
    rw [← map_mul,hprod]
    exact ClassGroup.mk_toPrincipalIdeal_eq_one gamma
  change mk (conj J)=(mk J)⁻¹
  rw [← hconj,← hI]
  apply (mul_left_cancel (a := mk I))
  rw [hm,mul_inv_cancel]

/-- Every actual finite-place kernel class is a square in the original
arbitrary-order class group. No caller patch or class-number premise occurs. -/
theorem exists_square_of_mem_binaryIdealLocalNormKernel (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (hxi : letI := K.binaryDiscriminantOrder_isDomain
      xi ∈ K.binaryIdealLocalNormKernel) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ eta : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant), eta*eta=xi := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨L,hg,hD,hclass,beta,hb,J,hprod⟩ := K.exists_binaryKernelClass_global_patch xi hxi
  let mk := ClassGroup.mk (R := DiscriminantOrder K.binaryPrimitiveDiscriminant)
    (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
  have hclass' : mk (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD)=xi := hclass
  have hh := congrArg mk hprod
  rw [map_mul,map_mul,hclass',K.binaryClassGroup_mk_fractionalConjugation J,
    ClassGroup.mk_toPrincipalIdeal_eq_one,one_mul] at hh
  refine ⟨mk J,?_⟩
  calc
    mk J*mk J=(xi*(mk J)⁻¹)*mk J := by rw [hh]
    _=xi := by simp only [mul_assoc,inv_mul_cancel,mul_one]

/-- The original simultaneous norm kernel is exactly the actual class
square set, including dyadic and conductor order-unit conditions. -/
theorem mem_binaryIdealLocalNormKernel_iff_square (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    xi ∈ K.binaryIdealLocalNormKernel ↔
      ∃ eta : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant), eta*eta=xi := by
  letI := K.binaryDiscriminantOrder_isDomain
  constructor
  · exact K.exists_square_of_mem_binaryIdealLocalNormKernel xi
  · rintro ⟨eta,rfl⟩
    exact K.square_mem_binaryIdealLocalNormKernel eta

/-- Equality with the canonical square-homomorphism range in Mathlib. -/
theorem binaryIdealLocalNormKernel_eq_squares (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryIdealLocalNormKernel=
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range := by
  letI := K.binaryDiscriminantOrder_isDomain
  ext xi
  rw [K.mem_binaryIdealLocalNormKernel_iff_square]
  simp only [MonoidHom.mem_range,powMonoidHom_apply,pow_two]

/-- At the original fixed content and discriminant, the original genus
is exactly the actual class-square coset. No real-place certificate remains. -/
theorem isSameGenus_iff_binaryIdealClass_square (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.IsSameGenus L ↔ ∃ eta : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant),
      eta*eta=L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD*
        (K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.isSameGenus_iff_binaryIdealLocalNormKernel_mem L hg hD,
    K.mem_binaryIdealLocalNormKernel_iff_square]

/-- The image of the original proper genus is the full actual square coset. -/
theorem binaryProperGenusIdealClass_range_eq_squareCoset (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Set.range K.binaryProperGenusIdealClass=
      {xi | xi*(K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ ∈
        (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range} := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.binaryProperGenusIdealClass_range_eq_kernelCoset]
  change {xi | xi*(K.binaryIdealClassAt K.binaryPrimitiveDiscriminant rfl)⁻¹ ∈
    K.binaryIdealLocalNormKernel}=_
  rw [K.binaryIdealLocalNormKernel_eq_squares]

/-- The original proper-genus carrier is equivalent to the actual square
subgroup, using the already verified kernel translation. -/
noncomputable def binaryProperGenusSquareEquiv (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.properGenus ≃
      (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact K.binaryIdealLocalNormKernel_eq_squares ▸ K.binaryProperGenusKernelEquiv

/-- The square-subgroup count is the original proper-genus count. -/
theorem card_binaryIdealClassSquares (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range=Fintype.card K.properGenus := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [← K.binaryIdealLocalNormKernel_eq_squares]
  exact K.card_binaryIdealLocalNormKernel

/-- The original ordinary full-O mass is the actual square-subgroup count
 divided by 2*w_D. This reuses the aggregate proper/full comparison and is
 not a density/product mass formula. -/
theorem ordinaryGenusMass_eq_card_binaryIdealClassSquares_div_two_normOneUnits
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.ordinaryGenusMass=
      (Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).range : ℚ)/
        (2*(Nat.card (DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [← K.binaryIdealLocalNormKernel_eq_squares]
  exact K.ordinaryGenusMass_eq_card_binaryIdealLocalNormKernel_div_two_normOneUnits

end PositiveDefiniteIntegralLattice

#assert_standard_axioms ClassGroup.mk_toPrincipalIdeal_eq_one
#assert_standard_axioms BinaryNormIdeal.fractionalConjugation_toPrincipalIdeal
#assert_standard_axioms BinaryNormIdeal.mk_fractionalConjugation_eq_of_mk_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryClassGroup_mk_fractionalConjugation
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_square_of_mem_binaryIdealLocalNormKernel
#assert_standard_axioms PositiveDefiniteIntegralLattice.mem_binaryIdealLocalNormKernel_iff_square
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealLocalNormKernel_eq_squares
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryIdealClass_square
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusIdealClass_range_eq_squareCoset
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusSquareEquiv
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryIdealClassSquares
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_card_binaryIdealClassSquares_div_two_normOneUnits
