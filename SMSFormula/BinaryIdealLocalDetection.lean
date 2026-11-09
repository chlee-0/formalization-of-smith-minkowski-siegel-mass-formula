import SMSFormula.BinaryIdealLocalFactors

/-!
# Local detection for the original binary fractional ideals

Order membership is detected by all actual integral p-adic coefficient
orders. Multiplication by an existing fractional inverse then detects
membership and equality of invertible fractional ideals. No maximal-order
or field premise on the quadratic local algebra is used.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

/-- A rational number integral in every genuine Q_p is an integer. The
actual integer denominator is a unit in every Z_p, so has no prime divisor. -/
theorem exists_int_of_forall_padic_integral (q : ℚ)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)], ∃ z : ℤ_[p], (z : ℚ_[p])=(q : ℚ_[p])) :
    ∃ n : ℤ, (n : ℚ)=q := by
  have hd : q.den=1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hdiv
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨z,hz⟩ := h p
    have hnorm : ‖(q : ℚ_[p])‖ ≤ 1 := hz ▸ z.property
    have hu := PadicInt.isUnit_den q hnorm
    have hlt : ‖(q.den : ℤ_[p])‖<1 := PadicInt.norm_natCast_lt_one_iff.mpr hdiv
    rw [PadicInt.isUnit_iff.mp hu] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  exact ⟨q.num,Rat.coe_int_num_of_den_eq_one hd⟩

/-- Membership in the original order is detected by preimages in the
Actual integral p-adic coefficient orders, including at2 and conductor primes. -/
theorem exists_order_preimage_iff_forall_padic (a b c : ℤ)
    [IsDomain (CoefficientOrder a b c)] (hD : b^2-4*a*c<0)
    (z : FractionRing (CoefficientOrder a b c)) :
    (∃ w : CoefficientOrder a b c, algebraMap _ _ w=z) ↔
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        ∃ w : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]),
          coefficientScalarMap a b c (algebraMap ℤ_[p] ℚ_[p]) w=
            fractionScalarMap a b c hD ℚ_[p] z := by
  constructor
  · rintro ⟨w,rfl⟩ p hp
    refine ⟨orderScalarMap a b c ℤ_[p] w,?_⟩
    rw [fractionScalarMap_algebraMap]
    apply QuadraticAlgebra.ext <;> simp [orderScalarMap,coefficientScalarMap]
  · intro h
    have hre : ∀ (p : ℕ) [Fact (Nat.Prime p)], ∃ s : ℤ_[p],
        (s : ℚ_[p])=((fractionRationalMap a b c hD z).re : ℚ_[p]) := by
      intro p hp
      obtain ⟨w,hw⟩ := h p
      exact ⟨w.re,congrArg QuadraticAlgebra.re hw⟩
    have him : ∀ (p : ℕ) [Fact (Nat.Prime p)], ∃ s : ℤ_[p],
        (s : ℚ_[p])=((fractionRationalMap a b c hD z).im : ℚ_[p]) := by
      intro p hp
      obtain ⟨w,hw⟩ := h p
      exact ⟨w.im,congrArg QuadraticAlgebra.im hw⟩
    obtain ⟨s,hs⟩ := exists_int_of_forall_padic_integral _ hre
    obtain ⟨t,ht⟩ := exists_int_of_forall_padic_integral _ him
    refine ⟨⟨s,t⟩,?_⟩
    apply (fractionRationalMap a b c hD).injective
    rw [fractionRationalMap_algebraMap]
    apply QuadraticAlgebra.ext
    · exact hs
    · exact ht

lemma coefficientScalarMap_star (a b c : ℤ) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : CoefficientAlgebra (a : R) (b : R) (c : R)) :
    coefficientScalarMap a b c f (star z)=star (coefficientScalarMap a b c f z) := by
  apply QuadraticAlgebra.ext <;> simp [coefficientScalarMap]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

/-- The original fractional order is detected by membership in the actual
local-order submodule, using all finite primes. -/
theorem binaryFraction_mem_one_iff_padic (K : PositiveDefiniteIntegralLattice 2)
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    z ∈ (1 : K.BinaryDiscriminantFractionalIdeals) ↔
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        K.binaryPadicFractionMap p z ∈
          (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
            (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [FractionalIdeal.mem_one_iff]
  rw [exists_order_preimage_iff_forall_padic _ _ _ K.binaryDiscriminantOrder_discriminant_neg]
  constructor
  · intro h p hp
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    exact Submodule.mem_one.mpr (h p)
  · intro h p hp
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    exact Submodule.mem_one.mp (h p)

/-- Actual field elements of an original fractional ideal belong to its
actual local extension. -/
lemma binaryPadicFractionMap_mem_idealExtension (K : PositiveDefiniteIntegralLattice 2)
    (I : K.BinaryDiscriminantFractionalIdeals)
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (hz : z ∈ I) (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicFractionMap p z ∈ K.binaryPadicIdealExtension p I := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  exact Submodule.subset_span ⟨z,hz,rfl⟩

lemma binaryPadicIdealExtension_mono (K : PositiveDefiniteIntegralLattice 2)
    (I J : K.BinaryDiscriminantFractionalIdeals) (h : I ≤ J)
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p I ≤ K.binaryPadicIdealExtension p J := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  exact Submodule.span_mono (Set.image_mono h)

/-- Multiplication by the actual inverse detects membership in an
invertible fractional ideal. The local algebras are allowed to split. -/
theorem binaryFraction_mem_unit_iff_padic (K : PositiveDefiniteIntegralLattice 2)
    (I : K.BinaryDiscriminantFractionalIdealsˣ)
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    z ∈ I.val ↔ ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicFractionMap p z ∈ K.binaryPadicIdealExtension p I.val := by
  letI := K.binaryDiscriminantOrder_isDomain
  constructor
  · intro hz p hp
    exact K.binaryPadicFractionMap_mem_idealExtension I.val z hz p
  · intro hz
    have hprod : FractionalIdeal.spanSingleton _ z * (I⁻¹).val ≤ (1 : K.BinaryDiscriminantFractionalIdeals) := by
      apply FractionalIdeal.spanSingleton_mul_le_iff.mpr
      intro y hy
      apply (K.binaryFraction_mem_one_iff_padic (z*y)).mpr
      intro p hp
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      have hinv := K.binaryPadicFractionMap_mem_idealExtension (I⁻¹).val y hy p
      have hmul := Submodule.mul_mem_mul (hz p) hinv
      have he : K.binaryPadicIdealExtension p I.val*K.binaryPadicIdealExtension p (I⁻¹).val=1 := by
        rw [← map_mul,← Units.val_mul,mul_inv_cancel,Units.val_one,map_one]
      rw [he,← map_mul] at hmul
      exact hmul
    apply FractionalIdeal.spanSingleton_le_iff_mem.mp
    calc
      FractionalIdeal.spanSingleton _ z =
          (FractionalIdeal.spanSingleton _ z*(I⁻¹).val)*I.val := by simp [mul_assoc]
      _ ≤ 1*I.val := mul_le_mul_left hprod _
      _ = I.val := one_mul _

/-- Inclusion INTO an invertible original ideal is detected locally.
The source ideal need not be invertible. -/
theorem binaryFractionalIdeal_le_unit_iff_padic (K : PositiveDefiniteIntegralLattice 2)
    (I : K.BinaryDiscriminantFractionalIdeals) (J : K.BinaryDiscriminantFractionalIdealsˣ) :
    letI := K.binaryDiscriminantOrder_isDomain
    I ≤ J.val ↔ ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicIdealExtension p I ≤ K.binaryPadicIdealExtension p J.val := by
  letI := K.binaryDiscriminantOrder_isDomain
  constructor
  · intro h p hp
    exact K.binaryPadicIdealExtension_mono I J.val h p
  · intro h z hz
    apply (K.binaryFraction_mem_unit_iff_padic J z).mpr
    intro p hp
    exact h p (K.binaryPadicFractionMap_mem_idealExtension I z hz p)

/-- Equality of actual invertible fractional ideals is detected by all
original local-order extensions. This is independent of ideal construction. -/
theorem binaryFractionalIdeal_unit_eq_iff_padic (K : PositiveDefiniteIntegralLattice 2)
    (I J : K.BinaryDiscriminantFractionalIdealsˣ) :
    letI := K.binaryDiscriminantOrder_isDomain
    I=J ↔ ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicIdealExtension p I.val=K.binaryPadicIdealExtension p J.val := by
  letI := K.binaryDiscriminantOrder_isDomain
  constructor
  · rintro rfl p hp
    rfl
  · intro h
    apply Units.ext
    apply le_antisymm
    · exact (K.binaryFractionalIdeal_le_unit_iff_padic I.val J).mpr (fun p _ => (h p).le)
    · exact (K.binaryFractionalIdeal_le_unit_iff_padic J.val I).mpr (fun p _ => (h p).ge)

/-- The original field involution becomes the actual local quadratic
involution, including when the local algebra splits. -/
lemma binaryPadicFractionMap_conjugation (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)]
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryPadicFractionMap p
        (fractionConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) z)=
      star (K.binaryPadicFractionMap p z) := by
  letI := K.binaryDiscriminantOrder_isDomain
  change coefficientScalarMap _ _ _ (Rat.castHom ℚ_[p])
      (fractionRationalMap _ _ _ _ (fractionConjugation _ _ _ z))=_
  rw [fractionRationalMap_conjugation,coefficientScalarMap_star]
  rfl

/-- Conjugation of the original fractional ideal commutes with actual
local-order span extension. This is a semilinear, not scalar-fixed, map. -/
theorem binaryPadicIdealExtension_conjugation (K : PositiveDefiniteIntegralLattice 2)
    (I : K.BinaryDiscriminantFractionalIdeals) (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p
        (fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) I)=
      Submodule.ringSpanExtension
        (starRingEnd (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant))
        (K.binaryPadicIdealExtension p I) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  have hcompat (r : DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) :
      star (algebraMap (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
        (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) r)=
      algebraMap _ _ (star r) :=
    (coefficientScalarMap_star _ _ _ (algebraMap ℤ_[p] ℚ_[p]) r).symm
  change Submodule.span _ (_ '' _)=Submodule.ringSpanExtension _ (Submodule.span _ (_ '' _))
  rw [Submodule.ringSpanExtension_span
    (starRingEnd (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)) _ hcompat]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨K.binaryPadicFractionMap p
      (fractionConjugation 1 (K.binaryPrimitiveDiscriminant%2)
        (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) z),?_,?_⟩
    · refine ⟨_,?_,rfl⟩
      exact (mem_fractionalConjugation_iff _ _ _ K.binaryDiscriminantOrder_discriminant_neg I z).mp hz
    · change star (K.binaryPadicFractionMap p
        (fractionConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) z))=_
      rw [K.binaryPadicFractionMap_conjugation,star_star]
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨fractionConjugation 1 (K.binaryPrimitiveDiscriminant%2)
        (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) z,?_,?_⟩
    · apply (mem_fractionalConjugation_iff _ _ _ K.binaryDiscriminantOrder_discriminant_neg I _).mpr
      rw [fractionConjugation_involutive _ _ _ K.binaryDiscriminantOrder_discriminant_neg z]
      exact hz
    · exact K.binaryPadicFractionMap_conjugation p z

/-- A principal local span conjugates to the span of the conjugate of its
Actual generator. No global ideal construction is asserted here. -/
theorem binaryPadicIdealExtension_conjugation_of_eq_span (K : PositiveDefiniteIntegralLattice 2)
    (I : K.BinaryDiscriminantFractionalIdeals) (p : ℕ) [Fact (Nat.Prime p)]
    (y : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)
    (hy : letI := K.binaryDiscriminantOrder_isDomain
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicIdealExtension p I=Submodule.span _ {y}) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p
        (fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) I)=
      Submodule.span _ {star y} := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  rw [K.binaryPadicIdealExtension_conjugation,hy]
  have hcompat (r : DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) :
      star (algebraMap (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
        (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) r)=
      algebraMap _ _ (star r) :=
    (coefficientScalarMap_star _ _ _ (algebraMap ℤ_[p] ℚ_[p]) r).symm
  rw [Submodule.ringSpanExtension_span
    (starRingEnd (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)) _ hcompat,
    Set.image_singleton]
  rfl

/-- Given an invertible global patch, the local ideal factors imply the exact
global ideal identity. The existence of such a patch is not proved here. -/
theorem binaryIdeal_product_eq_of_invertible_local_patch (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (beta : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ)
    (J : K.BinaryDiscriminantFractionalIdealsˣ)
    (hpatch : letI := K.binaryDiscriminantOrder_isDomain
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        ∃ y : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
          K.binaryPadicIdealExtension p J.val=Submodule.span _ {y.val} ∧
          K.binaryPadicIdealExtension p
              (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD : K.BinaryDiscriminantFractionalIdeals)*
              Submodule.span _ {star y.val}=
            Submodule.span _ {K.binaryPadicFractionMap p beta.val}*Submodule.span _ {y.val}) :
    letI := K.binaryDiscriminantOrder_isDomain
    L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD *
        Units.map (fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)).toMonoidHom J=
      toPrincipalIdeal (DiscriminantOrder K.binaryPrimitiveDiscriminant)
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) beta * J := by
  letI := K.binaryDiscriminantOrder_isDomain
  apply (K.binaryFractionalIdeal_unit_eq_iff_padic _ _).mpr
  intro p hp
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  obtain ⟨y,hy,hlocal⟩ := hpatch p
  rw [Units.val_mul,Units.val_mul,coe_toPrincipalIdeal]
  change K.binaryPadicIdealExtension p
      ((L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD).val *
        fractionalConjugation _ _ _ J.val)=
    K.binaryPadicIdealExtension p (FractionalIdeal.spanSingleton _ beta.val*J.val)
  rw [map_mul,map_mul,K.binaryPadicIdealExtension_conjugation_of_eq_span J.val p y.val hy,
    K.binaryPadicIdealExtension_spanSingleton,hy]
  exact hlocal

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_int_of_forall_padic_integral
#assert_standard_axioms BinaryNormIdeal.exists_order_preimage_iff_forall_padic
#assert_standard_axioms BinaryNormIdeal.coefficientScalarMap_star
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_mem_one_iff_padic
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicFractionMap_mem_idealExtension
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_mono
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_mem_unit_iff_padic
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalIdeal_le_unit_iff_padic
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalIdeal_unit_eq_iff_padic
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicFractionMap_conjugation
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_conjugation
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_conjugation_of_eq_span
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdeal_product_eq_of_invertible_local_patch
