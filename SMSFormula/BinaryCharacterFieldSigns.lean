import SMSFormula.BinaryDedekindResidue
import SMSFormula.BinaryOrderedProductEndpoint

/-!
# The product character and the prime signs of the same field

The existing fixed-modulus character deletes all lattice bad primes.
Its remaining prime values are the same field's quadratic residue signs.
Finite Euler products keep every deleted field factor explicitly.
-/

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The product discriminant is the primitive order discriminant times
the square of the original content. -/
theorem binaryCharacterDiscriminant_eq_content_sq_mul_primitive (K : PositiveDefiniteIntegralLattice 2) :
    goodPrimeEvenCharacterDiscriminant K 1 =
      (K.binaryContent : ℤ)^2*K.binaryPrimitiveDiscriminant := by
  rw [goodPrimeEvenCharacterDiscriminant,
    K.polarDeterminant_eq_two_pow_mul_pairingDeterminant,
    K.binaryContent_sq_mul_binaryPrimitiveDiscriminant]
  norm_num

/-- The actual product discriminant differs from the same field
discriminant by the displayed original content/index square. -/
theorem binaryCharacterDiscriminant_eq_content_index_sq_mul_fieldDiscr (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    goodPrimeEvenCharacterDiscriminant K 1 =
      ((K.binaryContent*K.binaryOrderIndex : ℕ) : ℤ)^2 *
        NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  rw [K.binaryCharacterDiscriminant_eq_content_sq_mul_primitive]
  calc
    _ = (K.binaryContent : ℤ)^2*((K.binaryOrderIndex : ℤ)^2*
        NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) :=
      congrArg (fun z : ℤ => (K.binaryContent : ℤ)^2*z)
        K.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr
    _ = _ := by push_cast; ring

/-- A prime is deleted by the existing product character exactly when
it is a lattice bad prime. This includes the dyadic deletion. -/
theorem binaryPrime_dvd_characterModulus_iff (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) :
    p.val ∣ goodPrimeEvenDirichletModulus K 1 ↔ p ∈ massBadPrimeSet K := by
  rw [mem_massBadPrimeSet_iff,goodPrimeEvenDirichletModulus,
    goodPrimeEvenCharacterDiscriminant_natAbs,p.property.dvd_mul]
  have h : p.val ∣ 4 ↔ p.val=2 := by
    constructor
    · intro h
      have h2 : p.val ∣ 2 := p.property.dvd_of_dvd_pow (show p.val ∣ 2^2 by simpa using h)
      exact ((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left p.property.ne_one
    · intro h
      rw [h]
      norm_num
  rw [h]

/-- The actual fixed-modulus character vanishes at every deleted prime. -/
theorem binaryDirichletCharacter_eq_zero_of_bad (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) (hp : p ∈ massBadPrimeSet K) :
    goodPrimeEvenDirichletCharacter K 1 p.val=0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime,p.property.coprime_iff_not_dvd]
  exact not_not.mpr ((K.binaryPrime_dvd_characterModulus_iff p).mpr hp)

/-- Away from the actual bad set, the content/index square is a unit
at p. No squarefree or maximal-order classification is assumed. -/
theorem binaryContentIndex_ne_zero_mod_of_good (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) (hp : p ∉ massBadPrimeSet K) :
    (((K.binaryContent*K.binaryOrderIndex : ℕ) : ℤ) : ZMod p.val) ≠ 0 := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hn : (goodPrimeEvenCharacterDiscriminant K 1 : ZMod p.val) ≠ 0 := by
    intro h
    have hdiv : (p.val : ℤ) ∣ goodPrimeEvenCharacterDiscriminant K 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    have hnat := Int.natAbs_dvd_natAbs.mpr hdiv
    have hnot := not_mem_massBadPrimeSet_not_dvd_polarDeterminant_natAbs K hp
    apply hnot
    simpa only [Int.natAbs_natCast,goodPrimeEvenCharacterDiscriminant_natAbs] using hnat
  intro h
  apply hn
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  rw [K.binaryCharacterDiscriminant_eq_content_index_sq_mul_fieldDiscr]
  push_cast
  rw [show ((K.binaryContent : ZMod p.val)*(K.binaryOrderIndex : ZMod p.val))=0 from by
    simpa only [Int.cast_natCast,Nat.cast_mul,Int.cast_mul] using h,zero_pow (by decide),zero_mul]

/-- The original good-prime quadratic value equals the same field's
prime sign, with the original bad-prime premise. -/
theorem binaryGoodPrimeQuadraticCharacter_eq_fieldSign (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) (hp : p ∉ massBadPrimeSet K) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    goodPrimeQuadraticCharacter K p =
      conductorPrimeSign (NumberField.discr
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p.val := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : Fact p.val.Prime := ⟨p.property⟩
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_even K p 1 (by norm_num),
    ← jacobiSym.legendreSym.to_jacobiSym p.val,
    K.binaryCharacterDiscriminant_eq_content_index_sq_mul_fieldDiscr,
    legendreSym.mul,legendreSym.sq_one' p.val (K.binaryContentIndex_ne_zero_mod_of_good p hp),one_mul,
    conductorPrimeSign_eq,if_neg (not_mem_massBadPrimeSet_ne_two K hp)]

/-- Exact all-prime comparison: the existing actual Dirichlet character
is the field prime sign with the original bad-prime mask. -/
theorem binaryDirichletCharacter_eq_masked_fieldSign (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    goodPrimeEvenDirichletCharacter K 1 p.val =
      if p ∈ massBadPrimeSet K then 0 else
        (conductorPrimeSign (NumberField.discr
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p.val : ℂ) := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  by_cases hp : p ∈ massBadPrimeSet K
  · rw [if_pos hp,K.binaryDirichletCharacter_eq_zero_of_bad p hp]
  · rw [if_neg hp,← goodPrimeQuadraticCharacter_eq_dirichletCharacter K 1 p hp (by norm_num),
      K.binaryGoodPrimeQuadraticCharacter_eq_fieldSign p hp]
    norm_cast

/-- Exact finite Euler-factor comparison with every deleted field factor
kept explicit. The weight is arbitrary; in particular it can be p^(-s). -/
theorem binaryFieldEulerProduct_eq_character_mul_bad (K : PositiveDefiniteIntegralLattice 2)
    (S : Finset {p : ℕ // p.Prime}) (w : {p : ℕ // p.Prime} → ℂ) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    let d := NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (∏ p ∈ S, (1-(conductorPrimeSign d p.val : ℂ)*w p)) =
      (∏ p ∈ S, (1-goodPrimeEvenDirichletCharacter K 1 p.val*w p)) *
        ∏ p ∈ S.filter (fun p => p ∈ massBadPrimeSet K),
          (1-(conductorPrimeSign d p.val : ℂ)*w p) := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  dsimp only
  rw [Finset.prod_filter,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [K.binaryDirichletCharacter_eq_masked_fieldSign p]
  by_cases hp : p ∈ massBadPrimeSet K <;> simp only [hp,if_true,if_false,zero_mul,sub_zero,one_mul,mul_one]

/-- The same exact correction for finite inverse Euler products. It does
not require division by a nonzero product or an analytic hypothesis. -/
theorem binaryFieldInverseEulerProduct_eq_character_mul_bad (K : PositiveDefiniteIntegralLattice 2)
    (S : Finset {p : ℕ // p.Prime}) (w : {p : ℕ // p.Prime} → ℂ) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    let d := NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (∏ p ∈ S, (1-(conductorPrimeSign d p.val : ℂ)*w p)⁻¹) =
      (∏ p ∈ S, (1-goodPrimeEvenDirichletCharacter K 1 p.val*w p)⁻¹) *
        ∏ p ∈ S.filter (fun p => p ∈ massBadPrimeSet K),
          (1-(conductorPrimeSign d p.val : ℂ)*w p)⁻¹ := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  dsimp only
  simp only [Finset.prod_inv_distrib]
  rw [K.binaryFieldEulerProduct_eq_character_mul_bad S w,mul_inv_rev,mul_comm]

/-- Increasing-prime convergence of all field-sign Euler factors to the
existing nontrivial Dirichlet L-value with its exact finite correction.
This does not identify that value with the actual Dedekind residue. -/
theorem binaryFieldInverseEulerProduct_tendsto_correctedLFunction (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
      ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
    let d := NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    Filter.Tendsto (fun M : ℕ => ∏ p ∈ rationalPrimesUpTo M,
      (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)⁻¹)⁻¹)
      Filter.atTop (nhds (DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) 1 *
        ∏ p ∈ massBadPrimeSet K, (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)⁻¹)⁻¹)) := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  dsimp only
  have ht := dirichlet_L_nontrivial_character_endpoint_complexEulerProduct_tendsto
    (goodPrimeEvenDirichletCharacter K 1) (goodPrimeEvenDirichletCharacter_ne_one K (by norm_num))
      (goodPrimeEvenDirichletCharacter_sq K 1 (by norm_num))
  have hc : Filter.Tendsto (fun M : ℕ => ∏ p ∈ rationalPrimesUpTo M,
      (1-goodPrimeEvenDirichletCharacter K 1 p.val*(p.val : ℂ)⁻¹)⁻¹)
      Filter.atTop (nhds (DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) 1)) := by
    convert ht using 1
    funext M
    rw [← rationalPrimesUpTo_map_val_eq_primesBelow M]
    simp only [Finset.prod_map,rationalPrimeValEmbedding,Function.Embedding.coeFn_mk,
      Nat.cast_one,Complex.cpow_neg_one]
  have he : ∀ᶠ M : ℕ in Filter.atTop,
      (rationalPrimesUpTo M).filter (fun p => p ∈ massBadPrimeSet K)=massBadPrimeSet K := by
    filter_upwards [Filter.eventually_ge_atTop ((massBadPrimeSet K).sup fun p => p.val)] with M hM
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨(mem_rationalPrimesUpTo_iff M p).mpr ((Finset.le_sup hp).trans hM),hp⟩
  apply Filter.Tendsto.congr' ?_ (hc.mul_const (∏ p ∈ massBadPrimeSet K,
    (1-(conductorPrimeSign (NumberField.discr
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p.val : ℂ)*(p.val : ℂ)⁻¹)⁻¹))
  filter_upwards [he] with M hM
  rw [K.binaryFieldInverseEulerProduct_eq_character_mul_bad (rationalPrimesUpTo M)
    (fun p => (p.val : ℂ)⁻¹),hM]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCharacterDiscriminant_eq_content_sq_mul_primitive
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCharacterDiscriminant_eq_content_index_sq_mul_fieldDiscr
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrime_dvd_characterModulus_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDirichletCharacter_eq_zero_of_bad
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryContentIndex_ne_zero_mod_of_good
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryGoodPrimeQuadraticCharacter_eq_fieldSign
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDirichletCharacter_eq_masked_fieldSign

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldEulerProduct_eq_character_mul_bad
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldInverseEulerProduct_eq_character_mul_bad

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldInverseEulerProduct_tendsto_correctedLFunction
