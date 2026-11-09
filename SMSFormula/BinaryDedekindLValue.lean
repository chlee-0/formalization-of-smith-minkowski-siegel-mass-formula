import SMSFormula.BinaryIdealDirichletCoefficients

/-!
# The same-field Dedekind residue and the corrected L-function

The bounded field-sign extension supplies an absolutely convergent Euler
product on Re(s)>1. Every original bad-prime factor is retained when
comparing with the existing masked Dirichlet character.
-/

open Filter Topology Complex

namespace BinaryNormIdeal

/-- The bounded field-sign Dirichlet summand is completely multiplicative. -/
noncomputable def fieldSignSummandHom (d : ℤ) (s : ℂ) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := fieldSignExtension d n * riemannZetaSummandHom hs n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by simp only [map_mul]; ring

theorem summable_fieldSignSummand (d : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n => ‖fieldSignSummandHom d s (ne_zero_of_one_lt_re hs) n‖) := by
  change Summable (fun n => ‖fieldSignExtension d n *
    riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖)
  simp only [norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_of_le_one_left (norm_nonneg _) (fieldSignExtension_norm_le_one d n))

theorem tsum_fieldSignSummand (d : ℤ) (s : ℂ) (hs : 1 < s.re) :
    ∑' n, fieldSignSummandHom d s (ne_zero_of_one_lt_re hs) n =
      LSeries (fieldSignExtension d) s := by
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ (map_zero (fieldSignExtension d))]
  rfl

/-- The native completely multiplicative Euler theorem applies to the
actual bounded extension, with increasing-prime order. -/
theorem fieldSignLSeries_eulerProduct (d : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
      (1-(conductorPrimeSign d p : ℂ)*(p : ℂ)^(-s))⁻¹)
      atTop (𝓝 (LSeries (fieldSignExtension d) s)) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative
    (summable_fieldSignSummand d s hs)
  rw [tsum_fieldSignSummand d s hs] at h
  convert h using 1
  funext N
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primesBelow hp⟩
  have he := fieldSignExtension_prime_pow d p 1
  simp only [pow_one] at he
  change _ = (1-fieldSignExtension d p*(p : ℂ)^(-s))⁻¹
  rw [he]

/-- None of the finite field correction factors vanishes at one. -/
theorem fieldPrime_eulerFactor_one_ne_zero (d : ℤ) (p : {p : ℕ // p.Prime}) :
    1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-(1 : ℂ)) ≠ 0 := by
  letI : Fact p.val.Prime := ⟨p.prop⟩
  have hp : (p.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  rw [Complex.cpow_neg_one]
  intro h
  have he := congrArg (fun z : ℂ => z*(p.val : ℂ)) h
  simp only [sub_mul,one_mul,mul_assoc,inv_mul_cancel₀ hp,mul_one,zero_mul] at he
  have hi : (p.val : ℤ)-conductorPrimeSign d p.val=0 := by exact_mod_cast he
  rcases conductorPrimeSign_trichotomy d p.val with hs | hs | hs <;>
    have ht := p.prop.two_le <;> omega

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The field-sign L-series on the open half-plane equals the original
masked LFunction times every deleted field inverse factor. -/
theorem binaryFieldSignLSeries_eq_correctedLFunction (K : PositiveDefiniteIntegralLattice 2)
    (s : ℂ) (hs : 1 < s.re) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
      ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
    let d := NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    LSeries (fieldSignExtension d) s =
      DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) s *
        ∏ p ∈ massBadPrimeSet K, (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-s))⁻¹ := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  let d := NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
  dsimp only
  have hf : Tendsto (fun M : ℕ => ∏ p ∈ rationalPrimesUpTo M,
      (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-s))⁻¹)
      atTop (𝓝 (LSeries (fieldSignExtension d) s)) := by
    have h := (fieldSignLSeries_eulerProduct d s hs).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext M
    dsimp only [Function.comp_apply]
    rw [← rationalPrimesUpTo_map_val_eq_primesBelow M]
    simp only [Finset.prod_map,rationalPrimeValEmbedding,Function.Embedding.coeFn_mk]
  have hc : Tendsto (fun M : ℕ => ∏ p ∈ rationalPrimesUpTo M,
      (1-goodPrimeEvenDirichletCharacter K 1 p.val*(p.val : ℂ)^(-s))⁻¹)
      atTop (𝓝 (DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) s)) := by
    have h := (DirichletCharacter.LSeries_eulerProduct (goodPrimeEvenDirichletCharacter K 1) hs).comp
      (tendsto_add_atTop_nat 1)
    rw [← DirichletCharacter.LFunction_eq_LSeries _ hs] at h
    convert h using 1
    funext M
    dsimp only [Function.comp_apply]
    rw [← rationalPrimesUpTo_map_val_eq_primesBelow M]
    simp only [Finset.prod_map,rationalPrimeValEmbedding,Function.Embedding.coeFn_mk]
  have he : ∀ᶠ M : ℕ in atTop,
      (rationalPrimesUpTo M).filter (fun p => p ∈ massBadPrimeSet K)=massBadPrimeSet K := by
    filter_upwards [eventually_ge_atTop ((massBadPrimeSet K).sup fun p => p.val)] with M hM
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨(mem_rationalPrimesUpTo_iff M p).mpr ((Finset.le_sup hp).trans hM),hp⟩
  apply tendsto_nhds_unique hf
  apply Filter.Tendsto.congr' ?_ (hc.mul_const (∏ p ∈ massBadPrimeSet K,
    (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-s))⁻¹))
  filter_upwards [he] with M hM
  rw [K.binaryFieldInverseEulerProduct_eq_character_mul_bad (rationalPrimesUpTo M)
    (fun p => (p.val : ℂ)^(-s)),hM]

/-- Actual ideal coefficients bind the same field's zeta function to
the corrected original LFunction on Re(s)>1. -/
theorem binaryDedekindZeta_eq_riemannZeta_mul_correctedLFunction (K : PositiveDefiniteIntegralLattice 2)
    (s : ℂ) (hs : 1 < s.re) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
      ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
    let E := FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)
    NumberField.dedekindZeta E s = riemannZeta s *
      (DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) s *
        ∏ p ∈ massBadPrimeSet K,
          (1-(conductorPrimeSign (NumberField.discr E) p.val : ℂ)*(p.val : ℂ)^(-s))⁻¹) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  dsimp only
  have h := dedekindZeta_eq_riemannZeta_mul_fieldSignLSeries 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    K.binaryDiscriminantOrder_discriminant_neg s hs
  rw [K.binaryFieldSignLSeries_eq_correctedLFunction s hs] at h
  exact h

/-- The genuine same-field residue equals the original nontrivial
LFunction at one, with every deleted field factor restored. -/
theorem binaryDedekindResidue_eq_correctedLFunction (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
      ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
    let E := FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)
    (NumberField.dedekindZeta_residue E : ℂ) =
      DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) 1 *
        ∏ p ∈ massBadPrimeSet K,
          (1-(conductorPrimeSign (NumberField.discr E) p.val : ℂ)*(p.val : ℂ)⁻¹)⁻¹ := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  let E := FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)
  let d := NumberField.discr E
  let χ := goodPrimeEvenDirichletCharacter K 1
  dsimp only
  have hf (p : {p : ℕ // p.Prime}) : ContinuousAt
      (fun z : ℂ => (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-z))⁻¹) 1 := by
    have hfactor : ContinuousAt
        (fun z : ℂ => 1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-z)) 1 := by
      apply continuousAt_const.sub
      apply continuousAt_const.mul
      exact (continuousAt_const_cpow (Nat.cast_ne_zero.mpr p.prop.ne_zero)).comp
        continuousAt_id.neg
    exact hfactor.inv₀ (fieldPrime_eulerFactor_one_ne_zero d p)
  have hb (S : Finset {p : ℕ // p.Prime}) : ContinuousAt
      (fun z : ℂ => ∏ p ∈ S, (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-z))⁻¹) 1 := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 : ℂ)) 1)
    | @insert p S hp ih =>
      simp only [Finset.prod_insert hp]
      exact (hf p).mul ih
  have hχ : ContinuousAt (DirichletCharacter.LFunction χ) (1 : ℂ) :=
    (DirichletCharacter.differentiable_LFunction
      (goodPrimeEvenDirichletCharacter_ne_one K (by norm_num))).continuous.continuousAt
  have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcont := (hχ.mul (hb (massBadPrimeSet K))).tendsto.comp hreal
  have hpunct : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    apply Complex.continuous_ofReal.continuousAt.continuousWithinAt.tendsto_nhdsWithin
    intro x hx
    change (x : ℂ) ≠ 1
    exact_mod_cast ne_of_gt hx
  have hzeta := riemannZeta_residue_one.comp hpunct
  have hnew := hzeta.mul hcont
  simp only [one_mul] at hnew
  have hlimit : Tendsto (fun x : ℝ => ((x : ℂ)-1)*NumberField.dedekindZeta E x)
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1 *
        ∏ p ∈ massBadPrimeSet K,
          (1-(conductorPrimeSign d p.val : ℂ)*(p.val : ℂ)^(-(1 : ℂ)))⁻¹)) := by
    apply Filter.Tendsto.congr' ?_ hnew
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    dsimp only [Function.comp_apply,Pi.mul_apply,χ,d,E]
    rw [K.binaryDedekindZeta_eq_riemannZeta_mul_correctedLFunction (x : ℂ)
      (by simpa only [Complex.ofReal_re] using hx)]
    ring
  have he := tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT E) hlimit
  simpa only [Complex.cpow_neg_one] using he

/-- The original full-O mass now has a proved corrected LFunction
expression. Its actual original genus two-torsion remains present. -/
theorem ordinaryGenusMass_eq_correctedLFunction (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
      ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
    let O := DiscriminantOrder K.binaryPrimitiveDiscriminant
    let E := FractionRing O
    ((ordinaryGenusMass K : ℚ) : ℝ) =
      Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| /
        (4*Real.pi*(Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker : ℝ)) *
          (DirichletCharacter.LFunction (goodPrimeEvenDirichletCharacter K 1) 1 *
            ∏ p ∈ massBadPrimeSet K,
              (1-(conductorPrimeSign (NumberField.discr E) p.val : ℂ)*(p.val : ℂ)⁻¹)⁻¹).re *
            ∏ p ∈ K.binaryOrderIndex.primeFactors,
              (1-(conductorPrimeSign (NumberField.discr E) p : ℝ)/(p : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  dsimp only
  have h := congrArg Complex.re K.binaryDedekindResidue_eq_correctedLFunction
  simp only [Complex.ofReal_re] at h
  rw [K.ordinaryGenusMass_eq_dedekindZeta_residue,h]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.fieldSignSummandHom
#assert_standard_axioms BinaryNormIdeal.summable_fieldSignSummand
#assert_standard_axioms BinaryNormIdeal.tsum_fieldSignSummand
#assert_standard_axioms BinaryNormIdeal.fieldSignLSeries_eulerProduct
#assert_standard_axioms BinaryNormIdeal.fieldPrime_eulerFactor_one_ne_zero
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldSignLSeries_eq_correctedLFunction
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDedekindZeta_eq_riemannZeta_mul_correctedLFunction
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDedekindResidue_eq_correctedLFunction
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_correctedLFunction
