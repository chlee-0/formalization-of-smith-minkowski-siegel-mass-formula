import SMSFormula.Applications.Unimodular.TypeIIdentityMass
import SMSFormula.Applications.Unimodular.GenusMass
import SMSFormula.StandardAxiomsGuard

/-!
These endpoints are conditional on one explicit native finite-count input
(the `..._of_native_count` hypotheses).  That input is discharged for every
`typeIISeed k`, `k > 0`, by the stable recursive certificates in
`StableIdentityComparison.StableRecursive`; a checked axiom set on these
conditional statements does not by itself prove the input.
The proof reuses the actual general mass theorem and the closed Type I result;
it neither computes a desired density backwards nor changes a normalization.
-/
noncomputable section
open BigOperators PositiveDefiniteIntegralLattice UnimodularMass
namespace StableIdentityNativeAssembly

abbrev C {n : ℕ} (L : PositiveDefiniteIntegralLattice n) :=
  associatedBilinearDualQuotientCount L 2 3

/-- Unimodular native normalization, uniform in the lattice, not only I_n. -/
lemma native_factor {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular)
    (hn : 1 ≤ n) :
    L.massLocalFactor 2 =
      (C L : ℝ) * ((2 : ℝ)^((n-1)*(n-1)))⁻¹ := by
  rw [massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_valuationFactor_of_isUnimodular hU,
    gramDetPadicValuationFactor_two_rank_eq_tangentPow]
  have htri : 3*(n*(n-1)/2) = n*(n-1) + n*(n-1)/2 := by
    have h := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)
    omega
  have hsq : n*(n-1) = (n-1)*(n-1)+(n-1) := by
    have h : n = (n-1)+1 := by omega
    calc
      n*(n-1) = ((n-1)+1)*(n-1) := by nth_rewrite 1 [h]; rfl
      _ = (n-1)*(n-1)+(n-1) := by ring
  have hp : (2 : ℝ)^n = (2 : ℝ)^(n-1)*2 := by
    nth_rewrite 1 [show n = (n-1)+1 by omega]
    rw [pow_succ]
  rw [htri]
  push_cast
  rw [pow_add, hsq, pow_add, hp]
  dsimp [C]
  field_simp

/-- The characteristic orbit count gives the native density transfer. -/
theorem native_factor_of_count {n : ℕ} (hn : 2 ≤ n)
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular)
    (hcount : C (identityLattice (n+1)) = 2^(n+1)*C L) :
    L.massLocalFactor 2 =
      (2 : ℝ)^(n-2) * (identityLattice (n+1)).massLocalFactor 2 := by
  rw [native_factor L hU (by omega),
    native_factor (identityLattice (n+1)) (identityLattice_isUnimodular _) (by omega),
    hcount]
  push_cast
  have he : n*n = (n-2)+(n+1)+(n-1)*(n-1) := by
    have h1 : n-1+1=n := by omega
    have h2 : n-2+2=n := by omega
    nlinarith
  rw [he, pow_add, pow_add]
  field_simp
  ring

/-- The factor is independent of all Bernoulli numbers and genus masses. -/
def ratio (k : ℕ) : ℝ :=
  ((2 : ℝ)^(4*k)-1) * ((2 : ℝ)^(4*k-1)+1) / 2

lemma rank_lift_times_step (k : ℕ) (hk : 0 < k) :
    (2 : ℝ)^(8*k-2) * (identityQuadraticTypeILocalFactorStepClosed (8*k+1) : ℝ) =
      ratio k := by
  rw [identityQuadraticTypeILocalFactorStepClosed_of_mod_eight_eq_one (by omega)]
  have hdiv : (8*k+1-3)/2 = 4*k-1 := by omega
  have hsub : 8*k+1-2 = 8*k-1 := by omega
  rw [hdiv, hsub]
  push_cast
  have hA : (2 : ℝ)^(4*k) = 2*(2 : ℝ)^(4*k-1) := by
    nth_rewrite 1 [show 4*k = (4*k-1)+1 by omega]
    rw [pow_succ]
    ring
  have hB : (2 : ℝ)^(8*k-2) = ((2 : ℝ)^(4*k-1))^2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hC : (2 : ℝ)^(8*k-1) = 2*((2 : ℝ)^(4*k-1))^2 := by
    rw [show 8*k-1 = (8*k-2)+1 by omega, pow_succ, hB]
    ring
  rw [hB, hC]
  unfold ratio
  rw [hA]
  field_simp
  ring

lemma common_rhs (D a b x y c : ℝ)
    (hD : D ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : D*x = a⁻¹*c) (hy : D*y = b⁻¹*c) : a*x=b*y := by
  have hx' : a*(D*x)=c := by rw [hx, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hy' : b*(D*y)=c := by rw [hy, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  apply mul_left_cancel₀ hD
  calc
    D*(a*x) = a*(D*x) := by ring
    _ = c := hx'
    _ = b*(D*y) := hy'.symm
    _ = D*(b*y) := by ring

/-- Same-rank general mass formula plus the independently known Type I mass.
No positivity/nonvanishing lemma for a Bernoulli product is required. -/
theorem mass_of_local_ratio (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (2*(4*k))) (hU : L.IsUnimodular)
    (hlocal : L.massLocalFactor 2 =
      ratio k * (identityLattice (2*(4*k))).massLocalFactor 2) :
    L.ordinaryGenusMass = typeIIConstant (2*(4*k)) := by
  have hr : 2*(4*k) = 8*k := by omega
  have hs : typeIEvenRankSign (2*(4*k)) = 1 := by
    simp [typeIEvenRankSign, show (2*(4*k)) % 8 = 0 by omega]
  have hL := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic
    (m := 4*k) (by omega) (show Even (4*k) from ⟨2*k, by omega⟩) L hU
  have hI := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic
    (m := 4*k) (by omega) (show Even (4*k) from ⟨2*k, by omega⟩)
    (identityLattice (2*(4*k))) (identityLattice_isUnimodular _)
  rw [massPartialPrimeInverseProduct_two, hs] at hL hI
  norm_num only [Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] at hL hI
  have hD : (2 : ℝ)^(4*k-1)+1 ≠ 0 := by positivity
  have ha := ne_of_gt (massLocalFactor_pos L 2)
  have hb := ne_of_gt (massLocalFactor_pos (identityLattice (2*(4*k))) 2)
  have hp := common_rhs ((2 : ℝ)^(4*k-1)+1)
    (L.massLocalFactor 2)
    ((identityLattice (2*(4*k))).massLocalFactor 2)
    (L.ordinaryGenusMass : ℝ)
    ((identityLattice (2*(4*k))).ordinaryGenusMass : ℝ) _ hD ha hb hL hI
  rw [identityLattice_ordinaryGenusMass_eq_typeIConstant_of_three_le (by omega)] at hp
  have hc : (typeIConstant (2*(4*k)) : ℝ) =
      ratio k * (typeIIConstant (2*(4*k)) : ℝ) := by
    rw [hr]
    unfold ratio
    exact_mod_cast typeI_typeII_ratio_eight_mul k hk
  apply Rat.cast_injective (α := ℝ)
  apply mul_left_cancel₀ ha
  calc
    L.massLocalFactor 2 * (L.ordinaryGenusMass : ℝ) =
        (identityLattice (2*(4*k))).massLocalFactor 2 *
          (typeIConstant (2*(4*k)) : ℝ) := hp
    _ = L.massLocalFactor 2 * (typeIIConstant (2*(4*k)) : ℝ) := by
      rw [hc, hlocal]
      ring

/-- Only the native count bridge remains; no supplied density value is needed. -/
theorem mass_at_four_mul_of_native_count (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (2*(4*k))) (hU : L.IsUnimodular)
    (hcount : C (identityLattice (2*(4*k)+1)) = 2^(2*(4*k)+1)*C L) :
    L.ordinaryGenusMass = typeIIConstant (2*(4*k)) := by
  apply mass_of_local_ratio k hk L hU
  rw [native_factor_of_count (by omega) L hU hcount,
    identityLattice_massLocalFactor_two_succ_eq_mul_closed_step
      (2*(4*k)) (by omega)]
  have hc : (2 : ℝ)^(2*(4*k)-2) *
      (identityQuadraticTypeILocalFactorStepClosed (2*(4*k)+1) : ℝ) = ratio k := by
    simpa only [show 2*(4*k) = 8*k by omega] using rank_lift_times_step k hk
  calc
    (2 : ℝ)^(2*(4*k)-2) *
        ((identityLattice (2*(4*k))).massLocalFactor 2 *
          (identityQuadraticTypeILocalFactorStepClosed (2*(4*k)+1) : ℝ)) =
      ((2 : ℝ)^(2*(4*k)-2) *
        (identityQuadraticTypeILocalFactorStepClosed (2*(4*k)+1) : ℝ)) *
          (identityLattice (2*(4*k))).massLocalFactor 2 := by ring
    _ = _ := by rw [hc]

lemma cast_unimodular {n m : ℕ} (h : n=m) (L : PositiveDefiniteIntegralLattice n)
    (hU : L.IsUnimodular) : (cast (by rw [h]) L : PositiveDefiniteIntegralLattice m).IsUnimodular := by
  cases h
  exact hU
lemma cast_count {n m : ℕ} (h : n=m) (L : PositiveDefiniteIntegralLattice n) :
    C (cast (by rw [h]) L : PositiveDefiniteIntegralLattice m) = C L := by cases h; rfl
lemma cast_mass {n m : ℕ} (h : n=m) (L : PositiveDefiniteIntegralLattice n) :
    (cast (by rw [h]) L : PositiveDefiniteIntegralLattice m).ordinaryGenusMass = L.ordinaryGenusMass := by
  cases h
  rfl

/-- Actual seed family; the count premise is still open, not silently supplied. -/
theorem seed_mass_of_native_count (k : ℕ) (hk : 0 < k)
    (hcount : C (identityLattice (8*k+1)) = 2^(8*k+1)*C (typeIISeed k)) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8*k) := by
  let h : 8*k = 2*(4*k) := by omega
  let L : PositiveDefiniteIntegralLattice (2*(4*k)) := cast (by rw [h]) (typeIISeed k)
  have hU : L.IsUnimodular := cast_unimodular h _ (typeIISeed_isUnimodular k)
  have hC : C (identityLattice (2*(4*k)+1)) = 2^(2*(4*k)+1)*C L := by
    rw [cast_count h (typeIISeed k), ← h]
    exact hcount
  have hm := mass_at_four_mul_of_native_count k hk L hU hC
  rw [cast_mass h (typeIISeed k), ← h] at hm
  exact hm

/-- Full O stabilizers in the literal existing genus sum. -/
theorem seed_literal_sum_of_native_count (k : ℕ) (hk : 0 < k)
    (hcount : C (identityLattice (8*k+1)) = 2^(8*k+1)*C (typeIISeed k)) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8*k) := by
  change (typeIISeed k).ordinaryGenusMass = typeIIConstant (8*k)
  exact seed_mass_of_native_count k hk hcount

end StableIdentityNativeAssembly
#assert_standard_axioms StableIdentityNativeAssembly.native_factor
#assert_standard_axioms StableIdentityNativeAssembly.native_factor_of_count
#assert_standard_axioms StableIdentityNativeAssembly.rank_lift_times_step
#assert_standard_axioms StableIdentityNativeAssembly.mass_of_local_ratio
#assert_standard_axioms StableIdentityNativeAssembly.seed_mass_of_native_count
#assert_standard_axioms StableIdentityNativeAssembly.seed_literal_sum_of_native_count
#assert_not_declared RationalQuadraticSpaceMatrix.specialOrthogonalTamagawaNumberENNReal_eq_two
