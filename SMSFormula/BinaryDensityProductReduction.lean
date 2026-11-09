import SMSFormula.BinaryDedekindLValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The actual binary density product and its finite remaining identity

The same-field residue supplies the infinite part of the original ordered
density product. The original bad-prime densities stay literal, including
two, content and conductor primes. The final finite identity is not proved.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal Filter Topology

/-- The original archimedean normalization in rank two. -/
theorem archimedeanMassFactor_two : archimedeanMassFactor 2=2/Real.pi := by
  unfold archimedeanMassFactor
  norm_num [Finset.prod_range_succ,Real.Gamma_one,Real.Gamma_one_half_eq]
  rw [Real.sqrt_eq_rpow,mul_assoc,← Real.rpow_add Real.pi_pos]
  norm_num [div_eq_mul_inv]
  exact Real.rpow_neg_one _

/-- The same field's real Euler factor, without the original character mask. -/
def binaryFieldEulerFactor (K : PositiveDefiniteIntegralLattice 2) (p : {p : ℕ // p.Prime}) : ℝ :=
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  1-(conductorPrimeSign (NumberField.discr
    (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p.val : ℝ)/(p.val : ℝ)

/-- Every field factor is positive, including the original bad primes. -/
theorem binaryFieldEulerFactor_pos (K : PositiveDefiniteIntegralLattice 2) (p : {p : ℕ // p.Prime}) :
    0<K.binaryFieldEulerFactor p := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : Fact p.val.Prime := ⟨p.prop⟩
  have hp : (1 : ℝ)<p.val := by exact_mod_cast p.prop.one_lt
  have hpos : (0 : ℝ)<p.val := by positivity
  unfold binaryFieldEulerFactor
  rcases conductorPrimeSign_trichotomy (NumberField.discr
    (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p.val with h | h | h
  · simp only [h,Int.cast_neg,Int.cast_one,neg_div,sub_neg_eq_add]
    positivity
  · simp [h]
  · simp only [h,Int.cast_one]
    exact sub_pos.mpr ((div_lt_one hpos).mpr hp)

/-- The actual density equals its field Euler factor away from original Bad. -/
theorem massLocalFactorAtPrime_eq_binaryFieldEulerFactor_of_good
    (K : PositiveDefiniteIntegralLattice 2) (p : {p : ℕ // p.Prime}) (hp : p ∉ massBadPrimeSet K) :
    massLocalFactorAtPrime K p=K.binaryFieldEulerFactor p := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  rw [massLocalFactorAtPrime_eq_goodPrimeEvenEulerFactor K p hp 1 (by norm_num) (by norm_num)]
  simp only [goodPrimeEvenEulerFactor,goodPrimeEulerCore,Nat.sub_self,Finset.Icc_eq_empty_of_lt
    (show 0<1 by norm_num),Finset.prod_empty,one_mul,Nat.cast_one,Real.rpow_neg_one]
  rw [K.binaryGoodPrimeQuadraticCharacter_eq_fieldSign p hp]
  rfl

/-- Only the original bad primes remain: actual inverse density times the
Field factor removed from the infinite product. -/
def binaryBadDensityCorrection (K : PositiveDefiniteIntegralLattice 2) : ℝ :=
  ∏ p ∈ massBadPrimeSet K, K.binaryFieldEulerFactor p*massLocalInverseFactorAtPrime K p

theorem binaryBadDensityCorrection_pos (K : PositiveDefiniteIntegralLattice 2) :
    0<K.binaryBadDensityCorrection := by
  apply Finset.prod_pos
  intro p _
  exact mul_pos (K.binaryFieldEulerFactor_pos p) (massLocalInverseFactorAtPrime_pos K p)

/-- The literal F-dual count in rank two has coefficient 1/8 at two and
1/2 at odd primes. This keeps the associated-bilinear conversion separate
from the quadratic congruence and determinant norm. -/
theorem binaryMassLocalFactor_eq_dualCount (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    massLocalFactor K p =
      (if p=2 then (1/8 : ℝ) else 1/2)*
        ((p : ℝ)^localDensityHenselExponent K p)⁻¹*
        (localDualQuotientCount K p (localDensityHenselExponent K p) : ℝ)*
          ‖(K.polarDeterminant : ℤ_[p])‖^(-(1 : ℝ)/2) := by
  change (((dualCountNormalizationFactor p 2)*
      ((1/2 : ℚ)*twoPadicNormInvPow p 2*
        ((p : ℚ)^localDensityDenominatorExponent 2 (localDensityHenselExponent K p))⁻¹*
          (localDualQuotientCount K p (localDensityHenselExponent K p) : ℚ)) : ℚ) : ℝ)*
      ‖(K.polarDeterminant : ℤ_[p])‖^(((1 : ℝ)-2)/2) = _
  norm_num only [localDensityDenominatorExponent,Nat.reduceSub,Nat.reduceMul,Nat.reduceDiv,
    mul_one,show ((1 : ℝ)-2)/2= -1/2 by norm_num]
  push_cast
  by_cases hp : p=2
  all_goals norm_num [dualCountNormalizationFactor,twoPadicNormInvPow,hp]
  all_goals ring
  all_goals simp

/-- Exact finite product comparison. No bad-prime density is evaluated. -/
theorem massFinitePrimeInverseProduct_eq_binaryField_mul_bad
    (K : PositiveDefiniteIntegralLattice 2) (S : Finset {p : ℕ // p.Prime}) :
    massFinitePrimeInverseProduct K S =
      (∏ p ∈ S, (K.binaryFieldEulerFactor p)⁻¹)*
        ∏ p ∈ S.filter (fun p => p ∈ massBadPrimeSet K),
          K.binaryFieldEulerFactor p*massLocalInverseFactorAtPrime K p := by
  classical
  rw [Finset.prod_filter,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p ∈ massBadPrimeSet K
  · rw [if_pos hp,← mul_assoc,inv_mul_cancel₀ (K.binaryFieldEulerFactor_pos p).ne',one_mul]
  · rw [if_neg hp,mul_one,massLocalInverseFactorAtPrime,
      massLocalFactorAtPrime_eq_binaryFieldEulerFactor_of_good K p hp]

/-- The increasing-prime field inverse product converges to the same
genuine Dedekind residue, after restoring every original deleted factor. -/
theorem binaryFieldInverseProduct_tendsto_residue (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    Tendsto (fun N : ℕ => ∏ p ∈ rationalPrimesUpTo N, (K.binaryFieldEulerFactor p)⁻¹)
      atTop (𝓝 (NumberField.dedekindZeta_residue
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  have h := K.binaryFieldInverseEulerProduct_tendsto_correctedLFunction
  dsimp only at h
  rw [← K.binaryDedekindResidue_eq_correctedLFunction] at h
  have hr := Complex.continuous_re.tendsto _ |>.comp h
  simpa only [binaryFieldEulerFactor,← Complex.ofReal_natCast,← Complex.ofReal_intCast,
    ← Complex.ofReal_one,← Complex.ofReal_inv,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_prod,Complex.ofReal_re,div_eq_mul_inv] using hr

/-- The actual ordered density product now has a canonical value with
no L-function or uncomputed infinite product in its expression. -/
theorem massLocalInverseProductTendsTo_binaryResidue_mul_badDensity
    (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    massLocalInverseProductTendsTo K
      (NumberField.dedekindZeta_residue
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))*
          K.binaryBadDensityCorrection) := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have he : ∀ᶠ N : ℕ in atTop,
      (rationalPrimesUpTo N).filter (fun p => p ∈ massBadPrimeSet K)=massBadPrimeSet K := by
    filter_upwards [eventually_ge_atTop ((massBadPrimeSet K).sup fun p => p.val)] with N hN
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨(mem_rationalPrimesUpTo_iff N p).mpr ((Finset.le_sup hp).trans hN),hp⟩
  apply Filter.Tendsto.congr' ?_ ((K.binaryFieldInverseProduct_tendsto_residue).mul_const
    K.binaryBadDensityCorrection)
  filter_upwards [he] with N hN
  rw [massPartialPrimeInverseProduct,K.massFinitePrimeInverseProduct_eq_binaryField_mul_bad,hN]
  rfl

/-- Uniqueness binds every limit of the original product to the same
residue and finite bad-prime correction. -/
theorem massLocalInverseProductTendsTo_iff_binaryResidue_mul_badDensity
    (K : PositiveDefiniteIntegralLattice 2) (P : ℝ) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    massLocalInverseProductTendsTo K P ↔
      P=NumberField.dedekindZeta_residue
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))*
          K.binaryBadDensityCorrection := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  constructor
  · intro h
    exact tendsto_nhds_unique h K.massLocalInverseProductTendsTo_binaryResidue_mul_badDensity
  · rintro rfl
    exact K.massLocalInverseProductTendsTo_binaryResidue_mul_badDensity

/-- The mass formula for the same `K` and the same positive `P` is equivalent to this one
finite identity. The original two-torsion and bad densities remain in it.
This theorem does not assert that the displayed finite equality holds. -/
theorem binaryMassFormula_iff_finite_badDensity_identity (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    let O := DiscriminantOrder K.binaryPrimitiveDiscriminant
    let E := FractionRing O
    (∃ P : ℝ, 0<P ∧ massLocalInverseProductTendsTo K P ∧
      ((ordinaryGenusMass K : ℚ) : ℝ)=archimedeanMassFactor 2*P) ↔
      8*(Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker : ℝ)*
          K.binaryBadDensityCorrection =
        Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| *
          ∏ p ∈ K.binaryOrderIndex.primeFactors,
            (1-(conductorPrimeSign (NumberField.discr E) p : ℝ)/(p : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI := K.finite_binaryClassGroup
  let O := DiscriminantOrder K.binaryPrimitiveDiscriminant
  let E := FractionRing O
  let t : ℝ := Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker
  let rho := NumberField.dedekindZeta_residue E
  let A := Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)|
  let e := ∏ p ∈ K.binaryOrderIndex.primeFactors,
    (1-(conductorPrimeSign (NumberField.discr E) p : ℝ)/(p : ℝ))
  have ht : 0<t := by
    dsimp only [t]
    exact_mod_cast (Nat.card_pos : 0<Nat.card
      (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker)
  have hr : 0<rho := NumberField.dedekindZeta_residue_pos E
  have hm : ((ordinaryGenusMass K : ℚ) : ℝ)=A/(4*Real.pi*t)*rho*e :=
    K.ordinaryGenusMass_eq_dedekindZeta_residue
  have halg : A/(4*Real.pi*t)*rho*e=(2/Real.pi)*(rho*K.binaryBadDensityCorrection) ↔
      8*t*K.binaryBadDensityCorrection=A*e := by
    have hc : (2/Real.pi)*(rho*K.binaryBadDensityCorrection)=
        (rho/(4*Real.pi*t))*(8*t*K.binaryBadDensityCorrection) := by
      field_simp [Real.pi_ne_zero,ht.ne']
      ring
    rw [hc]
    have hs : A/(4*Real.pi*t)*rho*e=(rho/(4*Real.pi*t))*(A*e) := by ring
    rw [hs]
    have hn : rho/(4*Real.pi*t) ≠ 0 := div_ne_zero hr.ne'
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht.ne')
    constructor
    · intro h
      exact (mul_left_cancel₀ hn h).symm
    · intro h
      rw [h]
  change (∃ P : ℝ, 0<P ∧ massLocalInverseProductTendsTo K P ∧
    ((ordinaryGenusMass K : ℚ) : ℝ)=archimedeanMassFactor 2*P) ↔
      8*t*K.binaryBadDensityCorrection=A*e
  constructor
  · rintro ⟨P,_,hP,hM⟩
    have he := (K.massLocalInverseProductTendsTo_iff_binaryResidue_mul_badDensity P).mp hP
    rw [he,archimedeanMassFactor_two,hm] at hM
    exact halg.mp hM
  · intro h
    refine ⟨rho*K.binaryBadDensityCorrection,
      mul_pos hr K.binaryBadDensityCorrection_pos,
      K.massLocalInverseProductTendsTo_binaryResidue_mul_badDensity,?_⟩
    rw [archimedeanMassFactor_two,hm]
    exact halg.mpr h

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.archimedeanMassFactor_two
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldEulerFactor
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldEulerFactor_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.massLocalFactorAtPrime_eq_binaryFieldEulerFactor_of_good
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadDensityCorrection
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadDensityCorrection_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryMassLocalFactor_eq_dualCount
#assert_standard_axioms PositiveDefiniteIntegralLattice.massFinitePrimeInverseProduct_eq_binaryField_mul_bad
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldInverseProduct_tendsto_residue
#assert_standard_axioms PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo_binaryResidue_mul_badDensity
#assert_standard_axioms PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo_iff_binaryResidue_mul_badDensity
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryMassFormula_iff_finite_badDensity_identity
