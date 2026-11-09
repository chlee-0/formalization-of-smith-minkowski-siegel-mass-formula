import SMSFormula.RationalFiniteAdeleIntegralQuotient

/-!
# Finite strong approximation for rational adeles

This file proves the concrete CRT statement isolated by
`RationalFiniteAdeleIntegralQuotient`: every rational finite adele differs
from a diagonal rational point by an everywhere-integral finite adele.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

private noncomputable def finiteAdelePositiveDenominator
    (a : RationalFiniteAdele) : ℕ :=
  (finiteAdeleDenominator a).natAbs

private theorem finiteAdelePositiveDenominator_ne_zero
    (a : RationalFiniteAdele) :
    finiteAdelePositiveDenominator a ≠ 0 := by
  simp only [finiteAdelePositiveDenominator, Int.natAbs_ne_zero]
  exact finiteAdeleDenominator_ne_zero a

private theorem finiteAdelePositiveDenominator_mul_mem
    (a : RationalFiniteAdele) :
    algebraMap ℤ RationalFiniteAdele
          (finiteAdelePositiveDenominator a : ℤ) * a ∈
        integralFiniteAdeleSubring := by
  let d := finiteAdeleDenominator a
  have hd := finiteAdeleDenominator_mul_mem_integralFiniteAdeleSubring a
  by_cases hnonneg : 0 ≤ d
  · simpa [finiteAdelePositiveDenominator, d, Int.natAbs_of_nonneg hnonneg]
      using hd
  · have hneg : d < 0 := lt_of_not_ge hnonneg
    have hnegmem :
        -(algebraMap ℤ RationalFiniteAdele d * a) ∈
          integralFiniteAdeleSubring :=
      integralFiniteAdeleSubring.neg_mem hd
    have hcast : (finiteAdelePositiveDenominator a : ℤ) = -d := by
      change ((d.natAbs : ℕ) : ℤ) = -d
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos hneg.le)
    rw [hcast, map_neg]
    simpa only [neg_mul] using hnegmem

private noncomputable def finiteAdeleScaledIntegral
    (a : RationalFiniteAdele) : integralFiniteAdeleSubring :=
  ⟨algebraMap ℤ RationalFiniteAdele
      (finiteAdelePositiveDenominator a : ℤ) * a,
    finiteAdelePositiveDenominator_mul_mem a⟩

private def finiteAdeleDenominatorPlace
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) :
    IsDedekindDomain.HeightOneSpectrum ℤ :=
  Rat.HeightOneSpectrum.primesEquiv.symm
    ⟨p, Nat.prime_of_mem_primeFactors p.property⟩

private instance finiteAdeleDenominatorPrimeFact
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) :
    Fact (Nat.Prime (p : ℕ)) :=
  ⟨Nat.prime_of_mem_primeFactors p.property⟩

private instance heightOneSpectrumPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩

private noncomputable def finiteAdeleScaledPadicIntAt
    (a : RationalFiniteAdele)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ℤ_[Rat.HeightOneSpectrum.primesEquiv v] :=
  Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
    ⟨(finiteAdeleScaledIntegral a : RationalFiniteAdele) v,
      (finiteAdeleScaledIntegral a).property v⟩

private def finiteAdeleApproximationModulus
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) : ℕ :=
  (p : ℕ) ^ (finiteAdelePositiveDenominator a).factorization p

private noncomputable def finiteAdeleApproximationResidue
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) : ℕ :=
  (finiteAdeleScaledPadicIntAt a (finiteAdeleDenominatorPlace a p)).appr
    ((finiteAdelePositiveDenominator a).factorization p)

private theorem finiteAdeleApproximationModulus_ne_zero
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) :
    finiteAdeleApproximationModulus a p ≠ 0 := by
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.property).ne_zero

private theorem finiteAdeleApproximationModulus_pairwise_coprime
    (a : RationalFiniteAdele) :
    Set.univ.Pairwise
      (Function.onFun Nat.Coprime (finiteAdeleApproximationModulus a)) := by
  intro p _ q _ hpq
  simpa [finiteAdeleApproximationModulus] using
    (Nat.pairwise_coprime_pow_primeFactors_factorization
      (n := finiteAdelePositiveDenominator a) hpq)

private noncomputable def finiteAdeleApproximationNumerator
    (a : RationalFiniteAdele) : ℕ :=
  (Nat.chineseRemainderOfFinset
    (finiteAdeleApproximationResidue a)
    (finiteAdeleApproximationModulus a) Finset.univ
    (fun p _ ↦ finiteAdeleApproximationModulus_ne_zero a p)
    (by simpa only [Finset.coe_univ] using
      finiteAdeleApproximationModulus_pairwise_coprime a)).1

private theorem finiteAdeleApproximationNumerator_residue
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) :
    PadicInt.toZModPow
        ((finiteAdelePositiveDenominator a).factorization p)
        (finiteAdeleApproximationNumerator a :
          ℤ_[Rat.HeightOneSpectrum.primesEquiv
            (finiteAdeleDenominatorPlace a p)]) =
      PadicInt.toZModPow
        ((finiteAdelePositiveDenominator a).factorization p)
        (finiteAdeleScaledPadicIntAt a
          (finiteAdeleDenominatorPlace a p)) := by
  let e := (finiteAdelePositiveDenominator a).factorization p
  let m := finiteAdeleApproximationModulus a p
  have hmod : finiteAdeleApproximationNumerator a ≡
      finiteAdeleApproximationResidue a p [MOD m] :=
    (Nat.chineseRemainderOfFinset
      (finiteAdeleApproximationResidue a)
      (finiteAdeleApproximationModulus a) Finset.univ
      (fun q _ ↦ finiteAdeleApproximationModulus_ne_zero a q)
      (by simpa only [Finset.coe_univ] using
        finiteAdeleApproximationModulus_pairwise_coprime a)).2 p
        (Finset.mem_univ p)
  have hcast :
      (finiteAdeleApproximationNumerator a : ZMod m) =
        finiteAdeleApproximationResidue a p :=
    (ZMod.natCast_eq_natCast_iff _ _ m).2 hmod
  have hpNat :
      (Rat.HeightOneSpectrum.primesEquiv
        (finiteAdeleDenominatorPlace a p) : ℕ) = (p : ℕ) := by
    exact congrArg Subtype.val
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
        ⟨p, Nat.prime_of_mem_primeFactors p.property⟩)
  calc
    PadicInt.toZModPow e
        (finiteAdeleApproximationNumerator a :
          ℤ_[Rat.HeightOneSpectrum.primesEquiv
            (finiteAdeleDenominatorPlace a p)]) =
        (finiteAdeleApproximationNumerator a :
          ZMod ((Rat.HeightOneSpectrum.primesEquiv
            (finiteAdeleDenominatorPlace a p) : ℕ) ^ e)) := by simp
    _ = (finiteAdeleApproximationResidue a p :
          ZMod ((Rat.HeightOneSpectrum.primesEquiv
            (finiteAdeleDenominatorPlace a p) : ℕ) ^ e)) := by
      rw [hpNat]
      exact hcast
    _ = PadicInt.toZModPow e
        (finiteAdeleScaledPadicIntAt a
          (finiteAdeleDenominatorPlace a p)) := by
      rfl

set_option maxHeartbeats 200000 in
private theorem finiteAdelePositiveDenominator_padic_norm
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) :
    ‖(finiteAdelePositiveDenominator a : ℚ_[p])‖ =
      (p : ℝ) ^
        (-((finiteAdelePositiveDenominator a).factorization p : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation]
  · rw [Padic.valuation_natCast,
      ← Nat.factorization_def _ (Nat.prime_of_mem_primeFactors p.property)]
  · exact_mod_cast finiteAdelePositiveDenominator_ne_zero a

set_option maxHeartbeats 200000 in
private theorem finiteAdeleScaledPadicInt_sub_numerator_norm_le
    (a : RationalFiniteAdele)
    (p : (finiteAdelePositiveDenominator a).primeFactors) :
    ‖finiteAdeleScaledPadicIntAt a (finiteAdeleDenominatorPlace a p) -
        (finiteAdeleApproximationNumerator a :
          ℤ_[Rat.HeightOneSpectrum.primesEquiv
            (finiteAdeleDenominatorPlace a p)])‖ ≤
      (p : ℝ) ^
        (-((finiteAdelePositiveDenominator a).factorization p : ℤ)) := by
  have hker :
      finiteAdeleScaledPadicIntAt a (finiteAdeleDenominatorPlace a p) -
          (finiteAdeleApproximationNumerator a :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv
              (finiteAdeleDenominatorPlace a p)]) ∈
        RingHom.ker (PadicInt.toZModPow
          ((finiteAdelePositiveDenominator a).factorization p)) := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (finiteAdeleApproximationNumerator_residue a p).symm
  have hspan :
      finiteAdeleScaledPadicIntAt a (finiteAdeleDenominatorPlace a p) -
          (finiteAdeleApproximationNumerator a :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv
              (finiteAdeleDenominatorPlace a p)]) ∈
        (Ideal.span {((Rat.HeightOneSpectrum.primesEquiv
          (finiteAdeleDenominatorPlace a p) : ℕ) :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv
              (finiteAdeleDenominatorPlace a p)]) ^
          (finiteAdelePositiveDenominator a).factorization p} :
            Ideal ℤ_[Rat.HeightOneSpectrum.primesEquiv
              (finiteAdeleDenominatorPlace a p)]) := by
    rw [← PadicInt.ker_toZModPow]
    exact hker
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hspan
  have hpNat :
      (Rat.HeightOneSpectrum.primesEquiv
        (finiteAdeleDenominatorPlace a p) : ℕ) = (p : ℕ) := by
    exact congrArg Subtype.val
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
        ⟨p, Nat.prime_of_mem_primeFactors p.property⟩)
  simpa only [hpNat] using hnorm

set_option maxHeartbeats 200000 in
private theorem finiteAdeleScaledPadicIntAt_coe
    (a : RationalFiniteAdele)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ((finiteAdeleScaledPadicIntAt a v :
        ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) :
          ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) =
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v) := by
  exact
    Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_apply v _

private theorem finiteAdeleApproximationNumerator_residue_at
    (a : RationalFiniteAdele)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvD : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∣
      finiteAdelePositiveDenominator a) :
    PadicInt.toZModPow
        ((finiteAdelePositiveDenominator a).factorization
          (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
        (finiteAdeleApproximationNumerator a :
          ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) =
      PadicInt.toZModPow
        ((finiteAdelePositiveDenominator a).factorization
          (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
        (finiteAdeleScaledPadicIntAt a v) := by
  have hpMem : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∈
      (finiteAdelePositiveDenominator a).primeFactors :=
    (Nat.mem_primeFactors).2
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).property, hvD,
        finiteAdelePositiveDenominator_ne_zero a⟩
  let pp : (finiteAdelePositiveDenominator a).primeFactors :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v : ℕ), hpMem⟩
  have hv : finiteAdeleDenominatorPlace a pp = v := by
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    exact Subtype.ext (by simp [finiteAdeleDenominatorPlace, pp])
  have h := finiteAdeleApproximationNumerator_residue a pp
  have htransport := hv ▸ h
  simpa only [pp] using htransport

private theorem finiteAdeleScaledPadicIntAt_sub_numerator_norm_le
    (a : RationalFiniteAdele)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvD : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∣
      finiteAdelePositiveDenominator a) :
    ‖finiteAdeleScaledPadicIntAt a v -
        (finiteAdeleApproximationNumerator a :
          ℤ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤
      (Rat.HeightOneSpectrum.primesEquiv v : ℝ) ^
        (-((finiteAdelePositiveDenominator a).factorization
          (Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ)) := by
  have hker :
      finiteAdeleScaledPadicIntAt a v -
          (finiteAdeleApproximationNumerator a :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) ∈
        RingHom.ker (PadicInt.toZModPow
          ((finiteAdelePositiveDenominator a).factorization
            (Rat.HeightOneSpectrum.primesEquiv v : ℕ))) := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (finiteAdeleApproximationNumerator_residue_at a v hvD).symm
  have hspan :
      finiteAdeleScaledPadicIntAt a v -
          (finiteAdeleApproximationNumerator a :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) ∈
        (Ideal.span {((Rat.HeightOneSpectrum.primesEquiv v : ℕ) :
          ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) ^
            (finiteAdelePositiveDenominator a).factorization
              (Rat.HeightOneSpectrum.primesEquiv v : ℕ)} :
          Ideal ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) := by
    rw [← PadicInt.ker_toZModPow]
    exact hker
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hspan

/-- Every rational finite adele differs from one diagonal rational point by
an everywhere-integral finite adele.  The rational point is constructed by
CRT from the prime-power residues of one common integral denominator. -/
theorem exists_rational_sub_mem_integralFiniteAdeleSubring
    (a : RationalFiniteAdele) :
    ∃ q : ℚ, a - algebraMap ℚ RationalFiniteAdele q ∈
      integralFiniteAdeleSubring := by
  let M := finiteAdelePositiveDenominator a
  let N := finiteAdeleApproximationNumerator a
  have hM : M ≠ 0 := finiteAdelePositiveDenominator_ne_zero a
  let q : ℚ := (N : ℚ) / (M : ℚ)
  refine ⟨q, ?_⟩
  intro v
  rw [mem_adicCompletionIntegers_iff_padic, PadicInt.mem_subring_iff]
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  have hscaled :
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
            ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v) -
          (N : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤
        ‖(M : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ := by
    by_cases hpM : p ∣ M
    · calc
        ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
              ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v) -
            (N : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ =
            ‖finiteAdeleScaledPadicIntAt a v -
              (N : ℤ_[Rat.HeightOneSpectrum.primesEquiv v])‖ := by
                rw [← finiteAdeleScaledPadicIntAt_coe]
                rfl
        _ ≤ (Rat.HeightOneSpectrum.primesEquiv v : ℝ) ^
            (-(M.factorization
              (Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ)) := by
          simpa only [M, N, p] using
            finiteAdeleScaledPadicIntAt_sub_numerator_norm_le a v
              (by simpa only [M, p] using hpM)
        _ = ‖(M : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ := by
          rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hM),
            Padic.valuation_natCast,
            ← Nat.factorization_def _
              (Rat.HeightOneSpectrum.primesEquiv v).property]
    · have hb :
          ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
            ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v)‖ ≤ 1 := by
        rw [← finiteAdeleScaledPadicIntAt_coe]
        exact PadicInt.norm_le_one (finiteAdeleScaledPadicIntAt a v)
      have hN :
          ‖(N : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤ 1 := by
        exact_mod_cast PadicInt.norm_le_one
          (N : ℤ_[Rat.HeightOneSpectrum.primesEquiv v])
      have hsub :
          ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
            ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v) -
            (N : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤ 1 := by
        rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (by
          simpa only [norm_neg, max_le_iff] using And.intro hb hN)
      have hcop : p.Coprime M :=
        (Rat.HeightOneSpectrum.primesEquiv v).property.coprime_iff_not_dvd.mpr
          hpM
      rw [(Padic.norm_natCast_eq_one_iff).2 hcop]
      exact hsub
  have hscale :
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
          ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v) =
        (M : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) *
          Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a v) := by
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        (algebraMap ℤ (v.adicCompletion ℚ)
          (finiteAdelePositiveDenominator a : ℤ) * a v) = _
    rw [map_mul]
    congr 1
    simp [M]
  have hMpadic :
      (M : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) ≠ 0 := by
    exact_mod_cast hM
  have hvalue :
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
          ((a - algebraMap ℚ RationalFiniteAdele q) v) =
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
              ((finiteAdeleScaledIntegral a : RationalFiniteAdele) v) -
            (N : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])) /
          (M : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) := by
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        (a v - algebraMap ℚ (v.adicCompletion ℚ) q) = _
    have hqmap :
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
            (algebraMap ℚ (v.adicCompletion ℚ) q) =
          algebraMap ℚ
            ℚ_[Rat.HeightOneSpectrum.primesEquiv v] q := by
      exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).commutes q
    rw [map_sub, hqmap, hscale]
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a v) -
        (((N : ℚ) / (M : ℚ) : ℚ) :
          ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) = _
    push_cast
    field_simp [hMpadic]
  rw [hvalue, norm_div]
  exact (div_le_one (norm_pos_iff.mpr hMpadic)).2 hscaled

/-- The canonical map `ℚ / ℤ → 𝔸_ℚ,f / Ẑ` is surjective. -/
theorem rationalModIntegerToFiniteAdeleModIntegral_surjective :
    Function.Surjective rationalModIntegerToFiniteAdeleModIntegral :=
  rationalModIntegerToFiniteAdeleModIntegral_surjective_iff.mpr
    exists_rational_sub_mem_integralFiniteAdeleSubring

/-- The rational diagonal gives the exact additive quotient identification
`ℚ / ℤ ≃+ 𝔸_ℚ,f / Ẑ`. -/
noncomputable def rationalModIntegerEquivFiniteAdeleModIntegral :
    RationalModInteger ≃+ RationalFiniteAdeleModIntegral :=
  AddEquiv.ofBijective rationalModIntegerToFiniteAdeleModIntegral
    ⟨rationalModIntegerToFiniteAdeleModIntegral_injective,
      rationalModIntegerToFiniteAdeleModIntegral_surjective⟩

@[simp]
theorem rationalModIntegerEquivFiniteAdeleModIntegral_apply
    (x : RationalModInteger) :
    rationalModIntegerEquivFiniteAdeleModIntegral x =
      rationalModIntegerToFiniteAdeleModIntegral x :=
  rfl

end PositiveDefiniteIntegralLattice
