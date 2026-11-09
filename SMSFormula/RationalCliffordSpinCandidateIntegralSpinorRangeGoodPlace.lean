import SMSFormula.RationalSpecialOrthogonalTamagawa
import SMSFormula.RationalTernaryHasseMinkowski

/-!
# Good places for the restricted integral Spinor range

This file isolates the elementary finite bad-place bookkeeping needed by the
restricted integral spinor-range calculation.  Outside the named set, the
rational form presentation has an odd, unimodular p-adic integral model.  The
rank-at-least-two hypothesis is kept as a separate hypothesis because it is
global and cannot be obtained by excluding finitely many places.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance cliffordSpinCandidateGoodPlacePackagingDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cliffordSpinCandidateGoodPlacePackagingPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## The finite odd-unimodular bad set -/

/-- The rational primes supporting two, a displayed form-matrix denominator,
or the numerator or denominator of its determinant.  The matrix-pair API is
applied to the same form twice so that its existing good-prime theorem can be
used literally. -/
def cliffordSpinCandidateOddUnimodularBadPrimes :
    Finset {p : ℕ // p.Prime} :=
  ((Rat.matrixPairBadPrimeSet V.pairingMatrix V.pairingMatrix).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈
              (Rat.matrixPairBadPrimeSupportNat
                V.pairingMatrix V.pairingMatrix).primeFactors from p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

@[simp]
theorem mem_cliffordSpinCandidateOddUnimodularBadPrimes_iff
    (p : {p : ℕ // p.Prime}) :
    p ∈ V.cliffordSpinCandidateOddUnimodularBadPrimes ↔
      p.1 ∈ Rat.matrixPairBadPrimeSet V.pairingMatrix V.pairingMatrix := by
  rw [cliffordSpinCandidateOddUnimodularBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

/-- Height-one version of the odd-unimodular bad-prime set. -/
def cliffordSpinCandidateOddUnimodularBadPlaces :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.cliffordSpinCandidateOddUnimodularBadPrimes.map
    Rat.HeightOneSpectrum.primesEquiv.symm.toEmbedding

@[simp]
theorem mem_cliffordSpinCandidateOddUnimodularBadPlaces_iff
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    v ∈ V.cliffordSpinCandidateOddUnimodularBadPlaces ↔
      (Rat.HeightOneSpectrum.primesEquiv v).1 ∈
        Rat.matrixPairBadPrimeSet V.pairingMatrix V.pairingMatrix := by
  simp only [cliffordSpinCandidateOddUnimodularBadPlaces,
    Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨p, hp, hpv⟩
    have hpv' : p = Rat.HeightOneSpectrum.primesEquiv v := by
      simpa using congrArg Rat.HeightOneSpectrum.primesEquiv hpv
    subst p
    exact
      (V.mem_cliffordSpinCandidateOddUnimodularBadPrimes_iff
        (Rat.HeightOneSpectrum.primesEquiv v)).1 hp
  · intro hp
    refine ⟨Rat.HeightOneSpectrum.primesEquiv v, ?_, ?_⟩
    · exact
        (V.mem_cliffordSpinCandidateOddUnimodularBadPrimes_iff
          (Rat.HeightOneSpectrum.primesEquiv v)).2 hp
    · simp

/-! ## Exact good-place certificate -/

/-- The precise local hypotheses used by the intended restricted spinor-range
theorem: rank at least two, odd residue characteristic, and an integral
unimodular model whose scalar extension is the displayed rational form. -/
structure CliffordSpinCandidateIntegralSpinorRangeGoodPlace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) where
  rank_atLeastTwo : 2 ≤ n
  prime_ne_two : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2
  integralFormMatrix :
    Matrix (Fin n) (Fin n)
      ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  integralFormMatrix_map :
    integralFormMatrix.map PadicInt.Coe.ringHom =
      V.pairingMatrix.map
        (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
  integralFormMatrix_isSymm : integralFormMatrix.IsSymm
  integralFormMatrix_det_isUnit : IsUnit integralFormMatrix.det

/-- Outside the named finite set, every rational form presentation of rank at
least two supplies the exact odd-unimodular local certificate. -/
noncomputable def cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
    (hn : 2 ≤ n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces) :
    V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  have hpnot :
      p ∉ Rat.matrixPairBadPrimeSet V.pairingMatrix V.pairingMatrix := by
    intro hp
    exact hv
      ((V.mem_cliffordSpinCandidateOddUnimodularBadPlaces_iff v).2 hp)
  obtain
      ⟨hp_two, hden, _hden', hdetnum, hdetden, _hdetnum', _hdetden'⟩ :=
    Rat.matrixPairGoodPrimeData
      V.pairingMatrix V.pairingMatrix V.form_det_ne_zero V.form_det_ne_zero
      (Rat.HeightOneSpectrum.primesEquiv v).2 hpnot
  let Fz : Matrix (Fin n) (Fin n) ℤ_[p] :=
    Rat.rationalMatrixPadicInt V.pairingMatrix hden
  refine
    { rank_atLeastTwo := hn
      prime_ne_two := hp_two
      integralFormMatrix := Fz
      integralFormMatrix_map := ?_
      integralFormMatrix_isSymm := ?_
      integralFormMatrix_det_isUnit := ?_ }
  · exact Rat.rationalMatrixPadicInt_map V.pairingMatrix hden
  · exact
      Rat.rationalMatrixPadicInt_isSymm
        V.pairingMatrix V.form_symm hden
  · exact
      Rat.rationalMatrixPadicInt_det_isUnit
        V.pairingMatrix V.form_det_ne_zero hden hdetnum hdetden

end RationalQuadraticSpaceMatrix
