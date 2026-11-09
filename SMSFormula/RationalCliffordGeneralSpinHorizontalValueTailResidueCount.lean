import SMSFormula.PadicQuadraticLocalDensityTailProduct
import SMSFormula.RationalPadicPlaceNormProduct
import SMSFormula.RationalCliffordGeneralSpinHorizontalRestrictedPrincipalBlockCoherence
import SMSFormula.RationalAdeleSingularSeriesEulerProduct

/-!
# The ledger value tail is the good Euler product of the residue counts

At a good place `v` (outside a supplied value-multiplier block `T`), the normalized value
multiplier `u_v / |r|_v` is the local density `δ_p(a) = #R_1 / p^n` of the good-place Gram
matrix of `W ⊕ ⟨a⟩` at the value (`localDensity_toReal_eq_card_div`, no parity split, with
the atlas and Haar obtained inside the proof).

If an integral lattice `L` of rank `n + 1` has Gram matrix equal to the Gram matrix of
`W ⊕ ⟨a⟩` and `a = M` is an integer, the good-place Gram matrix and value are the `p`-adic
images of `L.pairingMatrix` and `M`, so `δ_p(a) = c_p(M)`, the good residue factor of `L`.  The
block `T` of places maps to a block `T'` of primes that contains `2`, the prime divisors of `M`
and of `det F`, and the two tails are the same infinite product:

```text
prod'_{v not in T} u_v / |r|_v  =  prod'_{p not in T'} c_p(M).
```

Combined with the singular-series factorization of the finite value density,

```text
d_fin(1_Zhat)(M) * (w_W(T)/w_V(T)) / prod_T |r|_v  =  B_{T'}(M) * c_ledger(T),
```

where `c_ledger(T)` is the value-multiplier scalar and `B_{T'}(M)` is the existing block
limit of the residue counts at the primes of `T`.  The lattice/presentation equality and the
block are supplied; no presentation is chosen.  Negative scope: `B_{T'}(M)` is not compared with
the block weights, no real factor is evaluated, and no E coefficient is asserted.
-/

noncomputable section

open MeasureTheory Set Metric Matrix Finset Filter Topology PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

local instance vtrPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
local instance vtrDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _
local instance vtrFactPrimePowOne (p : ℕ) [Fact p.Prime] : Fact (p ^ 1).Prime :=
  ⟨by rw [pow_one]; exact Fact.out⟩
local instance vtrPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] :=
  borel _
local instance vtrPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

section Lattice

variable {W a ha}

/-- On a supplied lattice presentation (`L.pairingMatrix` equal to the Gram matrix of
`W ⊕ ⟨a⟩`, and `a = M`), the good-place Gram matrix and value are the `p`-adic images of the
lattice data, so the two level-one counts agree. -/
theorem card_goodPlaceIntegralGram_eq_residueCount (L : PositiveDefiniteIntegralLattice (n + 1)) {M : ℤ}
    (hL : ∀ i j, ((L.pairingMatrix i j : ℤ) : ℚ) = (W.nonisotropicLastExtension a ha).pairingMatrix i j)
    (haM : a = M) (p : ℕ) [Fact p.Prime] (hp : p ∉ W.goodPlaceExceptionalPrimes a ha) :
    (univ.filter (fun r : Fin (n + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ ((W.goodPlaceIntegralGram a ha p hp).map (PadicInt.toZModPow 1)) *ᵥ r =
          PadicInt.toZModPow 1 (W.goodPlaceIntegralValue a ha p hp))).card =
      Nat.card {z : Fin (n + 1) → ZMod (p ^ 1) //
        L.zmodQuadForm (p ^ 1) z = ((M : ℤ) : ZMod (p ^ 1))} := by
  have hGram : W.goodPlaceIntegralGram a ha p hp = L.pairingMatrix.map (Int.castRingHom ℤ_[p]) := by
    ext i j
    apply Subtype.ext
    change algebraMap ℚ ℚ_[p] ((W.nonisotropicLastExtension a ha).pairingMatrix i j) =
      (((L.pairingMatrix i j : ℤ) : ℤ_[p]) : ℚ_[p])
    rw [← hL, PadicInt.coe_intCast, map_intCast]
  have hVal : W.goodPlaceIntegralValue a ha p hp = ((M : ℤ) : ℤ_[p]) := by
    apply Subtype.ext
    change algebraMap ℚ ℚ_[p] a = (((M : ℤ) : ℤ_[p]) : ℚ_[p])
    rw [haM, PadicInt.coe_intCast, map_intCast]
  rw [L.card_residueSet_eq_card_filter_padic p M 1, hGram, hVal]

/-- The block of primes underlying a block of places. -/
def placeBlockPrimes (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : Finset ℕ :=
  T.image fun v ↦ (Rat.HeightOneSpectrum.primesEquiv v).1

theorem mem_placeBlockPrimes_iff (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (Rat.HeightOneSpectrum.primesEquiv v).1 ∈ placeBlockPrimes T ↔ v ∈ T := by
  unfold placeBlockPrimes
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.1 h
    have : w = v := Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hwv)
    exact this ▸ hw
  · intro h
    exact Finset.mem_image_of_mem _ h

end Lattice

end RationalQuadraticSpaceMatrix

end
