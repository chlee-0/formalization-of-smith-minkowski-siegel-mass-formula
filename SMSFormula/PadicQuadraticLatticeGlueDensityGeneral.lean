import SMSFormula.AdelicGaussianPresentationVolumeDensity

/-!
# Lattice glue equals the local density at every prime

The identification `ν(ℤ_p) · glue_M(ℤ_p^N) = δ_p(M)` (`latticeGlue_toReal_mul_eq_localResidueDensity`)
was proved only at odd `p ∤ M` through the level-one count.  Here it holds at every prime for every
`M ≠ 0`: the congruence-mass identity at large level `k` (`PadicInt.exists_card_eq_localDensity`),
the ball scaling `p^k ν(a + p^k ℤ_p) = ν(ℤ_p)` and the eventual constancy of the normalized
counts give `glue · ν(ℤ_p) · p^{kn} = #R_k`, i.e. `glue · ν(ℤ_p) = normalizedResidueCount(p^k) = δ_p(M)`.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory Metric Filter Matrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

local instance lgdPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance lgdPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- `ν(ℤ_p) · glue_M(ℤ_p^N) = δ_p(M)` at every prime, for every `M ≠ 0`. -/
theorem latticeGlue_toReal_mul_eq_localResidueDensity_of_ne_zero {n : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1))
    (p : ℕ) [Fact p.Prime] {M : ℤ} (hM0 : M ≠ 0)
    (point : ℕ → Fin (n + 1) → ℚ_[p])
    (hpoint : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point hpoint i)
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] :
    ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
        p point hpoint tH νs (Padic.unitHaar p (Fin (n + 1))) (((M : ℤ) : ℤ_[p]) : ℚ_[p])
          {x | ‖x.1‖ ≤ 1}).toReal * (νs (closedBall 0 1)).toReal =
      L.localResidueDensity M p := by
  have ha : ((((M : ℤ) : ℤ_[p]) : ℚ_[p])) ≠ 0 := by
    rw [padicIntCast_intCast_eq_algebraMap]
    exact (map_ne_zero _).mpr (by exact_mod_cast hM0)
  obtain ⟨k₀, hk₀⟩ := PadicInt.exists_card_eq_localDensity (L.pairingMatrix.map (Int.castRingHom ℤ_[p]))
    ((M : ℤ) : ℤ_[p]) ha point hpoint tH νs (Padic.unitHaar p (Fin (n + 1))) hcover
  obtain ⟨k, hkc, hk⟩ := ((L.eventually_normalizedResidueCount_eq_localResidueDensity p hM0).and
    (eventually_ge_atTop k₀)).exists
  have h := hk₀ k hk
  rw [Padic.unitHaar_unitCube, mul_one] at h
  have hb := PadicInt.pow_mul_measure_closedBall νs ((((M : ℤ) : ℤ_[p]) : ℚ_[p])) k
  have key : ((p : ℝ≥0∞) ^ k) ^ n * ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
      p point hpoint tH νs (Padic.unitHaar p (Fin (n + 1))) (((M : ℤ) : ℤ_[p]) : ℚ_[p])
        {x | ‖x.1‖ ≤ 1} * νs (closedBall 0 1)) =
      ((Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k) ↦
        r ⬝ᵥ ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.toZModPow k)) *ᵥ r =
          PadicInt.toZModPow k ((M : ℤ) : ℤ_[p]))).card : ℝ≥0∞) := by
    rw [← hb, ← h]
    push_cast
    ring
  have hGt := IntegralFiniteAdelePhase.padicSquareBranchAtlasGlue_integral_ne_top
    ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]))
    point hpoint tH νs (Padic.unitHaar p (Fin (n + 1))) hcover ha
  have hνt : νs (closedBall 0 1) ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
  have hreal := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  rw [← hkc, normalizedResidueCount, card_residueSet_eq_card_filter_padic L p M k, ← hreal]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  push_cast
  field_simp

end PositiveDefiniteIntegralLattice
