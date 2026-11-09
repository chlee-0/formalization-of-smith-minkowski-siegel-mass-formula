import SMSFormula.AdelicGaussianOrbitRatioEulerCancelled
import SMSFormula.AdelicGaussianPolarShellDifferentialScales
import SMSFormula.ThetaShellWeightElimination
import SMSFormula.AdelicGaussianRealShellFactor
import SMSFormula.RationalCliffordGeneralSpinHorizontalOrbitMassValue
import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicHaarFactor

/-!
# The explicit shell weight with a rational archimedean factor

In the explicit one-shell weight (`exists_representedNormTheta_mul_weight_eq`) the archimedean data
`Re d_∞(a) · μ_W(SO_W(ℝ)) / μ_B(SO_B(ℝ))` are replaced by `|q_a|_∞` with the nonzero rational
`q_a = e_W / (2 · e_B · det E · det F_L)` (`AdelicGaussianRealShellFactor`):

Also the presentation Haar scalar `c_G` is replaced by the residual baseline-weight ratio
`w_B(S')/w_V(S')` (`blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio`)
on any supplied presentation support `S'`:

`Θ_a · (b_W τ_V (w_B/w_V)(S') ∏_E δ ∏_E vol_W · |q_a|_∞ · ∏_B s_W / (∏_B D ∏_B s_B))
  = b_V τ_W d_Φ(a) ∏_E vol_V`.

No Γ-value, power of `π`, square root, real group mass or real presentation modulus remains in the
weight.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance oswrDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance oswrPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance oswrPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance oswrPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Replacing `R · μ_W / μ_B` by `E / C` when `R · μ_W · C = μ_B · E`. -/
theorem _root_.ENNReal.shellWeight_archimedean_replace {A R y₁ y₂ μW μB SW SB D C Ew : ℝ≥0∞}
    (hR : R * μW * C = μB * Ew) (hB0 : μB ≠ 0) (hBt : μB ≠ ⊤) (hC0 : C ≠ 0) (hCt : C ≠ ⊤) :
    A * R * y₁ * y₂ * (μW * SW) / (D * (μB * SB)) = A * y₁ * y₂ * (Ew / C) * SW / (D * SB) := by
  have hRμ : R * μW = μB * (Ew / C) := by
    rw [← mul_div_assoc]
    exact (ENNReal.eq_div_iff hC0 hCt).mpr (by rw [mul_comm]; exact hR)
  calc A * R * y₁ * y₂ * (μW * SW) / (D * (μB * SB)) =
        A * y₁ * y₂ * (Ew / C) * SW * μB / (D * SB * μB) := by
        congr 1
        · calc A * R * y₁ * y₂ * (μW * SW) = A * y₁ * y₂ * SW * (R * μW) := by ring
            _ = _ := by rw [hRμ]; ring
        · ring
    _ = _ := ENNReal.mul_div_mul_right _ _ hB0 hBt

section Ratio

local instance oswrShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance oswrShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < s + 2 + 1) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
