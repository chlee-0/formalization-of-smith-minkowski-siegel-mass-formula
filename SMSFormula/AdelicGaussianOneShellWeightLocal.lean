import SMSFormula.AdelicGaussianOneShellWeightRational
import SMSFormula.AdelicGaussianRationalShellFactorProductFormula
import SMSFormula.RationalCliffordGeneralSpinCentralFiberScalarLocalProduct
import SMSFormula.RationalQuadraticIsometrySpinCandidateFiniteCarrierTransport
import SMSFormula.ShellWeightLocalization

/-!
# The one-shell identity as a product of local terms over one finite set of places

On one supplied finite set `T` of places containing a presentation support, the dyadic place, both
odd-unimodular bad sets, the horizontal bad set `B = bad_B ∪ bad_W` and the support of `q_a`, with
the Euler-cancellation set `E := T` (as primes), the rational one-shell identity becomes

`Θ_a · τ_V · ∏_{v∈T} den_v = τ_W · d_Φ(a) · ∏_{v∈T} num_v`,

`den_v = (if v ∈ B then 1 else s_B(v)) · δ_v(a)`,  `num_v = ‖q_a‖_v · (if v ∈ B then D_v else s_W(v))`.

The central-fiber scalars `b_V, b_W` (`coe_..._eq_prod_of_subset`), the weight ratio `c_G`, the
Euler-cancellation volumes, the archimedean factor `|q_a|_∞ = ∏_T ‖q_a‖_v⁻¹` and all ambient data
(`vol_V`, `s_V`) and the idele conversion `m` cancel place by place (`ENNReal.shellWeight_localize`).
So the shell weight is `λ_a = (τ_W/τ_V) · ∏_{v∈T} num_v/den_v`: a product of explicit local terms of
the block `B = W ⊕ ⟨a⟩` and the lower space `W`.  Nothing is chosen; `C_a = 1` is not asserted.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance oswlDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance oswlPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance oswlPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance oswlPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Ratio

local instance oswlShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance oswlShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
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
