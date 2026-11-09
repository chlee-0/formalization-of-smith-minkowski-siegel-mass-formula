import SMSFormula.PadicCayleyTranslatedChartOverlapDifferential
import SMSFormula.PadicCayleyRestrictedPointwiseDifferential
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Strict differentiability of the p-adic Cayley maps

The forward and inverse Cayley formulas are analytic on their exact
domains, because the ring inverse is analytic at every unit of the complete
matrix algebra. Analyticity upgrades the already computed pointwise derivatives
to strict derivatives, which is the regularity mathlib's inverse function
theorem consumes over a complete nontrivially normed field. No chart, section,
inverse or measure is constructed here.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

/-- An analytic map with a known pointwise derivative has that derivative in
the strict sense. This is a uniqueness statement, not a new derivative. -/
theorem HasFDerivAt.hasStrictFDerivAt_of_analyticAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {x : E}
    (hf : HasFDerivAt f f' x) (ha : AnalyticAt 𝕜 f x) : HasStrictFDerivAt f f' x := by
  have h := ha.hasStrictFDerivAt
  rwa [hf.fderiv] at h

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/-- The forward Cayley formula is analytic throughout its source. -/
theorem analyticAt_padicCayleyForwardMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    AnalyticAt ℚ_[p] (padicCayleyForwardMatrix (ι := ι) p) X := by
  letI : CompleteSpace (Matrix ι ι ℚ_[p]) := FiniteDimensional.complete ℚ_[p] _
  change IsUnit (1 - X) at hX
  have hfun : padicCayleyForwardMatrix (ι := ι) p =
      fun Y ↦ (1 + Y) * Ring.inverse (1 - Y) := by
    funext Y
    simp only [padicCayleyForwardMatrix, nonsing_inv_eq_ringInverse]
  rw [hfun]
  have h1 : AnalyticAt ℚ_[p] (Ring.inverse : Matrix ι ι ℚ_[p] → Matrix ι ι ℚ_[p]) (1 - X) := by
    simpa only [hX.unit_spec] using analyticAt_inverse (𝕜 := ℚ_[p]) hX.unit
  have hden : AnalyticAt ℚ_[p] (fun Y : Matrix ι ι ℚ_[p] ↦ 1 - Y) X :=
    analyticAt_const.sub analyticAt_id
  have hinv : AnalyticAt ℚ_[p] (fun Y : Matrix ι ι ℚ_[p] ↦ Ring.inverse (1 - Y)) X :=
    h1.comp hden
  exact (analyticAt_const.add analyticAt_id).mul hinv

set_option backward.isDefEq.respectTransparency false in
/-- The inverse Cayley formula is analytic throughout its domain. -/
theorem analyticAt_padicCayleyInverseMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    AnalyticAt ℚ_[p] (padicCayleyInverseMatrix (ι := ι) p) g := by
  letI : CompleteSpace (Matrix ι ι ℚ_[p]) := FiniteDimensional.complete ℚ_[p] _
  change IsUnit (g + 1) at hg
  have hfun : padicCayleyInverseMatrix (ι := ι) p =
      fun h ↦ Ring.inverse (h + 1) * (h - 1) := by
    funext h
    simp only [padicCayleyInverseMatrix, nonsing_inv_eq_ringInverse]
  rw [hfun]
  have h1 : AnalyticAt ℚ_[p] (Ring.inverse : Matrix ι ι ℚ_[p] → Matrix ι ι ℚ_[p]) (g + 1) := by
    simpa only [hg.unit_spec] using analyticAt_inverse (𝕜 := ℚ_[p]) hg.unit
  have hden : AnalyticAt ℚ_[p] (fun h : Matrix ι ι ℚ_[p] ↦ h + 1) g :=
    analyticAt_id.add analyticAt_const
  have hinv : AnalyticAt ℚ_[p] (fun h : Matrix ι ι ℚ_[p] ↦ Ring.inverse (h + 1)) g :=
    AnalyticAt.comp (g := Ring.inverse) (f := fun h : Matrix ι ι ℚ_[p] ↦ h + 1) h1 hden
  exact hinv.mul (analyticAt_id.sub analyticAt_const)

/-- The forward Cayley derivative is a strict derivative on the source. -/
theorem hasStrictFDerivAt_padicCayleyForwardMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    HasStrictFDerivAt (padicCayleyForwardMatrix (ι := ι) p)
      (padicCayleyForwardDerivative p X) X :=
  (hasFDerivAt_padicCayleyForwardMatrix p X hX).hasStrictFDerivAt_of_analyticAt
    (analyticAt_padicCayleyForwardMatrix p X hX)

/-- The inverse Cayley derivative is a strict derivative on the domain. -/
theorem hasStrictFDerivAt_padicCayleyInverseMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    HasStrictFDerivAt (padicCayleyInverseMatrix (ι := ι) p)
      (padicCayleyInverseDerivative p g) g :=
  (hasFDerivAt_padicCayleyInverseMatrix p g hg).hasStrictFDerivAt_of_analyticAt
    (analyticAt_padicCayleyInverseMatrix p g hg)

/-- The restricted skew-adjoint Cayley map has its restricted derivative
in the strict sense at every point of the restricted source. -/
theorem hasStrictFDerivAt_skewAdjointPadicCayleyForwardMatrix
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    HasStrictFDerivAt (skewAdjointPadicCayleyForwardMatrix F p)
      (skewAdjointPadicCayleyForwardDerivative F p X) X := by
  have hcomp := (hasStrictFDerivAt_padicCayleyForwardMatrix p
    (X : Matrix ι ι ℚ_[p]) hX).comp X (skewAdjointPadicAmbientInclusion F p).hasStrictFDerivAt
  convert hcomp using 1

end Matrix
