import SMSFormula.RationalAdeleLinearAutHaarScalar

/-!
# The overlap integral, and the Haar scalar as a ratio of overlaps

The adelic orthogonal Haar invariance follows from the single overlap
`J(N) = int Phi(x) Phi(N x) dmu`.  Three of its four steps need no Fourier input at all, and they
are proved here for an arbitrary nonnegative test:

* `J(N)` is finite whenever the test is bounded by one with finite integral;
* `J(N)` is positive whenever the test is bounded below on an open neighbourhood of the origin,
  since the fixed Haar is positive on nonempty open sets and the matrix action is continuous;
* `J(g) = c(g) * J(g^-1)` for a matrix unit, by the defining transport of the Haar scalar --
  hence `c(g)` is the ratio of the two overlaps.

The one remaining analytic input is the transpose symmetry `J(N) = J(N^T)`, which follows
from one absolutely integrable double integral against the standard character and the
eigen identity `Phi^ = kappa Phi`.  It is not supplied here; it is carried as an explicit
hypothesis in the last two theorems.

Negative scope: no Fourier transform is computed, no eigenfunction is exhibited, and no adelic
orthogonal matrix is shown to preserve the Haar.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The overlap of a nonnegative test with its pullback along a full-adelic matrix. -/
def adelicOverlap (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (N : Matrix (Fin n) (Fin n) RationalAdele) : ℝ≥0∞ :=
  ∫⁻ x, Phi x * Phi (N.mulVec x) ∂(rationalAdeleCoordinateAddHaarMeasure n)

/-- A test bounded by one has overlap bounded by its own integral. -/
theorem adelicOverlap_le_lintegral {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hle : ∀ x, Phi x ≤ 1) (N : Matrix (Fin n) (Fin n) RationalAdele) :
    adelicOverlap Phi N ≤ ∫⁻ x, Phi x ∂(rationalAdeleCoordinateAddHaarMeasure n) := by
  refine lintegral_mono fun x ↦ ?_
  calc Phi x * Phi (N.mulVec x) ≤ Phi x * 1 := by
        exact mul_le_mul_right (hle _) _
    _ = Phi x := mul_one _

/-- Finiteness of the overlap. -/
theorem adelicOverlap_ne_top {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hle : ∀ x, Phi x ≤ 1)
    (hfin : (∫⁻ x, Phi x ∂(rationalAdeleCoordinateAddHaarMeasure n)) ≠ ⊤)
    (N : Matrix (Fin n) (Fin n) RationalAdele) :
    adelicOverlap Phi N ≠ ⊤ :=
  (lt_of_le_of_lt (adelicOverlap_le_lintegral hle N) (lt_top_iff_ne_top.2 hfin)).ne

/-- Positivity of the overlap, from a lower bound on an open neighbourhood of the origin.  The
fixed coordinate Haar is positive on every nonempty open set, and the matrix action is
continuous, so the intersection with the preimage still contains the origin. -/
theorem adelicOverlap_pos {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hmeas : Measurable Phi) {c : ℝ≥0∞} (hc : c ≠ 0) {U : Set (Fin n → RationalAdele)} (hU : IsOpen U)
    (h0 : (0 : Fin n → RationalAdele) ∈ U) (hUc : ∀ x ∈ U, c ≤ Phi x)
    (N : Matrix (Fin n) (Fin n) RationalAdele) :
    0 < adelicOverlap Phi N := by
  set mu := rationalAdeleCoordinateAddHaarMeasure n with hmu
  set V : Set (Fin n → RationalAdele) := U ∩ (fun x ↦ N.mulVec x) ⁻¹' U with hV
  have hVopen : IsOpen V :=
    hU.inter (hU.preimage (continuous_fullAdelicMatrixMulVec N))
  have hV0 : (0 : Fin n → RationalAdele) ∈ V := by
    refine ⟨h0, ?_⟩
    simp only [Set.mem_preimage, Matrix.mulVec_zero]
    exact h0
  have hVpos : 0 < mu V := hVopen.measure_pos mu ⟨0, hV0⟩
  have hbound : c * c * mu V ≤ adelicOverlap Phi N := by
    calc c * c * mu V = ∫⁻ _x in V, c * c ∂mu := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in V, Phi x * Phi (N.mulVec x) ∂mu := by
          refine setLIntegral_mono_ae
            ((hmeas.mul
              (hmeas.comp (continuous_fullAdelicMatrixMulVec N).measurable)).aemeasurable) ?_
          filter_upwards with x hx
          exact mul_le_mul' (hUc x hx.1) (hUc _ hx.2)
      _ ≤ adelicOverlap Phi N := setLIntegral_le_lintegral _ _
  exact lt_of_lt_of_le (by positivity) hbound

/-- The transport: for a matrix unit the overlap at `g` is the Haar scalar times the overlap at
`g` inverse. -/
theorem adelicOverlap_eq_haarScalar_mul_inv {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hmeas : Measurable Phi) (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    adelicOverlap Phi g.1 =
      fullAdelicMatrixUnitHaarScalar g * adelicOverlap Phi (g⁻¹).1 := by
  set mu := rationalAdeleCoordinateAddHaarMeasure n with hmu
  set h : (Fin n → RationalAdele) → ℝ≥0∞ :=
    fun z ↦ Phi z * Phi ((g⁻¹).1.mulVec z) with hh
  have hhmeas : Measurable h :=
    hmeas.mul (hmeas.comp (continuous_fullAdelicMatrixMulVec _).measurable)
  have hcancel : ∀ x, h (g.1.mulVec x) = Phi x * Phi (g.1.mulVec x) := by
    intro x
    have : (g⁻¹).1.mulVec (g.1.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hh]
    simp only [this]
    exact mul_comm _ _
  calc adelicOverlap Phi g.1 = ∫⁻ x, h (g.1.mulVec x) ∂mu := by
        refine lintegral_congr fun x ↦ ?_
        rw [hcancel x]
    _ = ∫⁻ z, h z ∂(Measure.map (fun x : Fin n → RationalAdele ↦ g.1.mulVec x) mu) := by
        rw [lintegral_map hhmeas (continuous_fullAdelicMatrixMulVec _).measurable]
    _ = ∫⁻ z, h z ∂((fullAdelicMatrixUnitHaarScalar g) • mu) := by
        rw [map_fullAdelicMatrixUnit_eq_smul]
    _ = fullAdelicMatrixUnitHaarScalar g * adelicOverlap Phi (g⁻¹).1 := by
        rw [lintegral_smul_measure]
        rfl

/-- The Haar scalar is a ratio of overlaps. -/
theorem haarScalar_eq_adelicOverlap_div {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hmeas : Measurable Phi) (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ)
    (hpos : 0 < adelicOverlap Phi (g⁻¹).1) (htop : adelicOverlap Phi (g⁻¹).1 ≠ ⊤) :
    (fullAdelicMatrixUnitHaarScalar g : ℝ≥0∞) =
      adelicOverlap Phi g.1 / adelicOverlap Phi (g⁻¹).1 := by
  rw [adelicOverlap_eq_haarScalar_mul_inv hmeas g, mul_div_assoc,
    ENNReal.div_self (ne_of_gt hpos) htop, mul_one]

/-- The transpose symmetry of the scalar, from the transpose symmetry of the overlap.  The
hypothesis `hsym` is the one remaining analytic input; it is not proved here. -/
theorem haarScalar_transpose_of_adelicOverlap_transpose
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi)
    (hsym : ∀ N : Matrix (Fin n) (Fin n) RationalAdele,
      adelicOverlap Phi N = adelicOverlap Phi N.transpose)
    (hpos : ∀ g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ, 0 < adelicOverlap Phi g.1)
    (htop : ∀ g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ, adelicOverlap Phi g.1 ≠ ⊤)
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    fullAdelicMatrixUnitHaarScalar (fullAdelicMatrixUnitTranspose g) =
      fullAdelicMatrixUnitHaarScalar g := by
  have hinvT : ((fullAdelicMatrixUnitTranspose g)⁻¹).1 = ((g⁻¹).1)ᵀ := rfl
  have h1 := haarScalar_eq_adelicOverlap_div hmeas (fullAdelicMatrixUnitTranspose g)
    (by rw [hinvT, ← hsym]; exact hpos g⁻¹) (by rw [hinvT, ← hsym]; exact htop g⁻¹)
  have h2 := haarScalar_eq_adelicOverlap_div hmeas g (hpos g⁻¹) (htop g⁻¹)
  rw [hinvT, ← hsym] at h1
  rw [fullAdelicMatrixUnitTranspose_val, ← hsym] at h1
  exact_mod_cast h1.trans h2.symm

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

open PositiveDefiniteIntegralLattice

/-- Adelic orthogonal Haar invariance, with its one analytic input explicit: a full-adelic orthogonal
matrix preserves the fixed coordinate Haar as soon as the overlap is transpose symmetric. -/
theorem fullAdelicOrthogonal_measurePreserving_of_adelicOverlap_transpose
    (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi)
    (hsym : ∀ N : Matrix (Fin n) (Fin n) RationalAdele,
      adelicOverlap Phi N = adelicOverlap Phi N.transpose)
    (hpos : ∀ g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ, 0 < adelicOverlap Phi g.1)
    (htop : ∀ g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ, adelicOverlap Phi g.1 ≠ ⊤)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  have hrecip := V.fullAdelicOrthogonal_haarScalar_transpose_mul_self g
  rw [haarScalar_transpose_of_adelicOverlap_transpose hmeas hsym hpos htop g.1] at hrecip
  have hsq : ((fullAdelicMatrixUnitHaarScalar g.1 : ℝ)) *
      (fullAdelicMatrixUnitHaarScalar g.1 : ℝ) = 1 := by
    exact_mod_cast congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) hrecip
  have hone : (fullAdelicMatrixUnitHaarScalar g.1 : ℝ) = 1 := by
    have hsqrt := Real.sqrt_mul_self (fullAdelicMatrixUnitHaarScalar g.1).coe_nonneg
    rw [hsq] at hsqrt
    simpa using hsqrt.symm
  refine (fullAdelicMatrixUnitHaarScalar_eq_one_iff g.1).1 ?_
  exact_mod_cast hone

end RationalQuadraticSpaceMatrix

end
