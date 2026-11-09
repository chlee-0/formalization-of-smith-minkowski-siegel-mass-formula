import SMSFormula.RationalCliffordGeneralSpinProperThetaBound
import SMSFormula.RationalAdelePolarDualStabilizerInvariance
import SMSFormula.RationalAdeleCongruenceClassThetaInput
import SMSFormula.RationalFiniteAdeleQuadraticGaussAnnihilatorContainment

/-!
# Pointwise finiteness of the dual-carrier theta

The proper-domain bound is already closed for any stabilizer-invariant test, so the polar dual
carrier needs exactly one further input: pointwise finiteness of its concrete `SO` theta.  This
file supplies it, and therefore closes the raw finiteness chain for the dual carrier.

The mechanism is the adjugate of the integral Gram matrix.  The polar dual lattice is the
preimage of the standard finite lattice under the polar matrix; multiplying by the adjugate
shows that a dual vector scaled by the discriminant is already standard-integral.  Scaling a
rational vector by the discriminant is a bijection of the rational coordinate space, and on the
archimedean side it is the existing width change `b |-> b * N^2` of the polar Gaussian.  So the
dual-carrier theta is bounded, term by term after that bijection, by the existing standard
theta at the smaller width `a / N^2`, whose finiteness is already proved.

No new carrier, chart, section, representative system or Haar normalization is introduced: the
comparison is the literal reindexing `x |-> N x` of the same rational coordinate sum.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The dual-carrier test -/

/-- The dual-carrier analogue of the standard polar Gaussian--lattice test: the same
archimedean polar Gaussian, but carried by the polar dual lattice at the finite places. -/
def rationalAdeleVectorPolarGaussianDualTest (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (x : Fin n → RationalAdele) : ℂ :=
  polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
    L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator
      (rationalAdeleVectorFinitePart n x)

/-- Its literal nonnegative version. -/
def rationalAdeleVectorPolarGaussianDualTestENNReal (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (x : Fin n → RationalAdele) : ℝ≥0∞ :=
  ENNReal.ofReal ‖rationalAdeleVectorPolarGaussianDualTest L (a : ℂ) x‖

/-! ## Invariance under the real/integral stabilizer -/

/-- The dual-carrier test is fixed by a full-adelic orthogonal element whose finite component
stabilizes the standard lattice, exactly as the standard test is. -/
theorem rationalAdeleVectorPolarGaussianDualTest_concreteStabilizer_mulVec
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianDualTest L (a : ℂ) (h.1.1.1.1.mulVec x) =
      rationalAdeleVectorPolarGaussianDualTest L (a : ℂ) x := by
  let hr := (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h.1).1
  let hf := (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h.1).2
  have hhf : hf ∈ L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
    exact (L.mem_fullAdelicRealFiniteLatticeStabilizerSubgroup_iff h.1).mp h.2
  unfold rationalAdeleVectorPolarGaussianDualTest
  rw [L.rationalAdeleVectorRealPart_concreteFullAdelicSpecialOrthogonal_mulVec,
    L.rationalAdeleVectorFinitePart_concreteFullAdelicSpecialOrthogonal_mulVec]
  rw [RationalQuadraticSpaceMatrix.polarRealGaussian_realSpecialOrthogonal L (a : ℂ) hr]
  rw [L.finitePolarDualLatticeIndicator_stabilizer_mulVec (g := hf.1) hhf]

/-- The nonnegative dual-carrier test has the same stabilizer invariance. -/
theorem rationalAdeleVectorPolarGaussianDualTestENNReal_concreteStabilizer_mulVec
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianDualTestENNReal L a (h.1.1.1.1.mulVec x) =
      rationalAdeleVectorPolarGaussianDualTestENNReal L a x := by
  unfold rationalAdeleVectorPolarGaussianDualTestENNReal
  rw [L.rationalAdeleVectorPolarGaussianDualTest_concreteStabilizer_mulVec]

/-! ## The discriminant containment for the polar dual lattice -/

private theorem intMatrix_mulVec_mem_integralFiniteAdeleVectors
    (C : Matrix (Fin n) (Fin n) ℤ) {z : Fin n → RationalFiniteAdele}
    (hz : z ∈ integralFiniteAdeleVectors n) :
    (C.map (algebraMap ℤ RationalFiniteAdele)).mulVec z ∈ integralFiniteAdeleVectors n := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem integralFiniteAdeleSubring fun j _ ↦
    integralFiniteAdeleSubring.mul_mem
      (integer_mem_integralFiniteAdeleSubring (C i j)) (hz j)

/-- The containment: the polar dual lattice scaled by the discriminant is standard-integral.
The proof is the adjugate identity for the integral Gram matrix; no denominator basis, chart or
local representative is chosen. -/
theorem natAbsDisc_mul_mem_integralFiniteAdeleVectors_of_mem_finitePolarDualLattice
    (L : PositiveDefiniteIntegralLattice n) {y : Fin n → RationalFiniteAdele}
    (hy : y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice) :
    (fun i ↦ (L.polarDeterminant.natAbs : RationalFiniteAdele) * y i) ∈
      integralFiniteAdeleVectors n := by
  set Cfa : Matrix (Fin n) (Fin n) RationalFiniteAdele :=
    L.polarGramMatrix.map (algebraMap ℤ RationalFiniteAdele) with hCfa
  set Afa : Matrix (Fin n) (Fin n) RationalFiniteAdele :=
    L.polarGramMatrix.adjugate.map (algebraMap ℤ RationalFiniteAdele) with hAfa
  have hAC : Afa * Cfa = L.polarDeterminant • (1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) := by
    rw [hAfa, hCfa, ← Matrix.map_mul, Matrix.adjugate_mul]
    rw [show L.polarGramMatrix.det = L.polarDeterminant from rfl]
    simpa using Matrix.map_smul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant
      (fun a ↦ map_zsmul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant a)
      (1 : Matrix (Fin n) (Fin n) ℤ)
  have hstep : Afa.mulVec (Cfa.mulVec y) = L.polarDeterminant • y := by
    rw [Matrix.mulVec_mulVec, hAC, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcast : (L.polarDeterminant • y) = fun i ↦ (L.polarDeterminant.natAbs : RationalFiniteAdele) * y i := by
    have hnat : (L.polarDeterminant.natAbs : ℤ) = L.polarDeterminant :=
      Int.natAbs_of_nonneg (le_of_lt L.polarDeterminant_pos)
    have hz : (L.polarDeterminant : RationalFiniteAdele) = (L.polarDeterminant.natAbs : RationalFiniteAdele) := by
      calc (L.polarDeterminant : RationalFiniteAdele)
          = ((L.polarDeterminant.natAbs : ℤ) : RationalFiniteAdele) := by rw [hnat]
        _ = (L.polarDeterminant.natAbs : RationalFiniteAdele) := Int.cast_natCast _
    funext i
    rw [Pi.smul_apply, zsmul_eq_mul, hz]
  have hyC : Cfa.mulVec y ∈ integralFiniteAdeleVectors n := by
    have := hy
    rw [RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff,
      L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix] at this
    exact this
  rw [← hcast, ← hstep, hAfa]
  exact intMatrix_mulVec_mem_integralFiniteAdeleVectors L.polarGramMatrix.adjugate hyC

/-! ## Scaling a rational coordinate vector -/

private theorem mulVec_const_mul {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (c : R) (v : Fin n → R) :
    M.mulVec (fun i ↦ c * v i) = fun i ↦ c * M.mulVec v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

theorem rationalAdeleVectorDiagonal_const_mul (N : ℕ) (x : Fin n → ℚ) :
    rationalAdeleVectorDiagonal n (fun i ↦ (N : ℚ) * x i) =
      fun i ↦ (N : RationalAdele) * rationalAdeleVectorDiagonal n x i := by
  funext i
  simp [rationalAdeleVectorDiagonal]

theorem rationalAdeleVectorFinitePart_const_mul (N : ℕ) (y : Fin n → RationalAdele) :
    rationalAdeleVectorFinitePart n (fun i ↦ (N : RationalAdele) * y i) =
      fun i ↦ (N : RationalFiniteAdele) * rationalAdeleVectorFinitePart n y i := by
  funext i
  rfl

theorem rationalAdeleVectorRealPart_const_mul (N : ℕ) (y : Fin n → RationalAdele) :
    rationalAdeleVectorRealPart n (fun i ↦ (N : RationalAdele) * y i) =
      fun i ↦ (N : ℝ) * rationalAdeleVectorRealPart n y i := by
  funext i
  show rationalInfiniteAdeleContinuousAddEquivReal (((N : RationalAdele) * y i).1) = _
  have h1 : (((N : RationalAdele) * y i)).1 = N • (y i).1 := by
    rw [nsmul_eq_mul]
    rfl
  rw [h1, map_nsmul, nsmul_eq_mul]
  simp [rationalAdeleVectorRealPart]

/-! ## Pointwise finiteness of the dual-carrier theta -/

/-- The literal reindexing bijection `x ↦ N x` of the rational coordinate space. -/
private def natScaleEquiv {N : ℕ} (hN : N ≠ 0) : (Fin n → ℚ) ≃ (Fin n → ℚ) where
  toFun x := fun i ↦ (N : ℚ) * x i
  invFun x := fun i ↦ x i / (N : ℚ)
  left_inv := by
    intro x
    funext i
    field_simp
  right_inv := by
    intro x
    funext i
    field_simp

/-- The domination: at every rational coordinate point the dual-carrier summand is bounded by
the standard summand of width `a / polarDeterminant^2` at the discriminant-scaled point. -/
theorem rationalAdeleVectorPolarGaussianDualTestENNReal_le_natAbsDisc_scaled
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) (x : Fin n → ℚ) :
    rationalAdeleVectorPolarGaussianDualTestENNReal L a
        ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) ≤
      rationalAdeleVectorPolarGaussianLatticeTestENNReal L
        (a / (L.polarDeterminant.natAbs : ℝ) ^ 2)
        ((g⁻¹).1.1.1.mulVec
          (rationalAdeleVectorDiagonal n (fun i ↦ (L.polarDeterminant.natAbs : ℚ) * x i))) := by
  set N : ℕ := L.polarDeterminant.natAbs with hNdef
  have hN : N ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos)
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNC : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set v : Fin n → RationalAdele :=
    (g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x) with hv
  have hw : (g⁻¹).1.1.1.mulVec
      (rationalAdeleVectorDiagonal n (fun i ↦ (N : ℚ) * x i)) =
      fun i ↦ (N : RationalAdele) * v i := by
    rw [rationalAdeleVectorDiagonal_const_mul, mulVec_const_mul, hv]
  by_cases hmem : rationalAdeleVectorFinitePart n v ∈
      L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · have hint : rationalAdeleVectorFinitePart n
        (fun i ↦ (N : RationalAdele) * v i) ∈ integralFiniteAdeleVectors n := by
      rw [rationalAdeleVectorFinitePart_const_mul]
      exact L.natAbsDisc_mul_mem_integralFiniteAdeleVectors_of_mem_finitePolarDualLattice hmem
    have hgauss :
        polarRealGaussian L ((a / (N : ℝ) ^ 2 : ℝ) : ℂ)
            (rationalAdeleVectorRealPart n (fun i ↦ (N : RationalAdele) * v i)) =
          polarRealGaussian L (a : ℂ) (rationalAdeleVectorRealPart n v) := by
      rw [rationalAdeleVectorRealPart_const_mul,
        RationalQuadraticSpaceMatrix.polarRealGaussian_nsmul L _ hN]
      congr 1
      have : ((a / (N : ℝ) ^ 2 : ℝ) : ℂ) = (a : ℂ) / (N : ℂ) ^ 2 := by push_cast; ring
      rw [this]
      field_simp
    rw [hw]
    unfold rationalAdeleVectorPolarGaussianDualTestENNReal
      rationalAdeleVectorPolarGaussianLatticeTestENNReal
      rationalAdeleVectorPolarGaussianDualTest
      rationalAdeleVectorPolarGaussianLatticeTest
    rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ hmem,
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem hint,
      hgauss]
  · have hzero : rationalAdeleVectorPolarGaussianDualTestENNReal L a v = 0 := by
      unfold rationalAdeleVectorPolarGaussianDualTestENNReal
        rationalAdeleVectorPolarGaussianDualTest
      rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hmem]
      simp
    rw [hzero]
    exact zero_le

/-- The pointwise finiteness: every concrete special-orthogonal theta value of the dual-carrier
test is finite.  This is the analytic input the abstracted proper-domain bound was waiting
for. -/
theorem concreteSpecialOrthogonalTheta_polarGaussianDual_ne_top
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteSpecialOrthogonalTheta
        (rationalAdeleVectorPolarGaussianDualTestENNReal L a) g ≠ ⊤ := by
  set N : ℕ := L.polarDeterminant.natAbs with hNdef
  have hN : N ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos)
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  have ha' : 0 < a / (N : ℝ) ^ 2 := div_pos ha (by positivity)
  have hbound :
      L.concreteSpecialOrthogonalTheta
          (rationalAdeleVectorPolarGaussianDualTestENNReal L a) g ≤
        L.concreteFullAdelicSpecialOrthogonalPolarTheta (a / (N : ℝ) ^ 2) g := by
    unfold concreteSpecialOrthogonalTheta concreteFullAdelicSpecialOrthogonalPolarTheta
    have hre := (natScaleEquiv (n := n) hN).tsum_eq
      (fun y : Fin n → ℚ ↦
        rationalAdeleVectorPolarGaussianLatticeTestENNReal L (a / (N : ℝ) ^ 2)
          ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n y)))
    rw [← hre]
    exact ENNReal.tsum_le_tsum fun x ↦
      L.rationalAdeleVectorPolarGaussianDualTestENNReal_le_natAbsDisc_scaled a g x
  exact (lt_of_le_of_lt hbound
    (lt_top_iff_ne_top.2
      (L.concreteFullAdelicSpecialOrthogonalPolarTheta_ne_top hn ha' g))).ne

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The payoff: the raw cutoff integral of the dual-carrier theta against the existing unit
cutoff is finite, hence so is its cutoff-normalized functional.  Nothing is assumed beyond
positivity of the archimedean width: the stabilizer invariance and the pointwise theta
finiteness of the dual carrier are both proved above. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_polarGaussianDual_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    {a : ℝ} (ha : 0 < a) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv
        (rationalAdeleVectorPolarGaussianDualTestENNReal L a)
        RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_ne_top_of_stabilizerInvariant
    hr inst hcutoffProduct hconv
    (fun h x ↦
      L.rationalAdeleVectorPolarGaussianDualTestENNReal_concreteStabilizer_mulVec a h x)
    (fun g ↦
      L.concreteSpecialOrthogonalTheta_polarGaussianDual_ne_top (by omega) ha g)

end PositiveDefiniteIntegralLattice

end
