import SMSFormula.Applications.Examples.Inputs
import SMSFormula.LocalDensity
import SMSFormula.StandardAxiomsGuard

/-! Native local depths for the actual integral A4 integral model. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

def a4DualNumerator {R : Type*} [CommRing R] (z : Fin 4 → R) : R :=
  2*z 0^2 + 3*z 1^2 + 3*z 2^2 + 2*z 3^2 + 3*z 0*z 1 + 2*z 0*z 2 +
    z 0*z 3 + 4*z 1*z 2 + 2*z 1*z 3 + 3*z 2*z 3

theorem a4_latticeOfPolarForm_pairingDeterminant :
    a4.latticeOfPolarForm.pairingDeterminant = 5 := by decide

theorem a4_latticeOfPolarForm_pairingDeterminant_val_two :
    padicValInt 2 a4.latticeOfPolarForm.pairingDeterminant = 0 := by
  rw [a4_latticeOfPolarForm_pairingDeterminant]
  exact padicValInt.eq_zero_of_not_dvd (by norm_num)

theorem a4_latticeOfPolarForm_dual_coordinates (y : Fin 4 → ℚ_[2]) :
    (a4.latticeOfPolarForm.pairingMatrix_padicField 2).mulVec y =
      ![2*y 0-y 1, -y 0+2*y 1-y 2, -y 1+2*y 2-y 3, -y 2+2*y 3] := by
  change (a4Polar.map (Int.cast : ℤ → ℚ_[2])).mulVec y = _
  ext i
  fin_cases i <;> simp [a4Polar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem a4_latticeOfPolarForm_padic_quadForm (y : Fin 4 → ℚ_[2]) :
    a4.latticeOfPolarForm.quadForm_padicField 2 y =
      2*(y 0^2+y 1^2+y 2^2+y 3^2-y 0*y 1-y 1*y 2-y 2*y 3) := by
  rw [quadForm_padicField, a4_latticeOfPolarForm_dual_coordinates]
  simp [dotProduct, Fin.sum_univ_succ]
  ring

/-- The half-polar dual already has even quadratic values at two. -/
theorem a4_latticeOfPolarForm_quadratic_depth_zero :
    a4.latticeOfPolarForm.IsHenselQuadraticDepth 2 0 := by
  intro y hy
  let z : Fin 4 → ℤ_[2] := fun i => ⟨_, hy i⟩
  have h5 : IsUnit (5 : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff]
    exact (PadicInt.norm_natCast_eq_one_iff (p := 2)).2 (by decide)
  let u : ℤ_[2]ˣ := h5.unit
  have hu : (u : ℤ_[2]) = 5 := h5.unit_spec
  have hi : (5 : ℤ_[2]) * (↑u⁻¹ : ℤ_[2]) = 1 := by rw [← hu]; simp
  have hpoly : (5 : ℚ_[2]) * a4.latticeOfPolarForm.quadForm_padicField 2 y =
      2 * a4DualNumerator (fun i => (z i : ℚ_[2])) := by
    have hz (i : Fin 4) : (z i : ℚ_[2]) =
        ![2*y 0-y 1, -y 0+2*y 1-y 2, -y 1+2*y 2-y 3, -y 2+2*y 3] i :=
      congr_fun (a4_latticeOfPolarForm_dual_coordinates y) i
    rw [a4_latticeOfPolarForm_padic_quadForm]
    simp only [a4DualNumerator, hz, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    ring
  refine ⟨(↑u⁻¹ : ℤ_[2]) * a4DualNumerator z, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (5 : ℚ_[2]) ≠ 0)
  simp only [pow_zero, one_mul]
  rw [hpoly]
  have hc : (5 : ℚ_[2]) * ((↑u⁻¹ : ℤ_[2]) : ℚ_[2]) = 1 :=
    congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hi
  have hcast : ((a4DualNumerator z : ℤ_[2]) : ℚ_[2]) =
      a4DualNumerator (fun i => (z i : ℚ_[2])) := by
    simp only [a4DualNumerator, PadicInt.coe_add, PadicInt.coe_mul,
      PadicInt.coe_pow]
    rfl
  simp only [PadicInt.coe_mul]
  change 2 * a4DualNumerator (fun i => (z i : ℚ_[2])) =
    5 * (2 * (((↑u⁻¹ : ℤ_[2]) : ℚ_[2]) * ((a4DualNumerator z : ℤ_[2]) : ℚ_[2])))
  rw [hcast]
  calc
    _ = (5 * ((↑u⁻¹ : ℤ_[2]) : ℚ_[2])) *
        (2 * a4DualNumerator (fun i => (z i : ℚ_[2]))) := by rw [hc, one_mul]
    _ = _ := by ring

theorem a4_latticeOfPolarForm_dyadic_hensel_two :
    IsLocalDensityHenselExponent a4.latticeOfPolarForm 2 2 := by
  exact
    { admissible := isLocalDensityAdmissibleExponent_of_one_le _ _ _ (by decide)
      lattice_depth := a4.latticeOfPolarForm.isHenselLatticeDepth_of_pairingDeterminant_val_lt 2 2
        (by rw [a4_latticeOfPolarForm_pairingDeterminant_val_two]; decide)
      quadratic_depth := IsHenselQuadraticDepth.succ _ 2 1
        (IsHenselQuadraticDepth.succ _ 2 0 a4_latticeOfPolarForm_quadratic_depth_zero)
      associated_bilinear_quadratic_depth :=
        a4_latticeOfPolarForm_quadratic_depth_zero.associatedBilinear_add_two_dyadic _ 0 }

def a4DyadicReduction : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _

theorem a4DyadicReduction_intCast (z : ℤ) :
    a4DyadicReduction (z : ZMod 4) = (z : ZMod 2) := by
  exact map_intCast a4DyadicReduction z

theorem a4Dyadic_kernel_residues : ∀ v : Fin 4 → ZMod 4,
    (((2 : ℤ) • a4Polar).map (Int.cast : ℤ → ZMod 4)).mulVec v = 0 ↔
      ∀ i, a4DyadicReduction (v i) = 0 := by
  decide +kernel

theorem a4_latticeOfPolarForm_associated_denominator_two_two :
    a4.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage 2 2 =
      primePowCoordinateSubmodule (n := 4) 2 1 := by
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker]
  ext x
  rw [LinearMap.mem_ker, mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  have h := a4Dyadic_kernel_residues (fun i => (x i : ZMod 4))
  have hm : a4.latticeOfPolarForm.polarGramMatrix = (2 : ℤ) • a4Polar := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a4, a4Polar,
      PositiveDefiniteIntegralQuadraticForm.latticeOfPolarForm, polarGramMatrix]
  rw [hm]
  change (((2 : ℤ) • a4Polar).map (Int.cast : ℤ → ZMod 4)).mulVec
      (fun i => (x i : ZMod 4)) = 0 ↔ _
  simpa only [a4DyadicReduction_intCast] using h

abbrev a4DyadicDenominator :=
  a4.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage 2 2

theorem a4Dyadic_quotient_eq_iff (x y : Fin 4 → ℤ) :
    a4DyadicDenominator.mkQ x = a4DyadicDenominator.mkQ y ↔
      ∀ i, (x i : ZMod 2) = y i := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  unfold a4DyadicDenominator
  rw [Submodule.Quotient.eq, a4_latticeOfPolarForm_associated_denominator_two_two,
    mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  simp only [Pi.sub_apply, Int.cast_sub, sub_eq_zero]
  rfl

theorem a4_local_polarDeterminant : a4.latticeOfPolarForm.polarDeterminant = 80 := by
  decide

theorem a4_latticeOfPolarForm_polarDeterminant_val_two :
    padicValInt 2 a4.latticeOfPolarForm.polarDeterminant = 4 := by
  have h16 : padicValInt 2 (16 : ℤ) = 4 := by
    change padicValInt 2 ((2 ^ 4 : ℕ) : ℤ) = 4
    rw [padicValInt.of_nat, padicValNat.prime_pow]
  rw [a4_local_polarDeterminant, show (80 : ℤ) = 16 * 5 by norm_num,
    padicValInt.mul (by norm_num : (16 : ℤ) ≠ 0) (by norm_num : (5 : ℤ) ≠ 0),
    h16, padicValInt.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℤ) ∣ 5)]

/-- The independent half and dyadic diagonal factors are retained. -/
theorem a4_density_two_eq_native_count :
    normalizedLocalDensity a4.latticeOfPolarForm 2 =
      (associatedBilinearDualQuotientCount a4.latticeOfPolarForm 2 2 : ℝ) / 8 := by
  rw [normalizedLocalDensity_eq_associatedBilinearDualQuotientCount
    a4.latticeOfPolarForm 2 2 a4_latticeOfPolarForm_dyadic_hensel_two]
  have hfactor : gramDetPadicNormFactor a4.latticeOfPolarForm 2 = 64 := by
    rw [gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq a4.latticeOfPolarForm 2 4
      (by rw [polarDeterminant_padic_norm_eq_padicValInt, a4_latticeOfPolarForm_polarDeterminant_val_two])]
    norm_num [gramDetPadicValuationFactor, Real.rpow_natCast]
  rw [hfactor]
  norm_num [twoPadicNormInvPow, localDensityDenominatorExponent]
  ring

end MassFormulaReleaseExamples
