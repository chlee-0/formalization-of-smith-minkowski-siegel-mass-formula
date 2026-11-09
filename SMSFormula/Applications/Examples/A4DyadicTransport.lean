import SMSFormula.Applications.Examples.A4LocalDepth
import SMSFormula.Applications.Examples.DyadicCountModels

/-! The original A4 native quotient and the explicit characteristic-two model. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

def a4DyadicRepresentative (v : A4DyadicVector) : Fin 4 → ℤ := fun i => (v i).val

def a4DyadicVectorToQuotient (v : A4DyadicVector) :
    localDualQuotientTarget a4DyadicDenominator :=
  a4DyadicDenominator.mkQ (a4DyadicRepresentative v)

theorem a4DyadicVectorToQuotient_injective :
    Function.Injective a4DyadicVectorToQuotient := by
  intro v w h
  have hc := (a4Dyadic_quotient_eq_iff _ _).mp h
  ext i
  simpa [a4DyadicRepresentative] using hc i

theorem a4DyadicVectorToQuotient_surjective :
    Function.Surjective a4DyadicVectorToQuotient := by
  intro z
  obtain ⟨x, rfl⟩ := a4DyadicDenominator.mkQ_surjective z
  refine ⟨fun i => (x i : ZMod 2), (a4Dyadic_quotient_eq_iff _ _).mpr ?_⟩
  intro i
  simp [a4DyadicRepresentative]

def a4DyadicQuotientEquiv : A4DyadicVector ≃
    localDualQuotientTarget a4DyadicDenominator :=
  Equiv.ofBijective a4DyadicVectorToQuotient
    ⟨a4DyadicVectorToQuotient_injective, a4DyadicVectorToQuotient_surjective⟩

abbrev A4DyadicFamily := (A4DyadicVector × A4DyadicVector) ×
  (A4DyadicVector × A4DyadicVector)

def a4DyadicColumns (t : A4DyadicFamily) : Fin 4 → A4DyadicVector :=
  ![t.1.1, t.1.2, t.2.1, t.2.2]

def a4DyadicImage (t : A4DyadicFamily) (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ∑ j, x j • a4DyadicRepresentative (a4DyadicColumns t j)

theorem a4DyadicImage_quotientMap (t : A4DyadicFamily) (x : Fin 4 → ℤ) :
    quotientBasisFamilyMap a4DyadicDenominator
      (fun j => a4DyadicVectorToQuotient (a4DyadicColumns t j)) x =
      a4DyadicDenominator.mkQ (a4DyadicImage t x) := by
  unfold quotientBasisFamilyMap a4DyadicVectorToQuotient a4DyadicImage
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]

def a4DyadicMatrix (t : A4DyadicFamily) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => a4DyadicColumns t j i

theorem a4DyadicImage_reduces (t : A4DyadicFamily) (x : Fin 4 → ℤ) :
    (fun i => (a4DyadicImage t x i : ZMod 2)) =
      (a4DyadicMatrix t).mulVec (fun j => (x j : ZMod 2)) := by
  ext i
  simp [a4DyadicImage, a4DyadicRepresentative, a4DyadicMatrix,
    Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

def a4IntegerQ (x : Fin 4 → ℤ) : ℤ :=
  x 0^2+x 1^2+x 2^2+x 3^2-x 0*x 1-x 1*x 2-x 2*x 3

theorem a4IntegerQ_cast (x : Fin 4 → ℤ) :
    (a4IntegerQ x : ZMod 2) = a4DyadicQ (fun i => (x i : ZMod 2)) := by
  simp [a4IntegerQ, a4DyadicQ]

theorem a4_latticeOfPolarForm_integer_quadForm (x : Fin 4 → ℤ) :
    a4.latticeOfPolarForm.quadForm x = 2 * a4IntegerQ x := by
  have hx : x = ![x 0,x 1,x 2,x 3] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  rw [a4_latticeOfPolarForm_quadForm]
  rfl

theorem a4Dyadic_double_eq_iff (a b : ℤ) :
    ((2*a : ℤ) : ZMod 4) = (2*b : ℤ) ↔ (a : ZMod 2) = b := by
  have h := zmod_pow_mul_eq_zero_iff_of_le 2 2 1 (by decide) (a-b)
  norm_num only [primePowModulus, Nat.reducePow, Nat.cast_ofNat, Nat.reduceSub] at h
  simpa only [mul_sub, Int.cast_sub, sub_eq_zero] using h

theorem a4Dyadic_preserves_iff (t : A4DyadicFamily) :
    (∀ x : Fin 4 → ℤ,
      (a4.latticeOfPolarForm.quadForm (a4DyadicImage t x) : ZMod 4) =
        (a4.latticeOfPolarForm.quadForm x : ZMod 4)) ↔
      ∀ x : A4DyadicVector, a4DyadicQ ((a4DyadicMatrix t).mulVec x) = a4DyadicQ x := by
  have hstep (x : Fin 4 → ℤ) :
      (a4.latticeOfPolarForm.quadForm (a4DyadicImage t x) : ZMod 4) =
        (a4.latticeOfPolarForm.quadForm x : ZMod 4) ↔
      a4DyadicQ ((a4DyadicMatrix t).mulVec (fun i => (x i : ZMod 2))) =
        a4DyadicQ (fun i => (x i : ZMod 2)) := by
    rw [a4_latticeOfPolarForm_integer_quadForm, a4_latticeOfPolarForm_integer_quadForm,
      a4Dyadic_double_eq_iff, a4IntegerQ_cast, a4IntegerQ_cast, a4DyadicImage_reduces]
  constructor
  · intro h x
    have hr := (hstep (a4DyadicRepresentative x)).mp (h _)
    simpa [a4DyadicRepresentative] using hr
  · intro h x
    exact (hstep x).mpr (h _)


theorem a4_vec_two {α : Type*} (a b c d : α) : (![a,b,c,d] : Fin 4 → α) 2 = c := rfl

theorem a4_vec_three {α : Type*} (a b c d : α) : (![a,b,c,d] : Fin 4 → α) 3 = d := rfl

def a4DyadicCoefficients (t : A4DyadicFamily) : Prop :=
  a4DyadicQ t.1.1 = 1 ∧ a4DyadicQ t.1.2 = 1 ∧
    a4DyadicQ t.2.1 = 1 ∧ a4DyadicQ t.2.2 = 1 ∧
    a4DyadicPair t.1.1 t.1.2 = 1 ∧ a4DyadicPair t.1.1 t.2.1 = 0 ∧
    a4DyadicPair t.1.1 t.2.2 = 0 ∧ a4DyadicPair t.1.2 t.2.1 = 1 ∧
    a4DyadicPair t.1.2 t.2.2 = 0 ∧ a4DyadicPair t.2.1 t.2.2 = 1

theorem a4Dyadic_expand (t : A4DyadicFamily) (x : A4DyadicVector) :
    a4DyadicQ ((a4DyadicMatrix t).mulVec x) =
      x 0^2*a4DyadicQ t.1.1 + x 1^2*a4DyadicQ t.1.2 +
      x 2^2*a4DyadicQ t.2.1 + x 3^2*a4DyadicQ t.2.2 +
      x 0*x 1*a4DyadicPair t.1.1 t.1.2 +
      x 0*x 2*a4DyadicPair t.1.1 t.2.1 +
      x 0*x 3*a4DyadicPair t.1.1 t.2.2 +
      x 1*x 2*a4DyadicPair t.1.2 t.2.1 +
      x 1*x 3*a4DyadicPair t.1.2 t.2.2 +
      x 2*x 3*a4DyadicPair t.2.1 t.2.2 := by
  simp [a4DyadicMatrix, a4DyadicColumns, a4DyadicQ, a4DyadicPair,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring_nf
  simp only [CharTwo.sub_eq_add]
  ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]

theorem a4Dyadic_preserves_iff_coefficients (t : A4DyadicFamily) :
    (∀ x : A4DyadicVector, a4DyadicQ ((a4DyadicMatrix t).mulVec x) = a4DyadicQ x) ↔
      a4DyadicCoefficients t := by
  constructor
  · intro h
    have h0 := h ![1,0,0,0]
    rw [a4Dyadic_expand, show a4DyadicQ ![1,0,0,0] = 1 by decide] at h0
    have h1 := h ![0,1,0,0]
    rw [a4Dyadic_expand, show a4DyadicQ ![0,1,0,0] = 1 by decide] at h1
    have h2 := h ![0,0,1,0]
    rw [a4Dyadic_expand, show a4DyadicQ ![0,0,1,0] = 1 by decide] at h2
    have h3 := h ![0,0,0,1]
    rw [a4Dyadic_expand, show a4DyadicQ ![0,0,0,1] = 1 by decide] at h3
    have h01 := h ![1,1,0,0]
    rw [a4Dyadic_expand, show a4DyadicQ ![1,1,0,0] = 1 by decide] at h01
    have h02 := h ![1,0,1,0]
    rw [a4Dyadic_expand, show a4DyadicQ ![1,0,1,0] = 0 by decide] at h02
    have h03 := h ![1,0,0,1]
    rw [a4Dyadic_expand, show a4DyadicQ ![1,0,0,1] = 0 by decide] at h03
    have h12 := h ![0,1,1,0]
    rw [a4Dyadic_expand, show a4DyadicQ ![0,1,1,0] = 1 by decide] at h12
    have h13 := h ![0,1,0,1]
    rw [a4Dyadic_expand, show a4DyadicQ ![0,1,0,1] = 0 by decide] at h13
    have h23 := h ![0,0,1,1]
    rw [a4Dyadic_expand, show a4DyadicQ ![0,0,1,1] = 1 by decide] at h23
    norm_num [a4_vec_two, a4_vec_three] at h0 h1 h2 h3 h01 h02 h03 h12 h13 h23
    refine ⟨h0, h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0, h1] at h01
      simpa only [CharTwo.add_self_eq_zero, zero_add] using h01
    · rw [h0, h2] at h02
      simpa only [CharTwo.add_self_eq_zero, zero_add] using h02
    · rw [h0, h3] at h03
      simpa only [CharTwo.add_self_eq_zero, zero_add] using h03
    · rw [h1, h2] at h12
      simpa only [CharTwo.add_self_eq_zero, zero_add] using h12
    · rw [h1, h3] at h13
      simpa only [CharTwo.add_self_eq_zero, zero_add] using h13
    · rw [h2, h3] at h23
      simpa only [CharTwo.add_self_eq_zero, zero_add] using h23
  · rintro ⟨h0,h1,h2,h3,h01,h02,h03,h12,h13,h23⟩ x
    rw [a4Dyadic_expand, h0,h1,h2,h3,h01,h02,h03,h12,h13,h23]
    simp only [a4DyadicQ, mul_one, mul_zero, add_zero, CharTwo.sub_eq_add]

theorem a4Dyadic_model_mem_iff (t : A4DyadicFamily) :
    t ∈ a4DyadicModelFamilies ↔ a4DyadicCoefficients t := by
  simp only [a4DyadicModelFamilies, a4DyadicShell, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, true_and, a4DyadicCoefficients]
  tauto

-- The membership interface avoids elaboration of the enumerated model.
attribute [local irreducible] a4DyadicModelFamilies


theorem a4Dyadic_native_mem_iff (t : A4DyadicFamily) :
    (fun j => a4DyadicVectorToQuotient (a4DyadicColumns t j)) ∈
      localDualQuotientSolutionFamilies a4.latticeOfPolarForm 2 2 a4DyadicDenominator
        (associatedBilinearDualPadicDenominatorIntegralPreimage_rank a4.latticeOfPolarForm 2 2) ↔
      ∀ x : Fin 4 → ℤ,
        (a4.latticeOfPolarForm.quadForm (a4DyadicImage t x) : ZMod 4) =
          (a4.latticeOfPolarForm.quadForm x : ZMod 4) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  constructor
  · intro h x
    exact h x _ (a4DyadicImage_quotientMap t x)
  · intro h x y hxy
    rw [a4DyadicImage_quotientMap] at hxy
    have hy : y - a4DyadicImage t x ∈ a4DyadicDenominator :=
      (Submodule.Quotient.eq a4DyadicDenominator).mp hxy.symm
    exact ((associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
      a4.latticeOfPolarForm 2 2
      a4_latticeOfPolarForm_dyadic_hensel_two.associated_bilinear_quadratic_depth).2 hy).trans (h x)

def a4DyadicModelToNative (t : {t // t ∈ a4DyadicModelFamilies}) :
    associatedBilinearDualQuotientSolutionFamily a4.latticeOfPolarForm 2 2 := by
  refine ⟨fun j => a4DyadicVectorToQuotient (a4DyadicColumns t.1 j), ?_⟩
  rw [a4Dyadic_native_mem_iff, a4Dyadic_preserves_iff, a4Dyadic_preserves_iff_coefficients]
  exact (a4Dyadic_model_mem_iff t.1).mp t.2

theorem a4DyadicModelToNative_bijective : Function.Bijective a4DyadicModelToNative := by
  constructor
  · intro v w h
    have hv : ∀ j, a4DyadicColumns v.1 j = a4DyadicColumns w.1 j := by
      intro j
      exact a4DyadicVectorToQuotient_injective
        (congr_fun (congrArg Subtype.val h) j)
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact hv 0
      · exact hv 1
    · apply Prod.ext
      · exact hv 2
      · exact hv 3
  · intro Y
    obtain ⟨v, hv⟩ := a4DyadicVectorToQuotient_surjective (Y.1 0)
    obtain ⟨w, hw⟩ := a4DyadicVectorToQuotient_surjective (Y.1 1)
    obtain ⟨z, hz⟩ := a4DyadicVectorToQuotient_surjective (Y.1 2)
    obtain ⟨u, hu⟩ := a4DyadicVectorToQuotient_surjective (Y.1 3)
    let t : A4DyadicFamily := ((v,w),(z,u))
    have hY : (fun j => a4DyadicVectorToQuotient (a4DyadicColumns t j)) = Y.1 := by
      ext j
      fin_cases j
      · exact hv
      · exact hw
      · exact hz
      · exact hu
    have hmem : t ∈ a4DyadicModelFamilies := by
      rw [a4Dyadic_model_mem_iff, ← a4Dyadic_preserves_iff_coefficients,
        ← a4Dyadic_preserves_iff, ← a4Dyadic_native_mem_iff, hY]
      exact Y.2
    refine ⟨⟨t,hmem⟩, ?_⟩
    apply Subtype.ext
    exact hY

theorem a4_native_count_two_two :
    associatedBilinearDualQuotientCount a4.latticeOfPolarForm 2 2 = 120 := by
  rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  calc
    _ = Nat.card {t // t ∈ a4DyadicModelFamilies} :=
      (Nat.card_congr (Equiv.ofBijective a4DyadicModelToNative
        a4DyadicModelToNative_bijective)).symm
    _ = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, a4DyadicModelFamilies_card]

theorem a4_density_two : normalizedLocalDensity a4.latticeOfPolarForm 2 = 15 := by
  rw [a4_density_two_eq_native_count, a4_native_count_two_two]
  norm_num

end MassFormulaReleaseExamples
