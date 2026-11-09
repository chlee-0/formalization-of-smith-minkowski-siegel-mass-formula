import SMSFormula.Applications.Examples.TernaryDyadicQuotient
import SMSFormula.Applications.Examples.DyadicCountModels

/-! Transport between the explicit dyadic model and the actual native quotient. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

abbrev ternaryDyadicDenominator :=
  ternaryLattice.associatedBilinearDualPadicDenominatorIntegralPreimage 2 4

def ternaryDyadicRepresentative (v : TernaryDyadicVector) : Fin 3 → ℤ :=
  ![(v.1 : ℤ), (v.2.1 : ℤ), (v.2.2 : ℤ)]

theorem ternaryDyadic_quotient_eq_iff (x y : Fin 3 → ℤ) :
    ternaryDyadicDenominator.mkQ x = ternaryDyadicDenominator.mkQ y ↔
      (x 0 : ZMod 8) = y 0 ∧ (x 1 : ZMod 4) = y 1 ∧
        (x 2 : ZMod 8) = y 2 := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  unfold ternaryDyadicDenominator
  rw [Submodule.Quotient.eq, ternary_associated_denominator_two_four,
    mem_diagonalPrimePowCoordinateSubmodule_iff]
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  change (((x 0 - y 0 : ℤ) : ZMod 8) = 0 ∧
    ((x 1 - y 1 : ℤ) : ZMod 4) = 0 ∧ ((x 2 - y 2 : ℤ) : ZMod 8) = 0) ↔ _
  simp only [Int.cast_sub, sub_eq_zero]

def ternaryDyadicVectorToQuotient (v : TernaryDyadicVector) :
    localDualQuotientTarget ternaryDyadicDenominator :=
  ternaryDyadicDenominator.mkQ (ternaryDyadicRepresentative v)

theorem ternaryDyadicVectorToQuotient_injective :
    Function.Injective ternaryDyadicVectorToQuotient := by
  intro v w h
  obtain ⟨h0, h1, h2⟩ := (ternaryDyadic_quotient_eq_iff _ _).mp h
  have hfin {m : ℕ} [NeZero m] (a b : Fin m)
      (h : (a.val : ZMod m) = b.val) : a = b := by
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hv
  apply Prod.ext
  · exact hfin _ _ (by simpa [ternaryDyadicRepresentative] using h0)
  · apply Prod.ext
    · exact hfin _ _ (by simpa [ternaryDyadicRepresentative] using h1)
    · exact hfin _ _ (by simpa [ternaryDyadicRepresentative] using h2)

theorem ternaryDyadicVectorToQuotient_surjective :
    Function.Surjective ternaryDyadicVectorToQuotient := by
  intro z
  obtain ⟨x, rfl⟩ := ternaryDyadicDenominator.mkQ_surjective z
  let v : TernaryDyadicVector :=
    (⟨(x 0 : ZMod 8).val, ZMod.val_lt _⟩,
      ⟨(x 1 : ZMod 4).val, ZMod.val_lt _⟩,
      ⟨(x 2 : ZMod 8).val, ZMod.val_lt _⟩)
  refine ⟨v, (ternaryDyadic_quotient_eq_iff _ _).mpr ?_⟩
  simp [v, ternaryDyadicRepresentative]

def ternaryDyadicQuotientEquiv : TernaryDyadicVector ≃
    localDualQuotientTarget ternaryDyadicDenominator :=
  Equiv.ofBijective ternaryDyadicVectorToQuotient
    ⟨ternaryDyadicVectorToQuotient_injective, ternaryDyadicVectorToQuotient_surjective⟩

theorem ternaryLattice_quadForm_coordinates (x : Fin 3 → ℤ) :
    ternaryLattice.quadForm x = x 0 ^ 2 + 2 * x 1 ^ 2 + 11 * x 2 ^ 2 := by
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  exact ternaryLattice_quadForm _ _ _

def ternaryDyadicImage (v w u : TernaryDyadicVector) (x : Fin 3 → ℤ) : Fin 3 → ℤ :=
  x 0 • ternaryDyadicRepresentative v + x 1 • ternaryDyadicRepresentative w +
    x 2 • ternaryDyadicRepresentative u

theorem ternaryDyadicImage_quadForm (v w u : TernaryDyadicVector) (x : Fin 3 → ℤ) :
    ternaryLattice.quadForm (ternaryDyadicImage v w u x) =
      x 0 ^ 2 * ternaryDyadicQ v + x 1 ^ 2 * ternaryDyadicQ w +
        x 2 ^ 2 * ternaryDyadicQ u +
        x 0 * x 1 * (2 * ternaryDyadicPair v w) +
        x 0 * x 2 * (2 * ternaryDyadicPair v u) +
        x 1 * x 2 * (2 * ternaryDyadicPair w u) := by
  rw [ternaryLattice_quadForm_coordinates]
  simp [ternaryDyadicImage, ternaryDyadicRepresentative, ternaryDyadicQ, ternaryDyadicPair]
  ring

theorem ternaryDyadicImage_quotientMap (v w u : TernaryDyadicVector) (x : Fin 3 → ℤ) :
    quotientBasisFamilyMap ternaryDyadicDenominator
      ![ternaryDyadicVectorToQuotient v, ternaryDyadicVectorToQuotient w,
        ternaryDyadicVectorToQuotient u] x =
      ternaryDyadicDenominator.mkQ (ternaryDyadicImage v w u x) := by
  unfold quotientBasisFamilyMap ternaryDyadicVectorToQuotient ternaryDyadicImage
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  simp [Fin.sum_univ_succ, add_assoc]

theorem ternaryDyadic_native_mem_iff (v w u : TernaryDyadicVector) :
    ![ternaryDyadicVectorToQuotient v, ternaryDyadicVectorToQuotient w,
        ternaryDyadicVectorToQuotient u] ∈
      localDualQuotientSolutionFamilies ternaryLattice 2 4 ternaryDyadicDenominator
        (associatedBilinearDualPadicDenominatorIntegralPreimage_rank ternaryLattice 2 4) ↔
      ∀ x : Fin 3 → ℤ,
        (ternaryLattice.quadForm (ternaryDyadicImage v w u x) : ZMod 16) =
          (ternaryLattice.quadForm x : ZMod 16) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  constructor
  · intro h x
    exact h x _ (ternaryDyadicImage_quotientMap v w u x)
  · intro h x y hxy
    rw [ternaryDyadicImage_quotientMap] at hxy
    have hy : y - ternaryDyadicImage v w u x ∈ ternaryDyadicDenominator :=
      (Submodule.Quotient.eq ternaryDyadicDenominator).mp hxy.symm
    exact ((associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
      ternaryLattice 2 4 ternary_dyadic_hensel_four.associated_bilinear_quadratic_depth).2
        hy).trans (h x)


/-- Six coefficients of the quadratic identity, in the original modulus 16. -/
def ternaryDyadicCoefficients (v w u : TernaryDyadicVector) : Prop :=
  (ternaryDyadicQ v : ZMod 16) = 1 ∧
    (ternaryDyadicQ w : ZMod 16) = 2 ∧
    (ternaryDyadicQ u : ZMod 16) = 11 ∧
    ((2 * ternaryDyadicPair v w : ℤ) : ZMod 16) = 0 ∧
    ((2 * ternaryDyadicPair v u : ℤ) : ZMod 16) = 0 ∧
    ((2 * ternaryDyadicPair w u : ℤ) : ZMod 16) = 0

theorem ternaryDyadic_preserves_iff_coefficients (v w u : TernaryDyadicVector) :
    (∀ x : Fin 3 → ℤ,
      (ternaryLattice.quadForm (ternaryDyadicImage v w u x) : ZMod 16) =
        (ternaryLattice.quadForm x : ZMod 16)) ↔ ternaryDyadicCoefficients v w u := by
  constructor
  · intro h
    have h0 := h ![1, 0, 0]
    have h1 := h ![0, 1, 0]
    have h2 := h ![0, 0, 1]
    have h01 := h ![1, 1, 0]
    have h02 := h ![1, 0, 1]
    have h12 := h ![0, 1, 1]
    simp only [ternaryDyadicImage_quadForm] at h0 h1 h2 h01 h02 h12
    simp only [ternaryLattice_quadForm_coordinates,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, zero_mul, mul_zero, one_mul,
      add_zero, zero_add] at h0 h1 h2 h01 h02 h12
    push_cast at h0 h1 h2 h01 h02 h12
    refine ⟨h0, h1, h2, ?_, ?_, ?_⟩
    · push_cast
      linear_combination h01 - h0 - h1
    · push_cast
      linear_combination h02 - h0 - h2
    · push_cast
      linear_combination h12 - h1 - h2
  · rintro ⟨h0, h1, h2, h01, h02, h12⟩ x
    rw [ternaryDyadicImage_quadForm, ternaryLattice_quadForm_coordinates]
    push_cast at h01 h02 h12 ⊢
    linear_combination (x 0 : ZMod 16)^2 * h0 + (x 1 : ZMod 16)^2 * h1 +
      (x 2 : ZMod 16)^2 * h2 + (x 0 : ZMod 16) * (x 1 : ZMod 16) * h01 +
      (x 0 : ZMod 16) * (x 2 : ZMod 16) * h02 +
      (x 1 : ZMod 16) * (x 2 : ZMod 16) * h12

theorem ternaryDyadic_pair_mod_iff (a : ℤ) :
    a % 8 = 0 ↔ ((2 * a : ℤ) : ZMod 16) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  norm_num
  omega

theorem ternaryDyadic_model_mem_iff (v w u : TernaryDyadicVector) :
    ((v, w), u) ∈ ternaryDyadicModelFamilies ↔ ternaryDyadicCoefficients v w u := by
  have hnorm (a b : ℤ) : a % 16 = b % 16 ↔ (a : ZMod 16) = b :=
    (ZMod.intCast_eq_intCast_iff' a b 16).symm
  simp only [ternaryDyadicModelFamilies, ternaryDyadicShell, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, true_and]
  rw [hnorm, hnorm, hnorm, ternaryDyadic_pair_mod_iff, ternaryDyadic_pair_mod_iff,
    ternaryDyadic_pair_mod_iff]
  norm_num only [Int.cast_ofNat]
  unfold ternaryDyadicCoefficients
  tauto


-- The membership theorem above supplies the interface to this large finite set.
-- Keep elaboration and linters from expanding its enumerated representation.
attribute [local irreducible] ternaryDyadicModelFamilies

/-- An ordered model triple gives the actual three native quotient basis images. -/
def ternaryDyadicModelToNative
    (t : {t // t ∈ ternaryDyadicModelFamilies}) :
    associatedBilinearDualQuotientSolutionFamily ternaryLattice 2 4 := by
  rcases t with ⟨⟨⟨v, w⟩, u⟩, ht⟩
  rw [ternaryDyadic_model_mem_iff] at ht
  have hc : ternaryDyadicCoefficients v w u := ht
  have hp := (ternaryDyadic_preserves_iff_coefficients v w u).mpr hc
  have hn := (ternaryDyadic_native_mem_iff v w u).mpr hp
  exact ⟨![ternaryDyadicVectorToQuotient v,
      ternaryDyadicVectorToQuotient w, ternaryDyadicVectorToQuotient u], hn⟩

theorem ternaryDyadicModelToNative_bijective : Function.Bijective ternaryDyadicModelToNative := by
  constructor
  · rintro ⟨⟨⟨v, w⟩, u⟩, ht⟩ ⟨⟨⟨v', w'⟩, u'⟩, hs⟩ h
    have hh : ![ternaryDyadicVectorToQuotient v, ternaryDyadicVectorToQuotient w,
        ternaryDyadicVectorToQuotient u] =
      ![ternaryDyadicVectorToQuotient v', ternaryDyadicVectorToQuotient w',
        ternaryDyadicVectorToQuotient u'] := congrArg Subtype.val h
    have h0 := ternaryDyadicVectorToQuotient_injective (congr_fun hh 0)
    have h1 := ternaryDyadicVectorToQuotient_injective (congr_fun hh 1)
    have h2 := ternaryDyadicVectorToQuotient_injective (congr_fun hh 2)
    apply Subtype.ext
    exact Prod.ext (Prod.ext h0 h1) h2
  · intro Y
    obtain ⟨v, hv⟩ := ternaryDyadicVectorToQuotient_surjective (Y.1 0)
    obtain ⟨w, hw⟩ := ternaryDyadicVectorToQuotient_surjective (Y.1 1)
    obtain ⟨u, hu⟩ := ternaryDyadicVectorToQuotient_surjective (Y.1 2)
    have hY : ![ternaryDyadicVectorToQuotient v, ternaryDyadicVectorToQuotient w,
        ternaryDyadicVectorToQuotient u] = Y.1 := by
      ext i
      fin_cases i
      · exact hv
      · exact hw
      · exact hu
    have hmem : ((v, w), u) ∈ ternaryDyadicModelFamilies := by
      have hn := Y.2
      rw [← hY] at hn
      have hp := (ternaryDyadic_native_mem_iff v w u).mp hn
      have hc := (ternaryDyadic_preserves_iff_coefficients v w u).mp hp
      rw [ternaryDyadic_model_mem_iff]
      exact hc
    let t : {t : (TernaryDyadicVector × TernaryDyadicVector) × TernaryDyadicVector //
        t ∈ ternaryDyadicModelFamilies} := ⟨((v, w), u), by
      rw [ternaryDyadic_model_mem_iff] at hmem ⊢
      exact hmem⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change ![ternaryDyadicVectorToQuotient v, ternaryDyadicVectorToQuotient w,
      ternaryDyadicVectorToQuotient u] = Y.1
    exact hY

/-- The count 128 belongs to the original associated-bilinear quotient family. -/
theorem ternary_native_count_two_four :
    associatedBilinearDualQuotientCount ternaryLattice 2 4 = 128 := by
  rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  calc
    _ = Nat.card {t // t ∈ ternaryDyadicModelFamilies} :=
      (Nat.card_congr (Equiv.ofBijective ternaryDyadicModelToNative
        ternaryDyadicModelToNative_bijective)).symm
    _ = 128 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, ternaryDyadicModelFamilies_card]

/-- The original density at two, with the independent half and polar factor. -/
theorem ternary_density_two : normalizedLocalDensity ternaryLattice 2 = 2 := by
  rw [ternary_density_two_eq_native_count, ternary_native_count_two_four]
  norm_num

end MassFormulaReleaseExamples
