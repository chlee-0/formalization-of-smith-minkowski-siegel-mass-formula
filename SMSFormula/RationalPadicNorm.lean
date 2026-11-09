import SMSFormula.FiniteQuadraticNorm
import SMSFormula.MatrixCongruence
import SMSFormula.RationalPadicSquareClass

/-!
# Odd-prime quadratic norms over the p-adics

The first local norm branch treated here is the unit branch of an unramified
quadratic extension. A nonsquare residue parameter gives a surjective norm on
p-adic integral units. The residue solution comes from finite-field norm
surjectivity, and a simple root in one coordinate lifts by Hensel's lemma.
-/

noncomputable section

namespace PadicInt

/-- A simple root modulo `p` of a polynomial over `ℤ_[p]` lifts to an exact
root. -/
theorem exists_polynomial_root_of_simple_root_mod_p
    {p : ℕ} [Fact p.Prime] (F : Polynomial ℤ_[p]) (a : ℤ_[p])
    (hFa : toZMod (F.eval a) = 0)
    (hderiv : toZMod (F.derivative.eval a) ≠ 0) :
    ∃ z : ℤ_[p], F.eval z = 0 := by
  have hFa_mem : F.eval a ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← ker_toZMod, RingHom.mem_ker]
    exact hFa
  have hFa_norm : ‖F.eval a‖ < 1 := by
    rw [← not_isUnit_iff]
    simpa [IsLocalRing.mem_maximalIdeal] using hFa_mem
  have hderiv_unit : IsUnit (F.derivative.eval a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro hzero
    apply hderiv
    rw [toZMod_eq_residueField_comp_residue]
    simp [hzero]
  have hderiv_norm : ‖F.derivative.eval a‖ = 1 :=
    isUnit_iff.mp hderiv_unit
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    simpa [hderiv_norm] using hFa_norm
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  exact ⟨z, hz⟩

/-- A simple root modulo `p` lifts to an exact root in the same residue
class. -/
theorem exists_polynomial_root_of_simple_root_mod_p_with_residue
    {p : ℕ} [Fact p.Prime] (F : Polynomial ℤ_[p]) (a : ℤ_[p])
    (hFa : toZMod (F.eval a) = 0)
    (hderiv : toZMod (F.derivative.eval a) ≠ 0) :
    ∃ z : ℤ_[p], F.eval z = 0 ∧ toZMod z = toZMod a := by
  have hFa_mem : F.eval a ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← ker_toZMod, RingHom.mem_ker]
    exact hFa
  have hFa_norm : ‖F.eval a‖ < 1 := by
    rw [← not_isUnit_iff]
    simpa [IsLocalRing.mem_maximalIdeal] using hFa_mem
  have hderiv_unit : IsUnit (F.derivative.eval a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro hzero
    apply hderiv
    rw [toZMod_eq_residueField_comp_residue]
    simp [hzero]
  have hderiv_norm : ‖F.derivative.eval a‖ = 1 :=
    isUnit_iff.mp hderiv_unit
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    simpa [hderiv_norm] using hFa_norm
  obtain ⟨z, hz, hz_close, _⟩ := hensels_lemma hnorm
  refine ⟨z, hz, ?_⟩
  have hza_norm : ‖z - a‖ < 1 := by
    simpa [hderiv_norm] using hz_close
  have hza_notunit : ¬ IsUnit (z - a) := by
    rw [not_isUnit_iff]
    exact hza_norm
  have hza_mem : z - a ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    simpa [IsLocalRing.mem_maximalIdeal] using hza_notunit
  have hza : toZMod (z - a) = 0 := by
    apply RingHom.mem_ker.mp
    rw [ker_toZMod]
    exact hza_mem
  exact sub_eq_zero.mp (by simpa using hza)

end PadicInt

namespace PositiveDefiniteIntegralLattice

/-- Every nonsingular symmetric binary form over an odd finite field
represents every scalar. -/
theorem exists_binary_gramQuadraticValue_eq_finiteField
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 2) (Fin 2) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (c : K) :
    ∃ v : Fin 2 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  apply (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr
  have hd_eq : d = ![d 0, d 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hd_eq]
  let a := d 0
  let b := d 1
  have ha : a ≠ 0 := hd 0
  have hb : b ≠ 0 := hd 1
  by_cases hsquare : IsSquare (-b / a)
  · have hiso : GramIsotropic (Matrix.diagonal ![a, b]) :=
      (binaryDiagonal_gramIsotropic_iff_isSquare_neg_div a b ha hb).mpr hsquare
    exact exists_binaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar a b ha hb hiso c
  · have hnorm := quadraticNormRepresents_finiteField_of_not_isSquare
      (-b / a) (c / a) hsquare
    rw [quadraticNormRepresents_iff_exists] at hnorm
    obtain ⟨x, y, hxy⟩ := hnorm
    refine ⟨![x, y], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    field_simp [ha] at hxy
    linear_combination hxy

set_option maxHeartbeats 800000 in
/-- At an odd prime, a symmetric binary p-adic integral form with unit
determinant represents every integral unit. -/
theorem exists_padicInt_binary_quadraticValue_eq_of_units
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    {c : ℤ_[p]} (hc : IsUnit c) :
    ∃ v : Fin 2 → ℤ_[p], dotProduct v (Matrix.mulVec A v) = c := by
  let Ar : Matrix (Fin 2) (Fin 2) (ZMod p) := A.map PadicInt.toZMod
  have hAr_symm : Ar.IsSymm := hA_symm.map PadicInt.toZMod
  have hAr_det : Ar.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod A.det) :=
      hA_det.map PadicInt.toZMod
    have hdet : Ar.det = PadicInt.toZMod A.det := by
      simpa [Ar] using (RingHom.map_det PadicInt.toZMod A).symm
    rw [hdet]
    exact hunit.ne_zero
  have hcres : PadicInt.toZMod c ≠ 0 :=
    (hc.map PadicInt.toZMod).ne_zero
  obtain ⟨r, hr⟩ := exists_binary_gramQuadraticValue_eq_finiteField
    Ar hAr_symm hAr_det (by
      simpa [ZMod.ringChar_zmod_n] using hpodd) (PadicInt.toZMod c)
  have hr_ne : r ≠ 0 := by
    intro hr0
    apply hcres
    rw [← hr]
    simp [hr0, gramQuadraticValue]
  have hmul_ne : Matrix.mulVec Ar r ≠ 0 := by
    intro hzero
    exact hr_ne (Matrix.eq_zero_of_mulVec_eq_zero hAr_det hzero)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hpodd hp2
  have hgradient :
      (2 : ZMod p) * Matrix.mulVec Ar r 0 ≠ 0 ∨
        (2 : ZMod p) * Matrix.mulVec Ar r 1 ≠ 0 := by
    by_cases h0 : Matrix.mulVec Ar r 0 ≠ 0
    · exact Or.inl (mul_ne_zero htwo h0)
    · right
      apply mul_ne_zero htwo
      intro h1
      apply hmul_ne
      funext i
      fin_cases i
      · exact not_ne_iff.mp h0
      · exact h1
  let x0 : ℤ_[p] := (r 0).val
  let y0 : ℤ_[p] := (r 1).val
  have hx0 : PadicInt.toZMod x0 = r 0 := by
    apply ZMod.val_injective
    simp [x0]
  have hy0 : PadicInt.toZMod y0 = r 1 := by
    apply ZMod.val_injective
    simp [y0]
  rcases hgradient with hgradient | hgradient
  · let F : Polynomial ℤ_[p] :=
      Polynomial.C (A 0 0) * Polynomial.X ^ 2 +
        Polynomial.C ((A 0 1 + A 1 0) * y0) * Polynomial.X +
        Polynomial.C (A 1 1 * y0 * y0 - c)
    have hF : PadicInt.toZMod (F.eval x0) = 0 := by
      simp [F, hx0, hy0, Ar, gramQuadraticValue, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] at hr ⊢
      linear_combination hr
    have hderiv_eq :
        PadicInt.toZMod (F.derivative.eval x0) =
          (2 : ZMod p) * Matrix.mulVec Ar r 0 := by
      simp [F, hx0, hy0, Ar, Matrix.mulVec, hA_symm.apply 0 1]
      ring
    obtain ⟨x, hx⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p
        F x0 hF (hderiv_eq ▸ hgradient)
    refine ⟨![x, y0], ?_⟩
    have hx' :
        A 0 0 * x ^ 2 + (A 0 1 + A 1 0) * y0 * x +
          (A 1 1 * y0 * y0 - c) = 0 := by
      simpa [F] using hx
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination hx'
  · let F : Polynomial ℤ_[p] :=
      Polynomial.C (A 1 1) * Polynomial.X ^ 2 +
        Polynomial.C ((A 0 1 + A 1 0) * x0) * Polynomial.X +
        Polynomial.C (A 0 0 * x0 * x0 - c)
    have hF : PadicInt.toZMod (F.eval y0) = 0 := by
      simp [F, hx0, hy0, Ar, gramQuadraticValue, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] at hr ⊢
      linear_combination hr
    have hderiv_eq :
        PadicInt.toZMod (F.derivative.eval y0) =
          (2 : ZMod p) * Matrix.mulVec Ar r 1 := by
      simp [F, hx0, hy0, Ar, Matrix.mulVec, hA_symm.apply 0 1]
      ring
    obtain ⟨y, hy⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p
        F y0 hF (hderiv_eq ▸ hgradient)
    refine ⟨![x0, y], ?_⟩
    have hy' :
        A 1 1 * y ^ 2 + (A 0 1 + A 1 0) * x0 * y +
          (A 0 0 * x0 * x0 - c) = 0 := by
      simpa [F] using hy
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination hy'

/-- The integral solution represents the same unit by the scalar-extended
binary Gram form over `ℚ_[p]`. -/
theorem exists_binary_gramQuadraticValue_eq_padic_unit_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    {c : ℤ_[p]} (hc : IsUnit c) :
    ∃ v : Fin 2 → ℚ_[p],
      gramQuadraticValue (A.map PadicInt.Coe.ringHom) v = (c : ℚ_[p]) := by
  obtain ⟨v, hv⟩ := exists_padicInt_binary_quadraticValue_eq_of_units
    hpodd A hA_symm hA_det hc
  refine ⟨fun i ↦ (v i : ℚ_[p]), ?_⟩
  have hmap := congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hv
  simpa [gramQuadraticValue, Matrix.mulVec, dotProduct] using hmap

/-- Two symmetric unimodular binary p-adic integral forms commonly represent
every integral unit after scalar extension to `ℚ_[p]`. -/
theorem binaryCommonRepresents_padic_unit_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A B : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    (hB_symm : B.IsSymm) (hB_det : IsUnit B.det)
    {c : ℤ_[p]} (hc : IsUnit c) :
    BinaryCommonRepresents
      (A.map PadicInt.Coe.ringHom) (B.map PadicInt.Coe.ringHom)
      (c : ℚ_[p]) :=
  ⟨exists_binary_gramQuadraticValue_eq_padic_unit_of_integral
      hpodd A hA_symm hA_det hc,
    exists_binary_gramQuadraticValue_eq_padic_unit_of_integral
      hpodd B hB_symm hB_det hc⟩

/-- Every nonsingular symmetric ternary form over an odd finite field is
isotropic. -/
theorem ternary_gramIsotropic_finiteField
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic A := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  have hbinary_symm : (Matrix.diagonal ![d 0, d 1]).IsSymm := by simp
  have hbinary_det : (Matrix.diagonal ![d 0, d 1]).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, hd]
  obtain ⟨u, hu⟩ := exists_binary_gramQuadraticValue_eq_finiteField
    (Matrix.diagonal ![d 0, d 1]) hbinary_symm hbinary_det hchar (-d 2)
  apply (gramIsotropic_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩)).mpr
  refine ⟨![u 0, u 1, 1], ?_, ?_⟩
  · intro hzero
    have := congrFun hzero 2
    simp at this
  · have hd_eq : d = ![d 0, d 1, d 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hd_eq]
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at hu ⊢
    linear_combination hu

set_option maxHeartbeats 1200000 in
/-- At an odd prime, a symmetric ternary p-adic integral form with unit
determinant has a nontrivial integral zero. -/
theorem exists_padicInt_ternary_isotropic
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    ∃ v : Fin 3 → ℤ_[p], v ≠ 0 ∧ dotProduct v (Matrix.mulVec A v) = 0 := by
  let Ar : Matrix (Fin 3) (Fin 3) (ZMod p) := A.map PadicInt.toZMod
  have hAr_symm : Ar.IsSymm := hA_symm.map PadicInt.toZMod
  have hAr_det : Ar.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod A.det) :=
      hA_det.map PadicInt.toZMod
    have hdet : Ar.det = PadicInt.toZMod A.det := by
      simpa [Ar] using (RingHom.map_det PadicInt.toZMod A).symm
    rw [hdet]
    exact hunit.ne_zero
  obtain ⟨r, hr_ne, hr⟩ := ternary_gramIsotropic_finiteField
    Ar hAr_symm hAr_det (by
      simpa [ZMod.ringChar_zmod_n] using hpodd)
  have hmul_ne : Matrix.mulVec Ar r ≠ 0 := by
    intro hzero
    exact hr_ne (Matrix.eq_zero_of_mulVec_eq_zero hAr_det hzero)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hpodd hp2
  have hgradient :
      (2 : ZMod p) * Matrix.mulVec Ar r 0 ≠ 0 ∨
        (2 : ZMod p) * Matrix.mulVec Ar r 1 ≠ 0 ∨
          (2 : ZMod p) * Matrix.mulVec Ar r 2 ≠ 0 := by
    by_cases h0 : Matrix.mulVec Ar r 0 ≠ 0
    · exact Or.inl (mul_ne_zero htwo h0)
    · right
      by_cases h1 : Matrix.mulVec Ar r 1 ≠ 0
      · exact Or.inl (mul_ne_zero htwo h1)
      · right
        apply mul_ne_zero htwo
        intro h2
        apply hmul_ne
        funext i
        fin_cases i
        · exact not_ne_iff.mp h0
        · exact not_ne_iff.mp h1
        · exact h2
  let x0 : ℤ_[p] := (r 0).val
  let y0 : ℤ_[p] := (r 1).val
  let z0 : ℤ_[p] := (r 2).val
  have hx0 : PadicInt.toZMod x0 = r 0 := by
    apply ZMod.val_injective
    simp [x0]
  have hy0 : PadicInt.toZMod y0 = r 1 := by
    apply ZMod.val_injective
    simp [y0]
  have hz0 : PadicInt.toZMod z0 = r 2 := by
    apply ZMod.val_injective
    simp [z0]
  rcases hgradient with hgradient | hgradient | hgradient
  · let F : Polynomial ℤ_[p] :=
      Polynomial.C (A 0 0) * Polynomial.X ^ 2 +
        Polynomial.C ((A 0 1 + A 1 0) * y0 +
          (A 0 2 + A 2 0) * z0) * Polynomial.X +
        Polynomial.C (A 1 1 * y0 * y0 +
          (A 1 2 + A 2 1) * z0 * y0 + A 2 2 * z0 * z0)
    have hF : PadicInt.toZMod (F.eval x0) = 0 := by
      simp [F, hx0, hy0, hz0, Ar, gramQuadraticValue, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hr ⊢
      linear_combination hr
    have hderiv_eq :
        PadicInt.toZMod (F.derivative.eval x0) =
          (2 : ZMod p) * Matrix.mulVec Ar r 0 := by
      simp [F, hx0, hy0, hz0, Ar, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, hA_symm.apply 0 1, hA_symm.apply 0 2]
      ring
    obtain ⟨x, hx, hxres⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p_with_residue
        F x0 hF (hderiv_eq ▸ hgradient)
    refine ⟨![x, y0, z0], ?_, ?_⟩
    · intro hzero
      apply hr_ne
      funext i
      fin_cases i
      · have hxi : x = 0 := by simpa using congrFun hzero 0
        calc
          r 0 = PadicInt.toZMod x := (hxres.trans hx0).symm
          _ = 0 := by simp [hxi]
      · have hyi : y0 = 0 := by simpa using congrFun hzero 1
        calc
          r 1 = PadicInt.toZMod y0 := hy0.symm
          _ = 0 := by simp [hyi]
      · have hzi : z0 = 0 := by simpa using congrFun hzero 2
        calc
          r 2 = PadicInt.toZMod z0 := hz0.symm
          _ = 0 := by simp [hzi]
    · have hx' :
          A 0 0 * x ^ 2 +
            ((A 0 1 + A 1 0) * y0 + (A 0 2 + A 2 0) * z0) * x +
            (A 1 1 * y0 * y0 + (A 1 2 + A 2 1) * z0 * y0 +
              A 2 2 * z0 * z0) = 0 := by
        simpa [F] using hx
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination hx'
  · let F : Polynomial ℤ_[p] :=
      Polynomial.C (A 1 1) * Polynomial.X ^ 2 +
        Polynomial.C ((A 0 1 + A 1 0) * x0 +
          (A 1 2 + A 2 1) * z0) * Polynomial.X +
        Polynomial.C (A 0 0 * x0 * x0 +
          (A 0 2 + A 2 0) * z0 * x0 + A 2 2 * z0 * z0)
    have hF : PadicInt.toZMod (F.eval y0) = 0 := by
      simp [F, hx0, hy0, hz0, Ar, gramQuadraticValue, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hr ⊢
      linear_combination hr
    have hderiv_eq :
        PadicInt.toZMod (F.derivative.eval y0) =
          (2 : ZMod p) * Matrix.mulVec Ar r 1 := by
      simp [F, hx0, hy0, hz0, Ar, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, hA_symm.apply 1 0, hA_symm.apply 1 2]
      ring
    obtain ⟨y, hy, hyres⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p_with_residue
        F y0 hF (hderiv_eq ▸ hgradient)
    refine ⟨![x0, y, z0], ?_, ?_⟩
    · intro hzero
      apply hr_ne
      funext i
      fin_cases i
      · have hxi : x0 = 0 := by simpa using congrFun hzero 0
        calc
          r 0 = PadicInt.toZMod x0 := hx0.symm
          _ = 0 := by simp [hxi]
      · have hyi : y = 0 := by simpa using congrFun hzero 1
        calc
          r 1 = PadicInt.toZMod y := (hyres.trans hy0).symm
          _ = 0 := by simp [hyi]
      · have hzi : z0 = 0 := by simpa using congrFun hzero 2
        calc
          r 2 = PadicInt.toZMod z0 := hz0.symm
          _ = 0 := by simp [hzi]
    · have hy' :
          A 1 1 * y ^ 2 +
            ((A 0 1 + A 1 0) * x0 + (A 1 2 + A 2 1) * z0) * y +
            (A 0 0 * x0 * x0 + (A 0 2 + A 2 0) * z0 * x0 +
              A 2 2 * z0 * z0) = 0 := by
        simpa [F] using hy
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination hy'
  · let F : Polynomial ℤ_[p] :=
      Polynomial.C (A 2 2) * Polynomial.X ^ 2 +
        Polynomial.C ((A 0 2 + A 2 0) * x0 +
          (A 1 2 + A 2 1) * y0) * Polynomial.X +
        Polynomial.C (A 0 0 * x0 * x0 +
          (A 0 1 + A 1 0) * y0 * x0 + A 1 1 * y0 * y0)
    have hF : PadicInt.toZMod (F.eval z0) = 0 := by
      simp [F, hx0, hy0, hz0, Ar, gramQuadraticValue, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hr ⊢
      linear_combination hr
    have hderiv_eq :
        PadicInt.toZMod (F.derivative.eval z0) =
          (2 : ZMod p) * Matrix.mulVec Ar r 2 := by
      simp [F, hx0, hy0, hz0, Ar, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, hA_symm.apply 2 0, hA_symm.apply 2 1]
      ring
    obtain ⟨z, hz, hzres⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p_with_residue
        F z0 hF (hderiv_eq ▸ hgradient)
    refine ⟨![x0, y0, z], ?_, ?_⟩
    · intro hzero
      apply hr_ne
      funext i
      fin_cases i
      · have hxi : x0 = 0 := by simpa using congrFun hzero 0
        calc
          r 0 = PadicInt.toZMod x0 := hx0.symm
          _ = 0 := by simp [hxi]
      · have hyi : y0 = 0 := by simpa using congrFun hzero 1
        calc
          r 1 = PadicInt.toZMod y0 := hy0.symm
          _ = 0 := by simp [hyi]
      · have hzi : z = 0 := by simpa using congrFun hzero 2
        calc
          r 2 = PadicInt.toZMod z := (hzres.trans hz0).symm
          _ = 0 := by simp [hzi]
    · have hz' :
          A 2 2 * z ^ 2 +
            ((A 0 2 + A 2 0) * x0 + (A 1 2 + A 2 1) * y0) * z +
            (A 0 0 * x0 * x0 + (A 0 1 + A 1 0) * y0 * x0 +
              A 1 1 * y0 * y0) = 0 := by
        simpa [F] using hz
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination hz'

/-- A symmetric unimodular ternary p-adic integral form is isotropic over
`ℚ_[p]` at every odd prime. -/
theorem ternary_gramIsotropic_padic_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    GramIsotropic (A.map PadicInt.Coe.ringHom) := by
  obtain ⟨v, hv_ne, hv⟩ :=
    exists_padicInt_ternary_isotropic hpodd A hA_symm hA_det
  refine ⟨fun i ↦ (v i : ℚ_[p]), ?_, ?_⟩
  · intro hzero
    apply hv_ne
    funext i
    have hi := congrFun hzero i
    apply Subtype.ext
    exact hi
  · have hmap := congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hv
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct] using hmap

/-- A symmetric unimodular ternary p-adic integral form represents every
p-adic scalar at an odd prime. -/
theorem exists_ternary_gramQuadraticValue_eq_padic_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    (c : ℚ_[p]) :
    ∃ v : Fin 3 → ℚ_[p],
      gramQuadraticValue (A.map PadicInt.Coe.ringHom) v = c := by
  have hsymm : (A.map PadicInt.Coe.ringHom).IsSymm :=
    hA_symm.map PadicInt.Coe.ringHom
  have hdet : (A.map PadicInt.Coe.ringHom).det ≠ 0 := by
    have hdet_eq : (A.map PadicInt.Coe.ringHom).det = (A.det : ℚ_[p]) := by
      simpa using (RingHom.map_det PadicInt.Coe.ringHom A).symm
    rw [hdet_eq]
    intro hzero
    apply hA_det.ne_zero
    apply Subtype.ext
    exact hzero
  exact exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
    (A.map PadicInt.Coe.ringHom) hsymm hdet (by norm_num)
    (ternary_gramIsotropic_padic_of_integral hpodd A hA_symm hA_det) c

private def gramQuadraticValueRing
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (x : Fin n → R) : R :=
  dotProduct x (Matrix.mulVec A x)

private lemma gramBilinearValue_symm_commRing
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hA : A.IsSymm)
    (x y : Fin n → R) :
    x ⬝ᵥ Matrix.mulVec A y = y ⬝ᵥ Matrix.mulVec A x := by
  rw [Matrix.dotProduct_mulVec]
  have hvec : Matrix.vecMul x A = Matrix.mulVec A x := by
    funext i
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply i j]
    rw [mul_comm]
  rw [hvec, dotProduct_comm]

private lemma gramQuadraticValue_add_commRing
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hA : A.IsSymm)
    (x y : Fin n → R) :
    gramQuadraticValueRing A (x + y) =
      gramQuadraticValueRing A x + gramQuadraticValueRing A y +
        2 * (x ⬝ᵥ Matrix.mulVec A y) := by
  simp only [gramQuadraticValueRing, Matrix.mulVec_add, dotProduct_add,
    add_dotProduct]
  rw [gramBilinearValue_symm_commRing A hA y x]
  ring

private lemma gramQuadraticValue_smul_commRing
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (r : R) (x : Fin n → R) :
    gramQuadraticValueRing A (r • x) =
      r ^ 2 * gramQuadraticValueRing A x := by
  simp [gramQuadraticValueRing, Matrix.mulVec, dotProduct, Finset.mul_sum]
  ring_nf

/-- A nontrivial nonsingular residue zero of a symmetric p-adic integral
form lifts along one nonzero-gradient coordinate to an exact integral zero. -/
private theorem exists_padicInt_isotropic_of_residue_isotropic
    {p n : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin n) (Fin n) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    (r : Fin n → ZMod p) (hr_ne : r ≠ 0)
    (hr : dotProduct r (Matrix.mulVec (A.map PadicInt.toZMod) r) = 0) :
    ∃ v : Fin n → ℤ_[p], v ≠ 0 ∧
      dotProduct v (Matrix.mulVec A v) = 0 := by
  let Ar : Matrix (Fin n) (Fin n) (ZMod p) := A.map PadicInt.toZMod
  have hAr_det : Ar.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod A.det) :=
      hA_det.map PadicInt.toZMod
    have hdet : Ar.det = PadicInt.toZMod A.det := by
      simpa [Ar] using (RingHom.map_det PadicInt.toZMod A).symm
    rw [hdet]
    exact hunit.ne_zero
  have hmul_ne : Matrix.mulVec Ar r ≠ 0 := by
    intro hzero
    exact hr_ne (Matrix.eq_zero_of_mulVec_eq_zero hAr_det hzero)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hpodd hp2
  obtain ⟨i, hi⟩ : ∃ i, Matrix.mulVec Ar r i ≠ 0 := by
    by_contra h
    apply hmul_ne
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  let r0 : Fin n → ℤ_[p] := fun j => (r j).val
  have hr0 (j : Fin n) : PadicInt.toZMod (r0 j) = r j := by
    apply ZMod.val_injective
    simp [r0]
  let e : Fin n → ℤ_[p] := fun j => if j = i then 1 else 0
  let X0 : Polynomial ℤ_[p] := Polynomial.X - Polynomial.C (r0 i)
  let F : Polynomial ℤ_[p] :=
    Polynomial.C (gramQuadraticValueRing A r0) +
      Polynomial.C (2 * Matrix.mulVec A r0 i) * X0 +
      Polynomial.C (A i i) * X0 ^ 2
  have hmapMul (j : Fin n) :
      PadicInt.toZMod (Matrix.mulVec A r0 j) = Matrix.mulVec Ar r j := by
    simp only [Matrix.mulVec, dotProduct, Ar, Matrix.map_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, hr0]
  have hmapQ : PadicInt.toZMod (gramQuadraticValueRing A r0) =
      dotProduct r (Matrix.mulVec Ar r) := by
    simp only [gramQuadraticValueRing, dotProduct]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, hr0, hmapMul]
  have hF : PadicInt.toZMod (F.eval (r0 i)) = 0 := by
    simp [F, X0, hmapQ, Ar, hr]
  have hderiv_eq :
      PadicInt.toZMod (F.derivative.eval (r0 i)) =
        (2 : ZMod p) * Matrix.mulVec Ar r i := by
    have heval : F.derivative.eval (r0 i) =
        2 * Matrix.mulVec A r0 i := by
      simp [F, X0, pow_two]
    rw [heval, map_mul, hmapMul]
    rw [map_ofNat PadicInt.toZMod 2]
  obtain ⟨z, hz, hzres⟩ :=
    PadicInt.exists_polynomial_root_of_simple_root_mod_p_with_residue
      F (r0 i) hF (hderiv_eq ▸ mul_ne_zero htwo hi)
  let delta : ℤ_[p] := z - r0 i
  let v : Fin n → ℤ_[p] := r0 + delta • e
  have heQ : gramQuadraticValueRing A e = A i i := by
    simp [gramQuadraticValueRing, Matrix.mulVec, dotProduct, e]
  have hcross : r0 ⬝ᵥ Matrix.mulVec A (delta • e) =
      delta * Matrix.mulVec A r0 i := by
    rw [gramBilinearValue_symm_commRing A hA_symm]
    simp [dotProduct, Matrix.mulVec, e]
  have hv_res (j : Fin n) : PadicInt.toZMod (v j) = r j := by
    by_cases hji : j = i
    · subst j
      simp [v, delta, e, hzres, hr0]
    · simp [v, delta, e, hji, hr0]
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hr_ne
    funext j
    rw [← hv_res j]
    simp [hv]
  · change gramQuadraticValueRing A (r0 + delta • e) = 0
    rw [gramQuadraticValue_add_commRing A hA_symm]
    rw [gramQuadraticValue_smul_commRing]
    rw [heQ, hcross]
    have hz' :
        gramQuadraticValueRing A r0 +
          (2 * Matrix.mulVec A r0 i) * delta +
          A i i * delta ^ 2 = 0 := by
      simpa [F, X0, delta] using hz
    linear_combination hz'

/-- Every nonsingular symmetric form of dimension at least three over an odd
finite field is isotropic. -/
theorem gramIsotropic_finiteField
    {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin n) (Fin n) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, hiso⟩ :=
    exists_gramMatrix_congr_differenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det hchar
  apply hiso.mpr
  apply (gramIsotropic_differenceGramBlock_iff A B).mpr
  exact Or.inl (ternary_gramIsotropic_finiteField
    A hA_symm hA_det hchar)

/-- At an odd prime, a symmetric p-adic integral form of dimension at least
three with unit determinant has a nontrivial integral zero. -/
theorem exists_padicInt_isotropic
    {p n : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    ∃ v : Fin n → ℤ_[p], v ≠ 0 ∧ dotProduct v (Matrix.mulVec A v) = 0 := by
  let Ar : Matrix (Fin n) (Fin n) (ZMod p) := A.map PadicInt.toZMod
  have hAr_symm : Ar.IsSymm := hA_symm.map PadicInt.toZMod
  have hAr_det : Ar.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod A.det) :=
      hA_det.map PadicInt.toZMod
    have hdet : Ar.det = PadicInt.toZMod A.det := by
      simpa [Ar] using (RingHom.map_det PadicInt.toZMod A).symm
    rw [hdet]
    exact hunit.ne_zero
  obtain ⟨r, hr_ne, hr⟩ := gramIsotropic_finiteField hn
    Ar hAr_symm hAr_det (by
      simpa [ZMod.ringChar_zmod_n] using hpodd)
  exact exists_padicInt_isotropic_of_residue_isotropic
    hpodd A hA_symm hA_det r hr_ne hr

/-- A symmetric unimodular p-adic integral form of dimension at least three
is isotropic over `ℚ_[p]` at every odd prime. -/
theorem gramIsotropic_padic_of_integral
    {p n : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    GramIsotropic (A.map PadicInt.Coe.ringHom) := by
  obtain ⟨v, hv_ne, hv⟩ :=
    exists_padicInt_isotropic hpodd hn A hA_symm hA_det
  refine ⟨fun i ↦ (v i : ℚ_[p]), ?_, ?_⟩
  · intro hzero
    apply hv_ne
    funext i
    have hi := congrFun hzero i
    apply Subtype.ext
    exact hi
  · have hmap := congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hv
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct] using hmap

/-- A symmetric unimodular p-adic integral form of dimension at least three
represents every p-adic scalar at an odd prime. -/
theorem exists_gramQuadraticValue_eq_padic_of_integral
    {p n : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    (c : ℚ_[p]) :
    ∃ v : Fin n → ℚ_[p],
      gramQuadraticValue (A.map PadicInt.Coe.ringHom) v = c := by
  have hsymm : (A.map PadicInt.Coe.ringHom).IsSymm :=
    hA_symm.map PadicInt.Coe.ringHom
  have hdet : (A.map PadicInt.Coe.ringHom).det ≠ 0 := by
    have hdet_eq : (A.map PadicInt.Coe.ringHom).det = (A.det : ℚ_[p]) := by
      simpa using (RingHom.map_det PadicInt.Coe.ringHom A).symm
    rw [hdet_eq]
    intro hzero
    apply hA_det.ne_zero
    apply Subtype.ext
    exact hzero
  exact exists_gramQuadraticValue_eq_of_gramIsotropic
    (A.map PadicInt.Coe.ringHom) hsymm hdet (by norm_num)
    (gramIsotropic_padic_of_integral hpodd hn A hA_symm hA_det) c

/-- Every nonsingular symmetric quaternary form over an odd finite field is
isotropic. -/
theorem quaternary_gramIsotropic_finiteField
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 4) (Fin 4) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic A := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  let D : Matrix (Fin 3) (Fin 3) K :=
    Matrix.diagonal ![d 0, d 1, d 2]
  have hD_symm : D.IsSymm := by simp [D]
  have hD_det : D.det ≠ 0 := by
    simp [D, Matrix.det_diagonal, Fin.prod_univ_three, hd]
  obtain ⟨u, hu_ne, hu⟩ :=
    ternary_gramIsotropic_finiteField D hD_symm hD_det hchar
  apply (gramIsotropic_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩)).mpr
  refine ⟨![u 0, u 1, u 2, 0], ?_, ?_⟩
  · intro hzero
    apply hu_ne
    funext i
    fin_cases i
    · exact congrFun hzero 0
    · exact congrFun hzero 1
    · exact congrFun hzero 2
  · have hd_eq : d = ![d 0, d 1, d 2, d 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hd_eq]
    simpa [D, gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_four] using hu

/-- At an odd prime, a symmetric quaternary p-adic integral form with unit
determinant has a nontrivial integral zero. -/
theorem exists_padicInt_quaternary_isotropic
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    ∃ v : Fin 4 → ℤ_[p], v ≠ 0 ∧ dotProduct v (Matrix.mulVec A v) = 0 := by
  let Ar : Matrix (Fin 4) (Fin 4) (ZMod p) := A.map PadicInt.toZMod
  have hAr_symm : Ar.IsSymm := hA_symm.map PadicInt.toZMod
  have hAr_det : Ar.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod A.det) :=
      hA_det.map PadicInt.toZMod
    have hdet : Ar.det = PadicInt.toZMod A.det := by
      simpa [Ar] using (RingHom.map_det PadicInt.toZMod A).symm
    rw [hdet]
    exact hunit.ne_zero
  obtain ⟨r, hr_ne, hr⟩ := quaternary_gramIsotropic_finiteField
    Ar hAr_symm hAr_det (by
      simpa [ZMod.ringChar_zmod_n] using hpodd)
  exact exists_padicInt_isotropic_of_residue_isotropic
    hpodd A hA_symm hA_det r hr_ne hr

/-- A symmetric unimodular quaternary p-adic integral form is isotropic over
`ℚ_[p]` at every odd prime. -/
theorem quaternary_gramIsotropic_padic_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    GramIsotropic (A.map PadicInt.Coe.ringHom) := by
  obtain ⟨v, hv_ne, hv⟩ :=
    exists_padicInt_quaternary_isotropic hpodd A hA_symm hA_det
  refine ⟨fun i ↦ (v i : ℚ_[p]), ?_, ?_⟩
  · intro hzero
    apply hv_ne
    funext i
    have hi := congrFun hzero i
    apply Subtype.ext
    exact hi
  · have hmap := congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hv
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct] using hmap

/-- A symmetric unimodular quaternary p-adic integral form represents every
p-adic scalar at an odd prime. -/
theorem exists_quaternary_gramQuadraticValue_eq_padic_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    (c : ℚ_[p]) :
    ∃ v : Fin 4 → ℚ_[p],
      gramQuadraticValue (A.map PadicInt.Coe.ringHom) v = c := by
  have hsymm : (A.map PadicInt.Coe.ringHom).IsSymm :=
    hA_symm.map PadicInt.Coe.ringHom
  have hdet : (A.map PadicInt.Coe.ringHom).det ≠ 0 := by
    have hdet_eq : (A.map PadicInt.Coe.ringHom).det = (A.det : ℚ_[p]) := by
      simpa using (RingHom.map_det PadicInt.Coe.ringHom A).symm
    rw [hdet_eq]
    intro hzero
    apply hA_det.ne_zero
    apply Subtype.ext
    exact hzero
  exact exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
    (A.map PadicInt.Coe.ringHom) hsymm hdet (by norm_num)
    (quaternary_gramIsotropic_padic_of_integral
      hpodd A hA_symm hA_det) c

/-- Every nonsingular symmetric quinary form over an odd finite field is
isotropic. -/
theorem quinary_gramIsotropic_finiteField
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 5) (Fin 5) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic A := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  let D : Matrix (Fin 4) (Fin 4) K :=
    Matrix.diagonal ![d 0, d 1, d 2, d 3]
  have hD_symm : D.IsSymm := by simp [D]
  have hD_det : D.det ≠ 0 := by
    simp [D, Matrix.det_diagonal, Fin.prod_univ_four, hd]
  obtain ⟨u, hu_ne, hu⟩ :=
    quaternary_gramIsotropic_finiteField D hD_symm hD_det hchar
  apply (gramIsotropic_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩)).mpr
  refine ⟨![u 0, u 1, u 2, u 3, 0], ?_, ?_⟩
  · intro hzero
    apply hu_ne
    funext i
    fin_cases i
    · exact congrFun hzero 0
    · exact congrFun hzero 1
    · exact congrFun hzero 2
    · exact congrFun hzero 3
  · have hd_eq : d = ![d 0, d 1, d 2, d 3, d 4] := by
      funext i
      fin_cases i <;> rfl
    rw [hd_eq]
    simpa [D, gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_five] using hu

/-- At an odd prime, a symmetric quinary p-adic integral form with unit
determinant has a nontrivial integral zero. -/
theorem exists_padicInt_quinary_isotropic
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 5) (Fin 5) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    ∃ v : Fin 5 → ℤ_[p], v ≠ 0 ∧ dotProduct v (Matrix.mulVec A v) = 0 := by
  let Ar : Matrix (Fin 5) (Fin 5) (ZMod p) := A.map PadicInt.toZMod
  have hAr_symm : Ar.IsSymm := hA_symm.map PadicInt.toZMod
  have hAr_det : Ar.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod A.det) :=
      hA_det.map PadicInt.toZMod
    have hdet : Ar.det = PadicInt.toZMod A.det := by
      simpa [Ar] using (RingHom.map_det PadicInt.toZMod A).symm
    rw [hdet]
    exact hunit.ne_zero
  obtain ⟨r, hr_ne, hr⟩ := quinary_gramIsotropic_finiteField
    Ar hAr_symm hAr_det (by
      simpa [ZMod.ringChar_zmod_n] using hpodd)
  exact exists_padicInt_isotropic_of_residue_isotropic
    hpodd A hA_symm hA_det r hr_ne hr

/-- A symmetric unimodular quinary p-adic integral form is isotropic over
`ℚ_[p]` at every odd prime. -/
theorem quinary_gramIsotropic_padic_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 5) (Fin 5) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det) :
    GramIsotropic (A.map PadicInt.Coe.ringHom) := by
  obtain ⟨v, hv_ne, hv⟩ :=
    exists_padicInt_quinary_isotropic hpodd A hA_symm hA_det
  refine ⟨fun i ↦ (v i : ℚ_[p]), ?_, ?_⟩
  · intro hzero
    apply hv_ne
    funext i
    have hi := congrFun hzero i
    apply Subtype.ext
    exact hi
  · have hmap := congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hv
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct] using hmap

/-- A symmetric unimodular quinary p-adic integral form represents every
p-adic scalar at an odd prime. -/
theorem exists_quinary_gramQuadraticValue_eq_padic_of_integral
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 5) (Fin 5) ℤ_[p])
    (hA_symm : A.IsSymm) (hA_det : IsUnit A.det)
    (c : ℚ_[p]) :
    ∃ v : Fin 5 → ℚ_[p],
      gramQuadraticValue (A.map PadicInt.Coe.ringHom) v = c := by
  have hsymm : (A.map PadicInt.Coe.ringHom).IsSymm :=
    hA_symm.map PadicInt.Coe.ringHom
  have hdet : (A.map PadicInt.Coe.ringHom).det ≠ 0 := by
    have hdet_eq : (A.map PadicInt.Coe.ringHom).det = (A.det : ℚ_[p]) := by
      simpa using (RingHom.map_det PadicInt.Coe.ringHom A).symm
    rw [hdet_eq]
    intro hzero
    apply hA_det.ne_zero
    apply Subtype.ext
    exact hzero
  exact exists_quinary_gramQuadraticValue_eq_of_gramIsotropic
    (A.map PadicInt.Coe.ringHom) hsymm hdet (by norm_num)
    (quinary_gramIsotropic_padic_of_integral
      hpodd A hA_symm hA_det) c

/-- If `d` and `c` are p-adic integral units and the residue of `d` is a
nonsquare at an odd prime, then `x² - d y² = c` has an integral solution. -/
theorem exists_padicInt_quadraticNorm_eq_of_units_nonsquare_residue
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℤ_[p]} (hd : IsUnit d) (hc : IsUnit c)
    (hdns : ¬ IsSquare (PadicInt.toZMod d)) :
    ∃ x y : ℤ_[p], x * x - d * y * y = c := by
  have hcres : PadicInt.toZMod c ≠ 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    intro hzero
    have : IsLocalRing.residue ℤ_[p] c = 0 := by
      apply PadicInt.residueField.injective
      simpa using hzero
    exact (IsLocalRing.residue_ne_zero_iff_isUnit c).2 hc this
  have hnorm : quadraticNormRepresents
      (PadicInt.toZMod d) (PadicInt.toZMod c) :=
    quadraticNormRepresents_finiteField_of_not_isSquare _ _ hdns
  rw [quadraticNormRepresents_iff_exists] at hnorm
  obtain ⟨xr, yr, hxy⟩ := hnorm
  let x0 : ℤ_[p] := (xr.val : ℕ)
  let y0 : ℤ_[p] := (yr.val : ℕ)
  have hx0 : PadicInt.toZMod x0 = xr := by
    apply ZMod.val_injective
    simp [x0]
  have hy0 : PadicInt.toZMod y0 = yr := by
    apply ZMod.val_injective
    simp [y0]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hpodd hp2
  by_cases hxr : xr = 0
  · have hyr : yr ≠ 0 := by
      intro hyr
      apply hcres
      simpa [hxr, hyr] using hxy.symm
    let F : Polynomial ℤ_[p] :=
      Polynomial.C (x0 * x0) - Polynomial.C d * Polynomial.X ^ 2 -
        Polynomial.C c
    have hFy : PadicInt.toZMod (F.eval y0) = 0 := by
      simp [F, hx0, hy0]
      linear_combination hxy
    have hderiv : PadicInt.toZMod (F.derivative.eval y0) ≠ 0 := by
      have hdres : PadicInt.toZMod d ≠ 0 := by
        rw [PadicInt.toZMod_eq_residueField_comp_residue]
        intro hzero
        have : IsLocalRing.residue ℤ_[p] d = 0 := by
          apply PadicInt.residueField.injective
          simpa using hzero
        exact (IsLocalRing.residue_ne_zero_iff_isUnit d).2 hd this
      have heq : PadicInt.toZMod (F.derivative.eval y0) =
          -(2 : ZMod p) * PadicInt.toZMod d * yr := by
        simp [F, hy0]
        ring
      rw [heq]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr htwo) hdres) hyr
    obtain ⟨y, hy⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p F y0 hFy hderiv
    refine ⟨x0, y, ?_⟩
    have hy' : x0 * x0 - d * y ^ 2 - c = 0 := by
      simpa [F] using hy
    rw [pow_two] at hy'
    linear_combination hy'
  · let F : Polynomial ℤ_[p] :=
      Polynomial.X ^ 2 - Polynomial.C (d * y0 * y0 + c)
    have hFx : PadicInt.toZMod (F.eval x0) = 0 := by
      simp [F, hx0, hy0]
      linear_combination hxy
    have hderiv : PadicInt.toZMod (F.derivative.eval x0) ≠ 0 := by
      have heq : PadicInt.toZMod (F.derivative.eval x0) =
          (2 : ZMod p) * xr := by
        calc
          PadicInt.toZMod (F.derivative.eval x0) =
              PadicInt.toZMod ((2 : ℤ_[p]) * x0) := by
                apply congrArg PadicInt.toZMod
                simp [F, one_add_one_eq_two]
          _ = PadicInt.toZMod (2 : ℤ_[p]) * PadicInt.toZMod x0 :=
            map_mul _ _ _
          _ = (2 : ZMod p) * xr := by rw [map_ofNat, hx0]
      rw [heq]
      exact mul_ne_zero htwo hxr
    obtain ⟨x, hx⟩ :=
      PadicInt.exists_polynomial_root_of_simple_root_mod_p F x0 hFx hderiv
    refine ⟨x, y0, ?_⟩
    have hx' : x * x = d * y0 * y0 + c := by
      exact sub_eq_zero.mp (by simpa [F, pow_two] using hx)
    linear_combination hx'

/-- The preceding integral solution represents every p-adic unit by the norm
from the unramified nonsplit quadratic algebra. -/
theorem quadraticNormRepresents_padic_units_of_nonsquare_residue
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℤ_[p]} (hd : IsUnit d) (hc : IsUnit c)
    (hdns : ¬ IsSquare (PadicInt.toZMod d)) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) := by
  rw [quadraticNormRepresents_iff_exists]
  obtain ⟨x, y, hxy⟩ :=
    exists_padicInt_quadraticNorm_eq_of_units_nonsquare_residue
      hpodd hd hc hdns
  exact ⟨x, y, congrArg Subtype.val hxy⟩

end PositiveDefiniteIntegralLattice

namespace PadicInt

/-- A p-adic integral unit has valuation zero. -/
lemma valuation_eq_zero_of_isUnit
    {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (hu : IsUnit u) :
    u.valuation = 0 := by
  obtain ⟨v, rfl⟩ := hu
  have hmul : (v : ℤ_[p]) * (↑v⁻¹ : ℤ_[p]) = 1 := by simp
  have hv : (v : ℤ_[p]) ≠ 0 := Units.ne_zero v
  have hvi : (↑v⁻¹ : ℤ_[p]) ≠ 0 := Units.ne_zero v⁻¹
  have h := congrArg valuation hmul
  rw [valuation_mul hv hvi, valuation_one] at h
  omega

/-- A p-adic integral unit is a square in `ℚ_[p]` exactly when it is already
a square in `ℤ_[p]`. -/
theorem isSquare_coe_iff_isSquare_of_isUnit
    {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare (u : ℚ_[p]) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hu0 : u ≠ 0 := IsUnit.ne_zero hu
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hu0
      apply Subtype.ext
      simpa [hzero] using hx
    have huval : u.valuation = 0 := valuation_eq_zero_of_isUnit hu
    have hxval : x.valuation = 0 := by
      have hval := congrArg Padic.valuation hx
      rw [Padic.valuation_mul hx0 hx0, valuation_coe, huval] at hval
      omega
    have hxnorm : ‖x‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
      simp
    let X : ℤ_[p] := ⟨x, hxnorm.le⟩
    exact ⟨X, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x : ℚ_[p]), congrArg Subtype.val hx⟩

/-- Two nonzero p-adic integers of the same valuation differ by an integral
unit factor. -/
theorem exists_isUnit_mul_eq_of_valuation_eq
    {p : ℕ} [Fact p.Prime] {C D : ℤ_[p]}
    (hC : C ≠ 0) (hD : D ≠ 0) (hval : C.valuation = D.valuation) :
    ∃ U : ℤ_[p], IsUnit U ∧ C = D * U := by
  have hCq : (C : ℚ_[p]) ≠ 0 := coe_ne_zero.mpr hC
  have hDq : (D : ℚ_[p]) ≠ 0 := coe_ne_zero.mpr hD
  let q : ℚ_[p] := (C : ℚ_[p]) * (D : ℚ_[p])⁻¹
  have hq0 : q ≠ 0 := mul_ne_zero hCq (inv_ne_zero hDq)
  have hqval : q.valuation = 0 := by
    rw [show q = (C : ℚ_[p]) * (D : ℚ_[p])⁻¹ by rfl,
      Padic.valuation_mul hCq (inv_ne_zero hDq), Padic.valuation_inv,
      valuation_coe, valuation_coe, hval]
    omega
  let U : ℤ_[p] :=
    ⟨q, (Padic.norm_le_one_iff_val_nonneg _).2 (by rw [hqval])⟩
  refine ⟨U, ?_, ?_⟩
  · rw [isUnit_iff]
    change ‖q‖ = 1
    rw [Padic.norm_eq_zpow_neg_valuation hq0, hqval]
    simp
  · apply Subtype.ext
    change (C : ℚ_[p]) = (D : ℚ_[p]) * q
    simp only [q]
    field_simp

end PadicInt

namespace Padic

/-- The valuation of a difference of nonzero p-adic numbers with distinct
valuations is the minimum of their valuations. -/
lemma valuation_sub_eq_of_ne
    {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.valuation ≠ b.valuation) :
    (a - b).valuation = min a.valuation b.valuation := by
  have hval : addValuation a ≠ addValuation b := by
    intro h
    apply hab
    simpa [addValuation, addValuationDef, ha, hb] using h
  have h := (addValuation (p := p)).map_add_of_distinct_val
    (x := a) (y := -b) (by simpa using hval)
  have hsub : a - b ≠ 0 := by
    intro hz
    apply hab
    rw [sub_eq_zero.mp hz]
  have hsub' : a + -b ≠ 0 := by simpa [sub_eq_add_neg] using hsub
  apply WithTop.coe_eq_coe.mp
  simpa [sub_eq_add_neg, addValuation, addValuationDef, ha, hb, hsub'] using h

/-- Negation does not change the valuation of a p-adic number. -/
lemma valuation_neg
    {p : ℕ} [Fact p.Prime] (a : ℚ_[p]) : (-a).valuation = a.valuation := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h := (addValuation (p := p)).map_neg a
    change addValuationDef (-a) = addValuationDef a at h
    have hna : -a ≠ 0 := neg_ne_zero.mpr ha
    simp only [addValuationDef, if_neg hna, if_neg ha] at h
    exact WithTop.coe_eq_coe.mp h

end Padic

namespace PositiveDefiniteIntegralLattice

/-- For a ramified quadratic parameter of valuation one and a unit target,
norm representation is equivalent to squarehood of the target residue. -/
theorem quadraticNormRepresents_padic_ramified_unit_iff_square_residue
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℤ_[p]} (hdval : d.valuation = 1) (hc : IsUnit c) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
      IsSquare (PadicInt.toZMod c) := by
  have hd0 : d ≠ 0 := by
    intro hd
    simp [hd] at hdval
  have hdvalq : (d : ℚ_[p]).valuation = 1 := by norm_cast
  have hc0 : c ≠ 0 := IsUnit.ne_zero hc
  have hcval : c.valuation = 0 := PadicInt.valuation_eq_zero_of_isUnit hc
  have hcvalq : (c : ℚ_[p]).valuation = 0 := by norm_cast
  constructor
  · rw [quadraticNormRepresents_iff_exists]
    rintro ⟨x, y, hxy⟩
    rcases eq_or_ne x 0 with rfl | hx
    · have hy : y ≠ 0 := by
        intro hy
        simp [hy] at hxy
        exact hc0 (Subtype.ext hxy.symm)
      have hval := congrArg Padic.valuation hxy
      have hvdy : ((d : ℚ_[p]) * y * y).valuation = 1 + 2 * y.valuation := by
        calc
          ((d : ℚ_[p]) * y * y).valuation =
              ((d : ℚ_[p]) * y).valuation + y.valuation := by
                rw [Padic.valuation_mul
                  (mul_ne_zero (PadicInt.coe_ne_zero.mpr hd0) hy) hy]
          _ = (d : ℚ_[p]).valuation + y.valuation + y.valuation := by
                rw [Padic.valuation_mul (PadicInt.coe_ne_zero.mpr hd0) hy]
          _ = 1 + 2 * y.valuation := by rw [hdvalq]; omega
      simp only [zero_mul, zero_sub] at hval
      rw [Padic.valuation_neg, hvdy, hcvalq] at hval
      omega
    · rcases eq_or_ne y 0 with rfl | hy
      · have hval := congrArg Padic.valuation hxy
        simp [Padic.valuation_mul, hx, hcvalq] at hval
        have hxnonneg : 0 ≤ x.valuation := by omega
        let X : ℤ_[p] :=
          ⟨x, (Padic.norm_le_one_iff_val_nonneg _).2 hxnonneg⟩
        refine ⟨PadicInt.toZMod X, ?_⟩
        have hX : X * X = c := by
          apply Subtype.ext
          simpa [X] using hxy
        simpa using congrArg PadicInt.toZMod hX.symm
      · have hvalx : (x * x).valuation = 2 * x.valuation := by
          rw [Padic.valuation_mul hx hx]
          omega
        have hvaly : ((d : ℚ_[p]) * y * y).valuation = 1 + 2 * y.valuation := by
          calc
            ((d : ℚ_[p]) * y * y).valuation =
                ((d : ℚ_[p]) * y).valuation + y.valuation := by
                  rw [Padic.valuation_mul
                    (mul_ne_zero (PadicInt.coe_ne_zero.mpr hd0) hy) hy]
            _ = (d : ℚ_[p]).valuation + y.valuation + y.valuation := by
                  rw [Padic.valuation_mul (PadicInt.coe_ne_zero.mpr hd0) hy]
            _ = 1 + 2 * y.valuation := by rw [hdvalq]; omega
        have hvals : (x * x).valuation ≠ ((d : ℚ_[p]) * y * y).valuation := by
          rw [hvalx, hvaly]
          omega
        have hmin := Padic.valuation_sub_eq_of_ne
          (mul_ne_zero hx hx)
          (mul_ne_zero (mul_ne_zero (PadicInt.coe_ne_zero.mpr hd0) hy) hy)
          hvals
        rw [hxy, hcvalq, hvalx, hvaly] at hmin
        have hxnonneg : 0 ≤ x.valuation := by omega
        have hynonneg : 0 ≤ y.valuation := by omega
        let X : ℤ_[p] :=
          ⟨x, (Padic.norm_le_one_iff_val_nonneg _).2 hxnonneg⟩
        let Y : ℤ_[p] :=
          ⟨y, (Padic.norm_le_one_iff_val_nonneg _).2 hynonneg⟩
        have hXY : X * X - d * Y * Y = c := by
          apply Subtype.ext
          exact hxy
        have hdres : PadicInt.toZMod d = 0 := by
          by_contra hdres
          have hdunit : IsUnit d := by
            rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
            intro hzero
            apply hdres
            rw [PadicInt.toZMod_eq_residueField_comp_residue]
            simp [hzero]
          have := PadicInt.valuation_eq_zero_of_isUnit hdunit
          omega
        refine ⟨PadicInt.toZMod X, ?_⟩
        have hres := congrArg PadicInt.toZMod hXY
        simp [hdres] at hres
        exact hres.symm
  · intro hsq
    have hcsq : IsSquare c :=
      (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd hc).2 hsq
    obtain ⟨x, hx⟩ := hcsq
    rw [quadraticNormRepresents_iff_exists]
    refine ⟨(x : ℚ_[p]), 0, ?_⟩
    simpa using (congrArg Subtype.val hx).symm

/-- For a valuation-one quadratic parameter, a target of the form `d * u`
with `u` a unit is represented exactly when the residue of `-u` is square.
This is the odd-valuation target branch transported from the unit branch by
the norm `-d` of the quadratic generator. -/
theorem quadraticNormRepresents_padic_ramified_mul_unit_iff_square_neg_residue
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d u : ℤ_[p]} (hdval : d.valuation = 1) (hu : IsUnit u) :
    quadraticNormRepresents (d : ℚ_[p]) ((d * u : ℤ_[p]) : ℚ_[p]) ↔
      IsSquare (PadicInt.toZMod (-u)) := by
  have hd0 : d ≠ 0 := by
    intro hd
    simp [hd] at hdval
  rw [← quadraticNormRepresents_padic_ramified_unit_iff_square_residue
    hpodd hdval hu.neg]
  have htransport := quadraticNormRepresents_iff_mul_neg_parameter
    (K := ℚ_[p]) (d := (d : ℚ_[p])) (c := (-u : ℤ_[p]))
    (PadicInt.coe_ne_zero.mpr hd0)
  rw [htransport]
  norm_num

/-- A rational ramified square class has an explicit valuation-one integral
parameter, and replacing the parameter by this representative preserves every
quadratic norm fiber. -/
theorem exists_padicInt_ramified_parameter_square_normalization
    {p : ℕ} [Fact p.Prime] {d : ℚ} (hd : d ≠ 0)
    (hpar : Rat.valuationParity p d = 1) :
    ∃ x : ℚ, x ≠ 0 ∧ ∃ D : ℤ_[p],
      D.valuation = 1 ∧
      (D : ℚ_[p]) = ((d * x ^ 2 : ℚ) : ℚ_[p]) ∧
      ∀ c : ℚ_[p],
        quadraticNormRepresents (d : ℚ_[p]) c ↔
          quadraticNormRepresents (D : ℚ_[p]) c := by
  obtain ⟨x, hx, hxval⟩ :=
    Rat.exists_square_normalization_of_valuationParity_eq_one hd hpar
  have hvalq : (((d * x ^ 2 : ℚ) : ℚ_[p])).valuation = 1 := by
    rw [Padic.valuation_ratCast, hxval]
  let D : ℤ_[p] :=
    ⟨((d * x ^ 2 : ℚ) : ℚ_[p]),
      (Padic.norm_le_one_iff_val_nonneg _).2 (by rw [hvalq]; omega)⟩
  refine ⟨x, hx, D, ?_, rfl, ?_⟩
  · apply Nat.cast_injective (R := ℤ)
    rw [← PadicInt.valuation_coe]
    exact hvalq
  · intro c
    have hxpadic : (x : ℚ_[p]) ≠ 0 := by exact_mod_cast hx
    have htransport := quadraticNormRepresents_iff_mul_sq_parameter
      (K := ℚ_[p]) (d := (d : ℚ_[p])) (c := c) (s := (x : ℚ_[p])) hxpadic
    simpa [D] using htransport

/-- A rational target of even p-adic valuation has an explicit integral unit
representative in its square class. Replacing the target by this representative
preserves representation for every quadratic parameter. -/
theorem exists_padicInt_unit_target_square_normalization
    {p : ℕ} [Fact p.Prime] {c : ℚ} (hc : c ≠ 0)
    (hpar : Rat.valuationParity p c = 0) :
    ∃ s : ℚ, s ≠ 0 ∧ ∃ C : ℤ_[p],
      IsUnit C ∧
      (C : ℚ_[p]) = ((c * s ^ 2 : ℚ) : ℚ_[p]) ∧
      ∀ d : ℚ_[p],
        quadraticNormRepresents d (c : ℚ_[p]) ↔
          quadraticNormRepresents d (C : ℚ_[p]) := by
  obtain ⟨s, hs, hsval⟩ :=
    Rat.exists_square_normalization_of_valuationParity_eq_zero hc hpar
  have hcs0 : c * s ^ 2 ≠ 0 := mul_ne_zero hc (pow_ne_zero 2 hs)
  have hvalq : (((c * s ^ 2 : ℚ) : ℚ_[p])).valuation = 0 := by
    rw [Padic.valuation_ratCast, hsval]
  let C : ℤ_[p] :=
    ⟨((c * s ^ 2 : ℚ) : ℚ_[p]),
      (Padic.norm_le_one_iff_val_nonneg _).2 (by rw [hvalq])⟩
  refine ⟨s, hs, C, ?_, rfl, ?_⟩
  · rw [PadicInt.isUnit_iff]
    change ‖((c * s ^ 2 : ℚ) : ℚ_[p])‖ = 1
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hcs0), hvalq]
    simp
  · intro d
    have hspadic : (s : ℚ_[p]) ≠ 0 := by exact_mod_cast hs
    have htransport := quadraticNormRepresents_iff_mul_sq_target
      (K := ℚ_[p]) (d := d) (c := (c : ℚ_[p])) (s := (s : ℚ_[p])) hspadic
    simpa [C] using htransport

/-- Relative to a valuation-one integral parameter, every rational target of
odd p-adic valuation is square-equivalent to the parameter times an integral
unit. The target replacement preserves every quadratic norm fiber. -/
theorem exists_padicInt_ramified_mul_unit_target_square_normalization
    {p : ℕ} [Fact p.Prime] {c : ℚ} (hc : c ≠ 0)
    (hpar : Rat.valuationParity p c = 1) {D : ℤ_[p]}
    (hDval : D.valuation = 1) :
    ∃ s : ℚ, s ≠ 0 ∧ ∃ U : ℤ_[p],
      IsUnit U ∧
      (((c * s ^ 2 : ℚ) : ℚ_[p]) = ((D * U : ℤ_[p]) : ℚ_[p])) ∧
      ∀ d : ℚ_[p],
        quadraticNormRepresents d (c : ℚ_[p]) ↔
          quadraticNormRepresents d ((D * U : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨s, hs, hsval⟩ :=
    Rat.exists_square_normalization_of_valuationParity_eq_one hc hpar
  have hvalq : (((c * s ^ 2 : ℚ) : ℚ_[p])).valuation = 1 := by
    rw [Padic.valuation_ratCast, hsval]
  let C : ℤ_[p] :=
    ⟨((c * s ^ 2 : ℚ) : ℚ_[p]),
      (Padic.norm_le_one_iff_val_nonneg _).2 (by rw [hvalq]; omega)⟩
  have hCval : C.valuation = 1 := by
    apply Nat.cast_injective (R := ℤ)
    rw [← PadicInt.valuation_coe]
    exact hvalq
  have hC0 : C ≠ 0 := by
    intro hC
    simp [hC] at hCval
  have hD0 : D ≠ 0 := by
    intro hD
    simp [hD] at hDval
  obtain ⟨U, hU, hCU⟩ :=
    PadicInt.exists_isUnit_mul_eq_of_valuation_eq hC0 hD0
      (hCval.trans hDval.symm)
  have hcastCU :
      (((c * s ^ 2 : ℚ) : ℚ_[p]) = ((D * U : ℤ_[p]) : ℚ_[p])) := by
    simpa [C] using congrArg Subtype.val hCU
  refine ⟨s, hs, U, hU, hcastCU, ?_⟩
  intro d
  have hspadic : (s : ℚ_[p]) ≠ 0 := by exact_mod_cast hs
  have htransport := quadraticNormRepresents_iff_mul_sq_target
    (K := ℚ_[p]) (d := d) (c := (c : ℚ_[p])) (s := (s : ℚ_[p])) hspadic
  rw [← hcastCU]
  simpa using htransport

/-- For a rational ramified parameter and an even-valuation rational target,
the quadratic norm criterion agrees with the explicit odd-prime Hilbert
symbol. -/
theorem quadraticNormRepresents_rat_padic_ramified_even_iff_hilbertSymbol
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity p d = 1)
    (hcpar : Rat.valuationParity p c = 0) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
      Rat.oddPrimeHilbertSymbol p hpodd d c = 1 := by
  obtain ⟨x, hx, D, hDval, hDcast, hDnorm⟩ :=
    exists_padicInt_ramified_parameter_square_normalization hd hdpar
  obtain ⟨s, hs, C, hCunit, hCcast, hCnorm⟩ :=
    exists_padicInt_unit_target_square_normalization hc hcpar
  have hnorm :
      quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
        IsSquare (PadicInt.toZMod C) := by
    rw [hDnorm, hCnorm,
      quadraticNormRepresents_padic_ramified_unit_iff_square_residue
        hpodd hDval hCunit]
  have hres :
      IsSquare (PadicInt.toZMod C) ↔
        Rat.oddPrimeUnitCharacter p c = 1 := by
    rw [← PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd hCunit]
    rw [← PadicInt.isSquare_coe_iff_isSquare_of_isUnit hCunit]
    rw [hCcast]
    have h :=
      Rat.isSquare_padic_iff_valuationParity_and_oddPrimeUnitCharacter
        hpodd (mul_ne_zero hc (pow_ne_zero 2 hs))
    rw [Rat.valuationParity_mul_sq (p := p) c s hc hs,
      Rat.oddPrimeUnitCharacter_mul_sq c s hc hs, hcpar] at h
    simpa using h
  rw [hnorm, hres]
  simp [Rat.oddPrimeHilbertSymbol, hdpar, hcpar]

/-- For a rational ramified parameter and an odd-valuation rational target,
the quadratic norm criterion reduces to p-adic squarehood of `-c / d`. -/
theorem quadraticNormRepresents_rat_padic_ramified_odd_iff_isSquare_neg_div
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity p d = 1)
    (hcpar : Rat.valuationParity p c = 1) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
      IsSquare ((-c / d : ℚ) : ℚ_[p]) := by
  obtain ⟨x, hx, D, hDval, hDcast, hDnorm⟩ :=
    exists_padicInt_ramified_parameter_square_normalization hd hdpar
  obtain ⟨s, hs, U, hU, hcsDU, hUnorm⟩ :=
    exists_padicInt_ramified_mul_unit_target_square_normalization
      hc hcpar hDval
  have hnorm :
      quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
        IsSquare (PadicInt.toZMod (-U)) := by
    rw [hDnorm, hUnorm,
      quadraticNormRepresents_padic_ramified_mul_unit_iff_square_neg_residue
        hpodd hDval hU]
  have hD0 : D ≠ 0 := by
    intro hD
    simp [hD] at hDval
  have hDq0 : (D : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hD0
  have hUeq :
      (U : ℚ_[p]) = (((c * s ^ 2 : ℚ) : ℚ_[p]) / (D : ℚ_[p])) := by
    have hcsDU' :
        (((c * s ^ 2 : ℚ) : ℚ_[p])) = (D : ℚ_[p]) * (U : ℚ_[p]) := by
      simpa using hcsDU
    calc
      (U : ℚ_[p]) = ((D : ℚ_[p]) * (U : ℚ_[p])) / (D : ℚ_[p]) := by
        field_simp [hDq0]
      _ = (((c * s ^ 2 : ℚ) : ℚ_[p]) / (D : ℚ_[p])) := by
        exact congrArg (fun z : ℚ_[p] => z / (D : ℚ_[p])) hcsDU'.symm
  have hsxq : ((s / x : ℚ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast div_ne_zero hs hx
  have hratio :
      ((-U : ℤ_[p]) : ℚ_[p]) =
        ((-c / d : ℚ) : ℚ_[p]) * ((s / x : ℚ) : ℚ_[p]) ^ 2 := by
    change -(U : ℚ_[p]) =
      ((-c / d : ℚ) : ℚ_[p]) * ((s / x : ℚ) : ℚ_[p]) ^ 2
    rw [hUeq, hDcast]
    push_cast
    field_simp [hd, hx]
  have hres :
      IsSquare (PadicInt.toZMod (-U)) ↔
        IsSquare ((-c / d : ℚ) : ℚ_[p]) := by
    have hnegU : IsUnit (-U) := hU.neg
    rw [← PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd hnegU]
    rw [← PadicInt.isSquare_coe_iff_isSquare_of_isUnit hnegU]
    rw [hratio]
    exact isSquare_mul_sq_iff_of_ne hsxq
  rw [hnorm, hres]

/-- For a rational ramified parameter and an odd-valuation rational target,
the quadratic norm criterion agrees with the explicit odd-prime Hilbert
symbol. -/
theorem quadraticNormRepresents_rat_padic_ramified_odd_iff_hilbertSymbol
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity p d = 1)
    (hcpar : Rat.valuationParity p c = 1) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
      Rat.oddPrimeHilbertSymbol p hpodd d c = 1 := by
  rw [quadraticNormRepresents_rat_padic_ramified_odd_iff_isSquare_neg_div
    hpodd hd hc hdpar hcpar]
  rw [Rat.isSquare_padic_iff_valuationParity_and_oddPrimeUnitCharacter
    hpodd (div_ne_zero (neg_ne_zero.mpr hc) hd)]
  rw [Rat.valuationParity_neg_div_eq_zero hc hd hcpar hdpar,
    Rat.oddPrimeUnitCharacter_neg_div hpodd c d hc hd]
  simp [Rat.oddPrimeHilbertSymbol, hdpar, hcpar, mul_assoc, mul_left_comm,
    mul_comm]

end PositiveDefiniteIntegralLattice

namespace PadicInt

/-- The valuation of a difference of nonzero p-adic integers with distinct
valuations is the minimum of their valuations. -/
lemma valuation_sub_eq_of_ne
    {p : ℕ} [Fact p.Prime] {a b : ℤ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.valuation ≠ b.valuation) :
    (a - b).valuation = min a.valuation b.valuation := by
  have hval :
      Padic.addValuation (a : ℚ_[p]) ≠ Padic.addValuation (b : ℚ_[p]) := by
    intro h
    apply hab
    simpa [Padic.addValuation, Padic.addValuationDef, ha, hb] using h
  have h := (Padic.addValuation (p := p)).map_add_of_distinct_val
    (x := (a : ℚ_[p])) (y := -(b : ℚ_[p])) (by simpa using hval)
  have hsub : a - b ≠ 0 := by
    intro hz
    apply hab
    rw [sub_eq_zero.mp hz]
  have hsubcoe : (↑a + -↑b : ℚ_[p]) ≠ 0 := by
    intro hz
    apply hsub
    apply Subtype.ext
    simpa [sub_eq_add_neg] using hz
  have hq :
      ((a : ℚ_[p]) - (b : ℚ_[p])).valuation =
        min (a : ℚ_[p]).valuation (b : ℚ_[p]).valuation := by
    apply WithTop.coe_eq_coe.mp
    simpa [sub_eq_add_neg, Padic.addValuation, Padic.addValuationDef, ha, hb,
      hsub, hsubcoe, PadicInt.coe_ne_zero] using h
  norm_cast at hq

/-- The residue of a p-adic integral unit is nonzero. -/
lemma toZMod_ne_zero_of_isUnit
    {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (hu : IsUnit u) :
    toZMod u ≠ 0 := by
  rw [toZMod_eq_residueField_comp_residue]
  intro hzero
  have : IsLocalRing.residue ℤ_[p] u = 0 := by
    apply residueField.injective
    simpa using hzero
  exact (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu this

/-- Negation does not change the valuation of a p-adic integer. -/
lemma valuation_neg
    {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) : (-u).valuation = u.valuation := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · have h := (Padic.addValuation (p := p)).map_neg (u : ℚ_[p])
    have hcu : (u : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hu
    have hncu : -(u : ℚ_[p]) ≠ 0 := neg_ne_zero.mpr hcu
    have hq : (-(u : ℚ_[p])).valuation = (u : ℚ_[p]).valuation := by
      change Padic.addValuationDef (-(u : ℚ_[p])) =
        Padic.addValuationDef (u : ℚ_[p]) at h
      simp only [Padic.addValuationDef, if_neg hncu, if_neg hcu] at h
      exact WithTop.coe_eq_coe.mp h
    norm_cast at hq

end PadicInt

namespace PositiveDefiniteIntegralLattice

/-- For a unit parameter with nonsquare residue, every nonzero integral
quadratic norm has even valuation. -/
theorem quadraticNorm_padicInt_valuation_even_of_unit_nonsquare_residue
    {p : ℕ} [Fact p.Prime] {d x y : ℤ_[p]}
    (hd : IsUnit d) (hdns : ¬ IsSquare (PadicInt.toZMod d))
    (hnorm : x * x - d * y * y ≠ 0) :
    Even (x * x - d * y * y).valuation := by
  have hd0 : d ≠ 0 := IsUnit.ne_zero hd
  have hdval : d.valuation = 0 := PadicInt.valuation_eq_zero_of_isUnit hd
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y ≠ 0 := by
      intro hy
      apply hnorm
      simp [hy]
    simp only [zero_mul, zero_sub]
    rw [PadicInt.valuation_neg,
      PadicInt.valuation_mul (mul_ne_zero hd0 hy) hy,
      PadicInt.valuation_mul hd0 hy, hdval]
    exact ⟨y.valuation, by omega⟩
  · rcases eq_or_ne y 0 with rfl | hy
    · simp only [mul_zero, sub_zero]
      rw [PadicInt.valuation_mul hx hx]
      exact ⟨x.valuation, by omega⟩
    · by_cases hvxy : x.valuation = y.valuation
      · let ux : ℤ_[p]ˣ := PadicInt.unitCoeff hx
        let uy : ℤ_[p]ˣ := PadicInt.unitCoeff hy
        let b : ℤ_[p] := (ux : ℤ_[p]) * ux - d * (uy : ℤ_[p]) * uy
        have huyres : PadicInt.toZMod (uy : ℤ_[p]) ≠ 0 :=
          PadicInt.toZMod_ne_zero_of_isUnit (Units.isUnit uy)
        have hbres : PadicInt.toZMod b ≠ 0 := by
          intro hb
          apply hdns
          have heq :
              PadicInt.toZMod (ux : ℤ_[p]) * PadicInt.toZMod (ux : ℤ_[p]) =
                PadicInt.toZMod d * PadicInt.toZMod (uy : ℤ_[p]) *
                  PadicInt.toZMod (uy : ℤ_[p]) := by
            have := hb
            simp [b] at this
            linear_combination this
          refine ⟨PadicInt.toZMod (ux : ℤ_[p]) /
              PadicInt.toZMod (uy : ℤ_[p]), ?_⟩
          rw [div_mul_div_comm]
          apply (eq_div_iff (mul_ne_zero huyres huyres)).2
          simpa [mul_assoc] using heq.symm
        have hbunit : IsUnit b := by
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
          intro hzero
          apply hbres
          rw [PadicInt.toZMod_eq_residueField_comp_residue]
          simp [hzero]
        have hb0 : b ≠ 0 := IsUnit.ne_zero hbunit
        have hbval : b.valuation = 0 :=
          PadicInt.valuation_eq_zero_of_isUnit hbunit
        let t : ℤ_[p] := (p : ℤ_[p]) ^ x.valuation
        have hxspec := PadicInt.unitCoeff_spec hx
        have hyspec := PadicInt.unitCoeff_spec hy
        have hyspec' :
            y = (uy : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation := by
          simpa [uy, hvxy] using hyspec
        have hfactor : x * x - d * y * y = b * (t * t) := by
          rw [hxspec, hyspec']
          simp only [ux, uy, t, b]
          ring
        rw [hfactor, PadicInt.valuation_mul hb0 (mul_ne_zero
          (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
          (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))),
          hbval, PadicInt.valuation_mul
            (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
            (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)),
          PadicInt.valuation_pow, PadicInt.valuation_p]
        exact ⟨x.valuation, by omega⟩
      · have hxx : x * x ≠ 0 := mul_ne_zero hx hx
        have hdyy : d * y * y ≠ 0 := mul_ne_zero (mul_ne_zero hd0 hy) hy
        have hvalx : (x * x).valuation = 2 * x.valuation := by
          rw [PadicInt.valuation_mul hx hx]
          omega
        have hvaly : (d * y * y).valuation = 2 * y.valuation := by
          rw [PadicInt.valuation_mul (mul_ne_zero hd0 hy) hy,
            PadicInt.valuation_mul hd0 hy, hdval]
          omega
        have hvals : (x * x).valuation ≠ (d * y * y).valuation := by
          rw [hvalx, hvaly]
          omega
        rw [PadicInt.valuation_sub_eq_of_ne hxx hdyy hvals, hvalx, hvaly]
        rcases lt_or_gt_of_ne hvxy with hlt | hgt
        · rw [min_eq_left (by omega)]
          exact ⟨x.valuation, by omega⟩
        · rw [min_eq_right (by omega)]
          exact ⟨y.valuation, by omega⟩

/-- For a unit parameter with nonsquare residue, every nonzero quadratic norm
over `ℚ_[p]` has even valuation. -/
theorem quadraticNorm_padic_valuation_even_of_unit_nonsquare_residue
    {p : ℕ} [Fact p.Prime] {d : ℤ_[p]} {x y : ℚ_[p]}
    (hd : IsUnit d) (hdns : ¬ IsSquare (PadicInt.toZMod d))
    (hnorm : x * x - (d : ℚ_[p]) * y * y ≠ 0) :
    Even (x * x - (d : ℚ_[p]) * y * y).valuation := by
  let q : ℚ_[p] := x * x - (d : ℚ_[p]) * y * y
  let m : ℕ := (max (-x.valuation) (-y.valuation)).toNat
  let s : ℚ_[p] := (p : ℚ_[p]) ^ m
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs0 : s ≠ 0 := pow_ne_zero _ hp0
  have hmx : -x.valuation ≤ (m : ℤ) :=
    le_trans (le_max_left _ _) (Int.self_le_toNat _)
  have hmy : -y.valuation ≤ (m : ℤ) :=
    le_trans (le_max_right _ _) (Int.self_le_toNat _)
  have hsval : s.valuation = (m : ℤ) := by
    simp [s, Padic.valuation_pow]
  have hsxval : 0 ≤ (s * x).valuation := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [Padic.valuation_mul hs0 hx, hsval]
      omega
  have hsyval : 0 ≤ (s * y).valuation := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [Padic.valuation_mul hs0 hy, hsval]
      omega
  let X : ℤ_[p] := ⟨s * x, (Padic.norm_le_one_iff_val_nonneg _).2 hsxval⟩
  let Y : ℤ_[p] := ⟨s * y, (Padic.norm_le_one_iff_val_nonneg _).2 hsyval⟩
  have hfactor :
      ((X * X - d * Y * Y : ℤ_[p]) : ℚ_[p]) = s ^ 2 * q := by
    change (s * x) * (s * x) - (d : ℚ_[p]) * (s * y) * (s * y) =
      s ^ 2 * (x * x - (d : ℚ_[p]) * y * y)
    ring
  have hq0 : q ≠ 0 := hnorm
  have hscaled0 : X * X - d * Y * Y ≠ 0 := by
    intro hz
    have hz' := congrArg Subtype.val hz
    rw [hfactor] at hz'
    exact (mul_ne_zero (pow_ne_zero _ hs0) hq0) hz'
  have heven := quadraticNorm_padicInt_valuation_even_of_unit_nonsquare_residue
    hd hdns hscaled0
  have hvaleq :
      ((X * X - d * Y * Y).valuation : ℤ) =
        2 * (m : ℤ) + q.valuation := by
    rw [← PadicInt.valuation_coe, hfactor,
      Padic.valuation_mul (pow_ne_zero _ hs0) hq0,
      Padic.valuation_pow, hsval]
    omega
  obtain ⟨k, hk⟩ := heven
  have hkz := congrArg (fun n : ℕ => (n : ℤ)) hk
  refine ⟨(k : ℤ) - m, ?_⟩
  change q.valuation = ((k : ℤ) - m) + ((k : ℤ) - m)
  omega

/-- The norm group of an odd-prime unramified nonsplit quadratic algebra
consists exactly of the nonzero p-adic elements with even valuation. -/
theorem quadraticNormRepresents_padic_unramified_iff_valuation_even
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d : ℤ_[p]} (hd : IsUnit d)
    (hdns : ¬ IsSquare (PadicInt.toZMod d)) {c : ℚ_[p]} (hc : c ≠ 0) :
    quadraticNormRepresents (d : ℚ_[p]) c ↔ Even c.valuation := by
  constructor
  · rw [quadraticNormRepresents_iff_exists]
    rintro ⟨x, y, hxy⟩
    subst c
    exact quadraticNorm_padic_valuation_even_of_unit_nonsquare_residue
      hd hdns hc
  · intro heven
    let u : ℚ_[p] := c * (p : ℚ_[p]) ^ (-c.valuation)
    have hp0 : (p : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hu : ‖u‖ = 1 := by
      simp [u, hc, Padic.norm_eq_zpow_neg_valuation]
      exact inv_mul_cancel₀ (zpow_ne_zero _ (by
        exact_mod_cast (Fact.out : p.Prime).ne_zero))
    let cu : ℤ_[p]ˣ := PadicInt.mkUnits hu
    have hcu : IsUnit (cu : ℤ_[p]) := Units.isUnit cu
    have hrep := quadraticNormRepresents_padic_units_of_nonsquare_residue
      hpodd hd hcu hdns
    rw [quadraticNormRepresents_iff_exists] at hrep ⊢
    obtain ⟨x, y, hxy⟩ := hrep
    obtain ⟨k, hk⟩ := heven
    let t : ℚ_[p] := (p : ℚ_[p]) ^ k
    refine ⟨t * x, t * y, ?_⟩
    have hcuval : ((cu : ℤ_[p]) : ℚ_[p]) = u := PadicInt.mkUnits_eq hu
    have hval : c.valuation = 2 * k := by omega
    calc
      t * x * (t * x) - (d : ℚ_[p]) * (t * y) * (t * y) =
          t ^ 2 * (x * x - (d : ℚ_[p]) * y * y) := by ring
      _ = t ^ 2 * ((cu : ℤ_[p]) : ℚ_[p]) := by rw [hxy]
      _ = ((p : ℚ_[p]) ^ k) ^ 2 *
          (c * (p : ℚ_[p]) ^ (-c.valuation)) := by rw [hcuval]
      _ = c := by
        rw [hval, ← zpow_natCast, ← zpow_mul]
        calc
          (p : ℚ_[p]) ^ (k * (2 : ℤ)) *
              (c * (p : ℚ_[p]) ^ (-(2 * k))) =
              c * ((p : ℚ_[p]) ^ (k * 2) *
                (p : ℚ_[p]) ^ (-(2 * k))) := by ring
          _ = c * (p : ℚ_[p]) ^ (k * 2 + -(2 * k)) := by
            rw [← zpow_add₀ hp0]
          _ = c := by ring_nf; simp

/-- For a rational unit parameter in the unramified nonsquare class, the
quadratic norm criterion agrees with the explicit odd-prime Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_unramified_iff_hilbertSymbol
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℚ} (hd0 : d ≠ 0) (hc0 : c ≠ 0)
    (hdval : padicValRat p d = 0)
    (hdchar : Rat.oddPrimeUnitCharacter p d = -1) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
      Rat.oddPrimeHilbertSymbol p hpodd d c = 1 := by
  let D : ℤ_[p] := ⟨(d : ℚ_[p]), (Padic.norm_le_one_iff_val_nonneg _).2 (by
    simp [Padic.valuation_ratCast, hdval])⟩
  have hDunit : IsUnit D := by
    rw [PadicInt.isUnit_iff]
    change ‖(d : ℚ_[p])‖ = 1
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hd0),
      Padic.valuation_ratCast, hdval]
    simp
  have hDns : ¬ IsSquare (PadicInt.toZMod D) := by
    intro hsq
    have hDsquare : IsSquare D :=
      (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd hDunit).2 hsq
    have hdpSquare : IsSquare (d : ℚ_[p]) := by
      obtain ⟨z, hz⟩ := hDsquare
      exact ⟨(z : ℚ_[p]), congrArg Subtype.val hz⟩
    have hcharOne :=
      (Rat.isSquare_padic_iff_oddPrimeUnitCharacter_eq_one_of_valuation_eq_zero
        hpodd hd0 hdval).1 hdpSquare
    omega
  have hnorm :
      quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
        Even (padicValRat p c) := by
    have hcp : (c : ℚ_[p]) ≠ 0 := by exact_mod_cast hc0
    have h := quadraticNormRepresents_padic_unramified_iff_valuation_even
      (c := (c : ℚ_[p])) hpodd hDunit hDns hcp
    simpa [D, Padic.valuation_ratCast] using h
  have hdpar : Rat.valuationParity p d = 0 := by
    simp [Rat.valuationParity, hdval]
  have hsymbol :
      Rat.oddPrimeHilbertSymbol p hpodd d c =
        (-1 : ℤ) ^ Rat.valuationParity p c := by
    simp [Rat.oddPrimeHilbertSymbol, hdpar, hdchar]
  rw [hnorm]
  constructor
  · intro heven
    have hpar : Rat.valuationParity p c = 0 := by
      have hem := Int.even_iff.mp heven
      simp [Rat.valuationParity, hem]
    rw [hsymbol, hpar]
    norm_num
  · intro hs
    rcases Rat.valuationParity_eq_zero_or_one p c with hpar | hpar
    · exact Int.even_iff.mpr (by simpa [Rat.valuationParity] using hpar)
    · rw [hsymbol, hpar] at hs
      norm_num at hs

/-- For every nonzero rational parameter and target, the quadratic norm
criterion over an odd p-adic field agrees with the explicit rational
odd-prime Hilbert-symbol formula. -/
theorem quadraticNormRepresents_rat_padic_iff_oddPrimeHilbertSymbol_eq_one
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
      Rat.oddPrimeHilbertSymbol p hpodd d c = 1 := by
  rcases Rat.valuationParity_eq_zero_or_one p d with hdpar | hdpar
  · rcases (sq_eq_one_iff.mp
      (Rat.oddPrimeUnitCharacter_sq (p := p) hd)) with hdchar | hdchar
    · have hdsquare : IsSquare (d : ℚ_[p]) :=
        (Rat.isSquare_padic_iff_valuationParity_and_oddPrimeUnitCharacter
          hpodd hd).2 ⟨hdpar, hdchar⟩
      have hdp0 : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd
      have hnorm : quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) :=
        quadraticNormRepresents_of_isSquare (d : ℚ_[p]) (c : ℚ_[p])
          (by rw [ringChar.eq_zero]; norm_num) hdp0 hdsquare
      constructor
      · intro _
        simp [Rat.oddPrimeHilbertSymbol, hdpar, hdchar]
      · intro _
        exact hnorm
    · obtain ⟨x, hx, hxval⟩ :=
        Rat.exists_square_normalization_of_valuationParity_eq_zero hd hdpar
      have hdx : d * x ^ 2 ≠ 0 := mul_ne_zero hd (pow_ne_zero 2 hx)
      have hdxchar : Rat.oddPrimeUnitCharacter p (d * x ^ 2) = -1 := by
        rw [Rat.oddPrimeUnitCharacter_mul_sq d x hd hx, hdchar]
      have hlocal :=
        quadraticNormRepresents_rat_padic_unramified_iff_hilbertSymbol
          hpodd hdx hc hxval hdxchar
      have hxpadic : (x : ℚ_[p]) ≠ 0 := by exact_mod_cast hx
      have htransport :
          quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
            quadraticNormRepresents ((d * x ^ 2 : ℚ) : ℚ_[p])
              (c : ℚ_[p]) := by
        simpa using
          (quadraticNormRepresents_iff_mul_sq_parameter
            (K := ℚ_[p]) (d := (d : ℚ_[p])) (c := (c : ℚ_[p]))
              (s := (x : ℚ_[p])) hxpadic)
      calc
        quadraticNormRepresents (d : ℚ_[p]) (c : ℚ_[p]) ↔
            quadraticNormRepresents ((d * x ^ 2 : ℚ) : ℚ_[p])
              (c : ℚ_[p]) := htransport
        _ ↔ Rat.oddPrimeHilbertSymbol p hpodd (d * x ^ 2) c = 1 := hlocal
        _ ↔ Rat.oddPrimeHilbertSymbol p hpodd d c = 1 := by
          rw [Rat.oddPrimeHilbertSymbol_mul_sq_left p hpodd d c x hd hx]
  · rcases Rat.valuationParity_eq_zero_or_one p c with hcpar | hcpar
    · exact quadraticNormRepresents_rat_padic_ramified_even_iff_hilbertSymbol
        hpodd hd hc hdpar hcpar
    · exact quadraticNormRepresents_rat_padic_ramified_odd_iff_hilbertSymbol
        hpodd hd hc hdpar hcpar

end PositiveDefiniteIntegralLattice
