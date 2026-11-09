import SMSFormula.BinaryFractionalIdeal
import SMSFormula.BinaryProperNormalization

/-!
# Proper binary coordinate changes and principal ideal rescaling

The ideal bases (a,θ) and (d,θ') retain the original integer coordinates.
A proper polynomial isometry gives an integral identity after multiplication
by a. Surjectivity of its original matrix then gives principal ideal scaling.
-/

open Matrix

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

private lemma polar_matrix_congruence (a b c d e f : ℤ)
    (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    U.transpose * (!![2*d,e;e,2*f] : Matrix (Fin 2) (Fin 2) ℤ) * U = !![2*a,b;b,2*c] := by
  have hA := hp ![1,0]
  have hC := hp ![0,1]
  have hS := hp ![1,1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hA hC hS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · nlinarith [hA]
  · nlinarith [hA,hC,hS]
  · nlinarith [hA,hC,hS]
  · nlinarith [hC]

/-- Proper polynomial transport preserves the exact primitive discriminant. -/
theorem discriminant_eq_of_proper_polynomial_matrix (a b c d e f : ℤ)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    b ^ 2 - 4*a*c = e ^ 2 - 4*d*f := by
  have h := congrArg Matrix.det (polar_matrix_congruence a b c d e f U hp)
  simp only [Matrix.det_mul, Matrix.det_transpose, hd, one_mul, mul_one, Matrix.det_fin_two] at h
  norm_num at h
  nlinarith

private lemma proper_polynomial_relations (a b c d e f k : ℤ)
    (hk : b = e + 2*k) (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    a * U 0 1 = k * U 0 0 - f * U 1 0 ∧
      a * U 1 1 = d * U 0 0 + (e+k)*U 1 0 := by
  let H : Matrix (Fin 2) (Fin 2) ℤ := !![2*a,b;b,2*c]
  let H' : Matrix (Fin 2) (Fin 2) ℤ := !![2*d,e;e,2*f]
  have hc : U.transpose * H' * U = H := polar_matrix_congruence a b c d e f U hp
  have hlin : H' * U = U.adjugate.transpose * H := by
    have h := congrArg (fun M => M * U.adjugate) hc
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one] at h
    have ht := congrArg Matrix.transpose h
    have hs : H.transpose = H := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have hs' : H'.transpose = H' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, hs'] using ht
  have h00 := congrArg (fun M => M 0 0) hlin
  have h10 := congrArg (fun M => M 1 0) hlin
  simp [H,H', Matrix.mul_apply, Matrix.adjugate_fin_two,
    Matrix.transpose_apply, Fin.sum_univ_two] at h00 h10
  rw [hk] at h00 h10
  constructor <;> nlinarith

/-- The integral comparison identity between ideal bases. The scalar is the
actual first target column, not a presumed isometry or an analytic certificate. -/
theorem scaled_coordinates_of_proper_polynomial_matrix (a b c d e f k : ℤ)
    (ha : a ≠ 0) (hdt : d ≠ 0) (hk : b = e + 2*k)
    (hac : a*c = d*f + e*k + k^2)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2)
    (x : Fin 2 → ℤ) :
    (a : CoefficientOrder d e f) * (coordinates d e f hdt (U.mulVec x)).val =
      (⟨d * U 0 0, U 1 0⟩ : CoefficientOrder d e f) *
        coefficientOrderEquivOfShift a b c d e f k hk hac (coordinates a b c ha x).val := by
  obtain ⟨hq,hs⟩ := proper_polynomial_relations a b c d e f k hk U hd hp
  rw [coordinates_apply, coordinates_apply]
  apply QuadraticAlgebra.ext
  · change a * (d * (U.mulVec x) 0) + (-d*f)*0*(U.mulVec x) 1 = _
    simp only [coefficientOrderEquivOfShift, AlgEquiv.coe_mk,
      QuadraticAlgebra.re_mul]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (d * x 1) * hq
  · simp [coefficientOrderEquivOfShift, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (x 1) * hs

/-- The comparison scalar has exactly norm ad, hence is nonzero when both
leading coefficients are nonzero. No sign, conductor or maximality premise is used. -/
theorem norm_first_column_of_polynomial_matrix (a b c d e f : ℤ)
    (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    (⟨d * U 0 0, U 1 0⟩ : CoefficientOrder d e f).norm = d*a := by
  have h := hp ![1,0]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  rw [QuadraticAlgebra.norm_def]
  simp only
  linear_combination d * h

/-- Proper coordinate transport gives the exact principal rescaling of
the original two ideals in the TARGET coefficient order. -/
theorem principal_scaling_of_proper_polynomial_matrix (a b c d e f k : ℤ)
    (ha : a ≠ 0) (hdt : d ≠ 0) (hk : b = e + 2*k)
    (hac : a*c = d*f + e*k + k^2)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    Ideal.span {(a : CoefficientOrder d e f)} * normIdeal d e f =
      Ideal.span {(⟨d * U 0 0, U 1 0⟩ : CoefficientOrder d e f)} *
        Ideal.map (coefficientOrderEquivOfShift a b c d e f k hk hac).toRingHom (normIdeal a b c) := by
  let E := coefficientOrderEquivOfShift a b c d e f k hk hac
  have hunit : IsUnit U := by rw [Matrix.isUnit_iff_isUnit_det, hd]; exact isUnit_one
  let V := Matrix.toLinearEquiv' U hunit.invertible
  have hbasis := scaled_coordinates_of_proper_polynomial_matrix a b c d e f k ha hdt hk hac U hd hp
  apply le_antisymm
  · intro z hz
    obtain ⟨y,hy,hz⟩ := Ideal.mem_span_singleton_mul.mp hz
    let t := (coordinates d e f hdt).symm ⟨y,hy⟩
    let x := V.symm t
    have hV : U.mulVec x = t := V.apply_symm_apply t
    have hcoord : (coordinates d e f hdt (U.mulVec x)).val = y := by
      rw [hV]
      exact congrArg Subtype.val ((coordinates d e f hdt).apply_symm_apply ⟨y,hy⟩)
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨E (coordinates a b c ha x).val,
      Ideal.mem_map_of_mem E.toRingHom (coordinates a b c ha x).prop, ?_⟩
    rw [← hbasis x, hcoord]
    exact hz
  · intro z hz
    obtain ⟨y,hy,hz⟩ := Ideal.mem_span_singleton_mul.mp hz
    obtain ⟨s,hs,he⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hy
    let x := (coordinates a b c ha).symm ⟨s,hs⟩
    have hcoord : (coordinates a b c ha x).val = s :=
      congrArg Subtype.val ((coordinates a b c ha).apply_symm_apply ⟨s,hs⟩)
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨(coordinates d e f hdt (U.mulVec x)).val,
      (coordinates d e f hdt (U.mulVec x)).prop, ?_⟩
    rw [hbasis x, hcoord]
    change (⟨d * U 0 0, U 1 0⟩ : CoefficientOrder d e f) * E s = z
    change E s = y at he
    rw [he]
    exact hz

/-- The canonical equal-discriminant translation supplies all shift witnesses.
The discriminant equality itself follows from the given proper matrix. -/
theorem principal_scaling_of_proper_polynomial_matrix_discriminant (a b c d e f : ℤ)
    (ha : a ≠ 0) (hdt : d ≠ 0)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    Ideal.span {(a : CoefficientOrder d e f)} * normIdeal d e f =
      Ideal.span {(⟨d * U 0 0, U 1 0⟩ : CoefficientOrder d e f)} *
        Ideal.map (coefficientOrderEquivOfDiscriminant a b c d e f
          (discriminant_eq_of_proper_polynomial_matrix a b c d e f U hd hp)).toRingHom
          (normIdeal a b c) := by
  unfold coefficientOrderEquivOfDiscriminant
  apply principal_scaling_of_proper_polynomial_matrix
  · exact ha
  · exact hdt
  · exact hd
  · exact hp

private lemma trace_difference_even (a b c d e f : ℤ)
    (hD : b^2 - 4*a*c = e^2 - 4*d*f) : 2 ∣ b-e := by
  have h := congrArg (Int.castRingHom (ZMod 2)) hD
  have hh : (b : ZMod 2)^2 = (e : ZMod 2)^2 := by
    have hn : (4 : ZMod 2) = 0 := by decide
    simpa [hn] using h
  have hs (x : ZMod 2) : x^2 = x := by fin_cases x <;> decide
  rw [hs, hs] at hh
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub e b 2).mp hh.symm

/-- Canonical order translations compose exactly. This keeps the choice of
coefficient presentation out of the later common-order class comparison. -/
theorem coefficientOrderEquivOfDiscriminant_trans (a b c d e f l m n : ℤ)
    (hD : b^2 - 4*a*c = e^2 - 4*d*f)
    (hD' : e^2 - 4*d*f = m^2 - 4*l*n) :
    (coefficientOrderEquivOfDiscriminant a b c d e f hD).trans
      (coefficientOrderEquivOfDiscriminant d e f l m n hD') =
        coefficientOrderEquivOfDiscriminant a b c l m n (hD.trans hD') := by
  have hdiv := Int.mul_ediv_cancel' (trace_difference_even a b c d e f hD)
  have hk : (b-e)/2 + (e-m)/2 = (b-m)/2 := by omega
  apply AlgEquiv.ext
  intro z
  apply QuadraticAlgebra.ext
  · change (z.re + (b-e)/2*z.im) + (e-m)/2*z.im = z.re + (b-m)/2*z.im
    linear_combination z.im * hk
  · rfl

/-- Both coefficient ideals can be compared in the same discriminant order.
This is a principal-scaling statement, not a genus or Picard-class theorem. -/
theorem principal_scaling_in_discriminantOrder (a b c d e f D : ℤ)
    (ha : a ≠ 0) (hdt : d ≠ 0) (hres : D % 4 = 0 ∨ D % 4 = 1)
    (hD : b^2 - 4*a*c = D)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    let hDL := (discriminant_eq_of_proper_polynomial_matrix a b c d e f U hd hp).symm.trans hD
    let E := coefficientOrderEquivDiscriminantOrder a b c D hres hD
    let E' := coefficientOrderEquivDiscriminantOrder d e f D hres hDL
    Ideal.span {(a : DiscriminantOrder D)} * Ideal.map E'.toRingHom (normIdeal d e f) =
      Ideal.span {E' (⟨d * U 0 0, U 1 0⟩ : CoefficientOrder d e f)} *
        Ideal.map E.toRingHom (normIdeal a b c) := by
  dsimp only
  let hDE := discriminant_eq_of_proper_polynomial_matrix a b c d e f U hd hp
  let E' := coefficientOrderEquivDiscriminantOrder d e f D hres (hDE.symm.trans hD)
  have h := congrArg (Ideal.map E'.toRingHom)
    (principal_scaling_of_proper_polynomial_matrix_discriminant a b c d e f ha hdt U hd hp)
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton] at h
  have hc := coefficientOrderEquivOfDiscriminant_trans a b c d e f
    1 (D%2) (((D%2)^2-D)/4) hDE
    ((hDE.symm.trans hD).trans (discriminantOrder_coefficients D hres).symm)
  have hm : E'.toRingHom.comp
      (coefficientOrderEquivOfDiscriminant a b c d e f hDE).toRingHom =
      (coefficientOrderEquivDiscriminantOrder a b c D hres hD).toRingHom := by
    apply RingHom.ext
    intro z
    exact congrArg (fun E : CoefficientOrder a b c ≃ₐ[ℤ] DiscriminantOrder D => E z) hc
  rw [Ideal.map_map, hm] at h
  simpa only [map_intCast] using h

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- Every original proper global lattice isometry gives nonzero principal
rescaling of the actual norm ideals. The order translation preserves both
the imaginary coordinate and the norm; no genus or class certificate is supplied. -/
theorem IsProperGlobalIsometry.exists_principal_scaling_binaryNormIdeals
    {K L : PositiveDefiniteIntegralLattice 2} (h : K.IsProperGlobalIsometry L) :
    ∃ E : K.binaryCoefficientOrder ≃ₐ[ℤ] L.binaryCoefficientOrder,
      (∀ z, (E z).im = z.im) ∧ (∀ z, (E z).norm = z.norm) ∧
      ∃ x y : L.binaryCoefficientOrder, x ≠ 0 ∧ y ≠ 0 ∧
        Ideal.span {x} * L.binaryNormIdeal =
          Ideal.span {y} * Ideal.map E.toRingHom K.binaryNormIdeal := by
  obtain ⟨U, hU, hd, hform⟩ := h
  let a := K.pairingMatrix 0 0 / (K.binaryContent : ℤ)
  let b := 2 * K.pairingMatrix 0 1 / (K.binaryContent : ℤ)
  let c := K.pairingMatrix 1 1 / (K.binaryContent : ℤ)
  let d := L.pairingMatrix 0 0 / (L.binaryContent : ℤ)
  let e := 2 * L.pairingMatrix 0 1 / (L.binaryContent : ℤ)
  let f := L.pairingMatrix 1 1 / (L.binaryContent : ℤ)
  have ha : a ≠ 0 := ne_of_gt K.binaryPrimitivePolynomial_leading_pos
  have hdt : d ≠ 0 := ne_of_gt L.binaryPrimitivePolynomial_leading_pos
  have hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
    intro x
    have heq := (binaryPrimitivePolynomialIsometryEquivOfMatrix K L U hU hform).map_app x
    rw [binaryPrimitivePolynomialIsometryEquivOfMatrix_apply] at heq
    simpa only [binaryPrimitivePolynomial_apply] using heq
  let E := BinaryNormIdeal.coefficientOrderEquivOfDiscriminant a b c d e f
    (BinaryNormIdeal.discriminant_eq_of_proper_polynomial_matrix a b c d e f U hd hp)
  refine ⟨E, ?_, ?_, (a : L.binaryCoefficientOrder), ⟨d * U 0 0, U 1 0⟩, ?_, ?_, ?_⟩
  · intro z
    rfl
  · exact BinaryNormIdeal.norm_coefficientOrderEquivOfDiscriminant a b c d e f _
  · intro hz
    have hh := congrArg QuadraticAlgebra.re hz
    exact ha (by simpa using hh)
  · intro hz
    have hn := BinaryNormIdeal.norm_first_column_of_polynomial_matrix a b c d e f U hp
    rw [hz] at hn
    exact mul_ne_zero hdt ha (by simpa using hn.symm)
  · exact BinaryNormIdeal.principal_scaling_of_proper_polynomial_matrix_discriminant
      a b c d e f ha hdt U hd hp


/-- The forward principal-scaling bridge in the actual common discriminant
order. Both maps preserve the original generator orientation and norm. -/
theorem IsProperGlobalIsometry.exists_principal_scaling_binaryDiscriminantNormIdeals
    {K L : PositiveDefiniteIntegralLattice 2} (h : K.IsProperGlobalIsometry L) :
    ∃ E : L.binaryCoefficientOrder ≃ₐ[ℤ]
        BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant,
      (∀ z, (E z).im = z.im) ∧ (∀ z, (E z).norm = z.norm) ∧
      ∃ x y : BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant,
        x ≠ 0 ∧ y ≠ 0 ∧
        Ideal.span {x} * Ideal.map E.toRingHom L.binaryNormIdeal =
          Ideal.span {y} * K.binaryDiscriminantNormIdeal := by
  obtain ⟨U, hU, hd, hform⟩ := h
  let a := K.pairingMatrix 0 0 / (K.binaryContent : ℤ)
  let b := 2 * K.pairingMatrix 0 1 / (K.binaryContent : ℤ)
  let c := K.pairingMatrix 1 1 / (K.binaryContent : ℤ)
  let d := L.pairingMatrix 0 0 / (L.binaryContent : ℤ)
  let e := 2 * L.pairingMatrix 0 1 / (L.binaryContent : ℤ)
  let f := L.pairingMatrix 1 1 / (L.binaryContent : ℤ)
  have ha : a ≠ 0 := ne_of_gt K.binaryPrimitivePolynomial_leading_pos
  have hdt : d ≠ 0 := ne_of_gt L.binaryPrimitivePolynomial_leading_pos
  have hp : ∀ x : Fin 2 → ℤ,
      d * (U.mulVec x) 0 ^ 2 + e * (U.mulVec x) 0 * (U.mulVec x) 1 +
        f * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
    intro x
    have heq := (binaryPrimitivePolynomialIsometryEquivOfMatrix K L U hU hform).map_app x
    rw [binaryPrimitivePolynomialIsometryEquivOfMatrix_apply] at heq
    simpa only [binaryPrimitivePolynomial_apply] using heq
  let hD := BinaryNormIdeal.discriminant_eq_of_proper_polynomial_matrix a b c d e f U hd hp
  let E := BinaryNormIdeal.coefficientOrderEquivDiscriminantOrder d e f
    K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four hD.symm
  refine ⟨E, ?_, ?_, (a : BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant),
    E (⟨d * U 0 0, U 1 0⟩ : L.binaryCoefficientOrder), ?_, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    apply BinaryNormIdeal.norm_coefficientOrderEquivOfDiscriminant
  · intro hz
    have hh := congrArg QuadraticAlgebra.re hz
    exact ha (by simpa using hh)
  · intro hz
    have hn := BinaryNormIdeal.norm_first_column_of_polynomial_matrix a b c d e f U hp
    have hz' : (⟨d * U 0 0, U 1 0⟩ : L.binaryCoefficientOrder) = 0 :=
      E.injective (hz.trans (map_zero E).symm)
    rw [hz'] at hn
    exact mul_ne_zero hdt ha (by simpa using hn.symm)
  · have hh := BinaryNormIdeal.principal_scaling_in_discriminantOrder a b c d e f
      K.binaryPrimitiveDiscriminant ha hdt K.binaryPrimitiveDiscriminant_mod_four rfl U hd hp
    have heq : Ideal.map K.binaryCoefficientOrderEquivDiscriminantOrder.toRingHom K.binaryNormIdeal =
        K.binaryDiscriminantNormIdeal :=
      Ideal.map_comap_of_equiv K.binaryCoefficientOrderEquivDiscriminantOrder.toRingEquiv
    rw [← heq]
    exact hh

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.discriminant_eq_of_proper_polynomial_matrix
#assert_standard_axioms BinaryNormIdeal.scaled_coordinates_of_proper_polynomial_matrix
#assert_standard_axioms BinaryNormIdeal.norm_first_column_of_polynomial_matrix
#assert_standard_axioms BinaryNormIdeal.principal_scaling_of_proper_polynomial_matrix
#assert_standard_axioms BinaryNormIdeal.principal_scaling_of_proper_polynomial_matrix_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsProperGlobalIsometry.exists_principal_scaling_binaryNormIdeals

#assert_standard_axioms BinaryNormIdeal.coefficientOrderEquivOfDiscriminant_trans
#assert_standard_axioms BinaryNormIdeal.principal_scaling_in_discriminantOrder

#assert_standard_axioms PositiveDefiniteIntegralLattice.IsProperGlobalIsometry.exists_principal_scaling_binaryDiscriminantNormIdeals
