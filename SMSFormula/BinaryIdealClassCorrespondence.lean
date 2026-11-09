import SMSFormula.BinaryProperIdealScaling

/-!
# Recovering proper binary coordinates from principal ideal scaling

The reverse comparison uses the actual ideal bases. Positive norms in a
negative-discriminant order force the recovered integer matrix to have
positive determinant. No maximal-order or class-number theorem is assumed.
-/

open Matrix

namespace BinaryNormIdeal

/-- Every nonzero element of a negative-discriminant integral order has
strictly positive norm, including in nonmaximal and dyadic cases. -/
theorem norm_pos_of_discriminant_neg (a b c : ℤ) (hD : b^2 - 4*a*c < 0)
    (z : CoefficientOrder a b c) (hz : z ≠ 0) : 0 < z.norm := by
  have hn : 4*z.norm = (2*z.re+b*z.im)^2 - (b^2-4*a*c)*z.im^2 := by
    rw [QuadraticAlgebra.norm_def]
    ring
  by_cases hi : z.im = 0
  · have hr : z.re ≠ 0 := by
      intro hr
      apply hz
      apply QuadraticAlgebra.ext <;> simp [hr,hi]
    rw [hi] at hn
    nlinarith [sq_pos_of_ne_zero hr]
  · have hs := sq_pos_of_ne_zero hi
    nlinarith [sq_nonneg (2*z.re+b*z.im), mul_neg_of_neg_of_pos hD hs]

private theorem equiv_of_equal_ranges {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (F G : M →ₗ[ℤ] N)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (h : F.range = G.range) :
    ∃ e : M ≃ₗ[ℤ] M, ∀ v, F (e v) = G v := by
  let e := (LinearEquiv.ofInjective G hG).trans
    ((LinearEquiv.ofEq _ _ h.symm).trans (LinearEquiv.ofInjective F hF).symm)
  refine ⟨e, ?_⟩
  intro v
  exact LinearEquiv.ofInjective_symm_apply F (h := hF) _

/-- Equality of nonzero principal rescalings recovers an integer coordinate
equivalence with the exact multiplied ideal-coordinate identity. -/
theorem exists_coordinates_equiv_of_principal_scaling (a b c d e f k : ℤ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hD : e^2 - 4*d*f < 0)
    (hk : b = e+2*k) (hac : a*c = d*f+e*k+k^2)
    (x y : CoefficientOrder d e f) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Ideal.span {x} * normIdeal d e f =
      Ideal.span {y} * Ideal.map
        (coefficientOrderEquivOfShift a b c d e f k hk hac).toRingHom (normIdeal a b c)) :
    ∃ V : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ), ∀ v,
      x * (coordinates d e f hd (V v)).val =
        y * coefficientOrderEquivOfShift a b c d e f k hk hac (coordinates a b c ha v).val := by
  letI := coefficientOrder_isDomain d e f hD
  let E := coefficientOrderEquivOfShift a b c d e f k hk hac
  let F : (Fin 2 → ℤ) →ₗ[ℤ] CoefficientOrder d e f :=
    { toFun v := x * (coordinates d e f hd v).val
      map_add' := by intros; simp [mul_add]
      map_smul' := by
        intro r v
        apply QuadraticAlgebra.ext <;> simp <;> ring }
  let G : (Fin 2 → ℤ) →ₗ[ℤ] CoefficientOrder d e f :=
    { toFun v := y * E (coordinates a b c ha v).val
      map_add' := by intros; simp [mul_add]
      map_smul' := by
        intro r v
        apply QuadraticAlgebra.ext <;> simp [E, coefficientOrderEquivOfShift] <;> ring }
  have hF : Function.Injective F := by
    intro u v huv
    exact (coordinates d e f hd).injective (Subtype.ext (mul_left_cancel₀ hx huv))
  have hG : Function.Injective G := by
    intro u v huv
    exact (coordinates a b c ha).injective (Subtype.ext (E.injective (mul_left_cancel₀ hy huv)))
  have hFr (z) : z ∈ F.range ↔ z ∈ Ideal.span {x} * normIdeal d e f := by
    constructor
    · rintro ⟨v,rfl⟩
      exact Ideal.mem_span_singleton_mul.mpr ⟨_, (coordinates d e f hd v).prop, rfl⟩
    · intro hz
      obtain ⟨w,hw,hwz⟩ := Ideal.mem_span_singleton_mul.mp hz
      refine ⟨(coordinates d e f hd).symm ⟨w,hw⟩, ?_⟩
      change x * _ = z
      rw [(coordinates d e f hd).apply_symm_apply]
      exact hwz
  have hGr (z) : z ∈ G.range ↔ z ∈ Ideal.span {y} * Ideal.map E.toRingHom (normIdeal a b c) := by
    constructor
    · rintro ⟨v,rfl⟩
      exact Ideal.mem_span_singleton_mul.mpr ⟨_,
        Ideal.mem_map_of_mem E.toRingHom (coordinates a b c ha v).prop, rfl⟩
    · intro hz
      obtain ⟨w,hw,hwz⟩ := Ideal.mem_span_singleton_mul.mp hz
      obtain ⟨t,ht,htw⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hw
      refine ⟨(coordinates a b c ha).symm ⟨t,ht⟩, ?_⟩
      change y * E _ = z
      rw [(coordinates a b c ha).apply_symm_apply]
      change E t = w at htw
      rw [htw]
      exact hwz
  have hr : F.range = G.range := by
    ext z
    rw [hFr,hGr]
    exact h ▸ Iff.rfl
  exact equiv_of_equal_ranges F G hF hG hr

/-- Determinants of the exact multiplied ideal bases keep the leading
coefficient scale and the orientation of the generator translation. -/
theorem determinant_of_scaled_coordinates (a b c d e f k : ℤ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hk : b = e+2*k)
    (hac : a*c = d*f+e*k+k^2) (x y : CoefficientOrder d e f)
    (U : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ v : Fin 2 → ℤ, x * (coordinates d e f hd (U.mulVec v)).val =
      y * coefficientOrderEquivOfShift a b c d e f k hk hac (coordinates a b c ha v).val) :
    x.norm * d * U.det = y.norm * a := by
  let X : Matrix (Fin 2) (Fin 2) ℤ := !![x.re, -d*f*x.im; x.im, x.re+e*x.im]
  let Y : Matrix (Fin 2) (Fin 2) ℤ := !![y.re, -d*f*y.im; y.im, y.re+e*y.im]
  have hm : X * !![d,0;0,1] * U = Y * !![a,k;0,1] := by
    have h0 := h ![1,0]
    have h1 := h ![0,1]
    have hr0 := congrArg QuadraticAlgebra.re h0
    have hi0 := congrArg QuadraticAlgebra.im h0
    have hr1 := congrArg QuadraticAlgebra.re h1
    have hi1 := congrArg QuadraticAlgebra.im h1
    simp [coordinates_apply, coefficientOrderEquivOfShift, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at hr0 hi0 hr1 hi1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X,Y, Matrix.mul_apply, Fin.sum_univ_two]
    · nlinarith only [hr0]
    · nlinarith only [hr1]
    · nlinarith only [hi0]
    · nlinarith only [hi1]
  have hh := congrArg Matrix.det hm
  have hX : X.det = x.norm := by
    simp [X, Matrix.det_fin_two, QuadraticAlgebra.norm_def]
    ring
  have hY : Y.det = y.norm := by
    simp [Y, Matrix.det_fin_two, QuadraticAlgebra.norm_def]
    ring
  simp only [Matrix.det_mul, hX, hY] at hh
  simpa [Matrix.det_fin_two] using hh

/-- Positive leading coefficients and nonzero principal factors force proper
orientation and exact primitive polynomial preservation in the reverse direction. -/
theorem exists_proper_polynomial_matrix_of_principal_scaling (a b c d e f k : ℤ)
    (ha : 0 < a) (hd : 0 < d) (hD : e^2 - 4*d*f < 0)
    (hk : b = e+2*k) (hac : a*c = d*f+e*k+k^2)
    (x y : CoefficientOrder d e f) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Ideal.span {x} * normIdeal d e f =
      Ideal.span {y} * Ideal.map
        (coefficientOrderEquivOfShift a b c d e f k hk hac).toRingHom (normIdeal a b c)) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U ∧ U.det = 1 ∧
      ∀ v : Fin 2 → ℤ,
        d * (U.mulVec v) 0 ^ 2 + e * (U.mulVec v) 0 * (U.mulVec v) 1 +
          f * (U.mulVec v) 1 ^ 2 = a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2 := by
  obtain ⟨V,hV⟩ := exists_coordinates_equiv_of_principal_scaling a b c d e f k
    (ne_of_gt ha) (ne_of_gt hd) hD hk hac x y hx hy h
  let U := LinearMap.toMatrix' V.toLinearMap
  have hb : ∀ v, x * (coordinates d e f (ne_of_gt hd) (U.mulVec v)).val =
      y * coefficientOrderEquivOfShift a b c d e f k hk hac
        (coordinates a b c (ne_of_gt ha) v).val := by
    intro v
    simpa only [U, LinearMap.toMatrix'_mulVec] using hV v
  have hu : IsUnit U := by
    apply LinearMap.isUnit_toMatrix'_iff.mpr
    exact ⟨⟨V.toLinearMap, V.symm.toLinearMap,
      by apply LinearMap.ext; intro v; exact V.apply_symm_apply v,
      by apply LinearMap.ext; intro v; exact V.symm_apply_apply v⟩, rfl⟩
  have hdet := determinant_of_scaled_coordinates a b c d e f k
    (ne_of_gt ha) (ne_of_gt hd) hk hac x y U hb
  have hnx := norm_pos_of_discriminant_neg d e f hD x hx
  have hny := norm_pos_of_discriminant_neg d e f hD y hy
  have hud : IsUnit U.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact hu
  have hdU : U.det = 1 := by
    rcases Int.isUnit_iff.mp hud with hpos | hneg
    · exact hpos
    · rw [hneg] at hdet
      nlinarith [mul_pos hnx hd, mul_pos hny ha]
  refine ⟨U,hu,hdU,?_⟩
  intro v
  have hn := congrArg QuadraticAlgebra.norm (hb v)
  rw [map_mul, map_mul,
    norm_coordinates, norm_coefficientOrderEquivOfShift, norm_coordinates] at hn
  rw [hdU, mul_one] at hdet
  have hn' : (x.norm*d) *
      (d * (U.mulVec v) 0 ^ 2 + e * (U.mulVec v) 0 * (U.mulVec v) 1 + f * (U.mulVec v) 1 ^ 2) =
      (x.norm*d) * (a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2) := by
    calc
      _ = (y.norm*a) * (a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2) := by
        simpa only [mul_assoc] using hn
      _ = _ := by rw [hdet]
  exact mul_left_cancel₀ (ne_of_gt (mul_pos hnx hd)) hn'

/-- Proper polynomial equivalence is exactly nonzero principal scaling of
the norm ideals under the canonical oriented order identification. -/
theorem proper_polynomial_matrix_iff_principal_scaling (a b c d e f : ℤ)
    (ha : 0 < a) (hd : 0 < d) (hneg : e^2 - 4*d*f < 0)
    (hD : b^2 - 4*a*c = e^2 - 4*d*f) :
    (∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U ∧ U.det = 1 ∧
      ∀ v : Fin 2 → ℤ,
        d * (U.mulVec v) 0 ^ 2 + e * (U.mulVec v) 0 * (U.mulVec v) 1 +
          f * (U.mulVec v) 1 ^ 2 = a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2) ↔
    ∃ x y : CoefficientOrder d e f, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * normIdeal d e f =
        Ideal.span {y} * Ideal.map
          (coefficientOrderEquivOfDiscriminant a b c d e f hD).toRingHom (normIdeal a b c) := by
  constructor
  · rintro ⟨U,_,hdet,hp⟩
    refine ⟨(a : CoefficientOrder d e f), ⟨d*U 0 0, U 1 0⟩, ?_, ?_, ?_⟩
    · intro hz
      have hh := congrArg QuadraticAlgebra.re hz
      exact (ne_of_gt ha) (by simpa using hh)
    · intro hz
      have hn := norm_first_column_of_polynomial_matrix a b c d e f U hp
      rw [hz] at hn
      exact (ne_of_gt (mul_pos hd ha)) (by simpa using hn.symm)
    · exact principal_scaling_of_proper_polynomial_matrix_discriminant a b c d e f
        (ne_of_gt ha) (ne_of_gt hd) U hdet hp
  · rintro ⟨x,y,hx,hy,h⟩
    unfold coefficientOrderEquivOfDiscriminant at h
    exact exists_proper_polynomial_matrix_of_principal_scaling a b c d e f _
      ha hd hneg _ _ x y hx hy h

private lemma principal_scaling_map {R S : Type*} [CommRing R] [CommRing S]
    (F : R ≃+* S) (P Q : Ideal R) (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Ideal.span {x} * P = Ideal.span {y} * Q) :
    ∃ u v : S, u ≠ 0 ∧ v ≠ 0 ∧
      Ideal.span {u} * Ideal.map F.toRingHom P = Ideal.span {v} * Ideal.map F.toRingHom Q := by
  refine ⟨F x,F y,?_,?_,?_⟩
  · exact fun hzero => hx (F.injective (hzero.trans (map_zero F).symm))
  · exact fun hzero => hy (F.injective (hzero.trans (map_zero F).symm))
  · have hh := congrArg (Ideal.map F.toRingHom) h
    simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] using hh

private lemma principal_scaling_map_iff {R S : Type*} [CommRing R] [CommRing S]
    (E : R ≃+* S) (I J : Ideal R) :
    (∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * I = Ideal.span {y} * J) ↔
    ∃ x y : S, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * Ideal.map E.toRingHom I = Ideal.span {y} * Ideal.map E.toRingHom J := by
  constructor
  · rintro ⟨x,y,hx,hy,h⟩
    exact principal_scaling_map E I J x y hx hy h
  · rintro ⟨x,y,hx,hy,h⟩
    have hh := principal_scaling_map E.symm (Ideal.map E.toRingHom I) (Ideal.map E.toRingHom J) x y hx hy h
    simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv] using hh

/-- The same proper-polynomial criterion in one fixed discriminant order.
The two canonical embeddings are fixed by the coefficients and D. -/
theorem proper_polynomial_matrix_iff_commonOrder_principal_scaling
    (a b c d e f D : ℤ) (ha : 0 < a) (hd : 0 < d) (hneg : D < 0)
    (hres : D % 4 = 0 ∨ D % 4 = 1)
    (hK : b^2 - 4*a*c = D) (hL : e^2 - 4*d*f = D) :
    (∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U ∧ U.det = 1 ∧
      ∀ v : Fin 2 → ℤ,
        d * (U.mulVec v) 0 ^ 2 + e * (U.mulVec v) 0 * (U.mulVec v) 1 +
          f * (U.mulVec v) 1 ^ 2 = a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2) ↔
    ∃ x y : DiscriminantOrder D, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * Ideal.map
        (coefficientOrderEquivDiscriminantOrder d e f D hres hL).toRingHom (normIdeal d e f) =
      Ideal.span {y} * Ideal.map
        (coefficientOrderEquivDiscriminantOrder a b c D hres hK).toRingHom (normIdeal a b c) := by
  let E := coefficientOrderEquivOfDiscriminant a b c d e f (hK.trans hL.symm)
  let F := coefficientOrderEquivDiscriminantOrder d e f D hres hL
  let G := coefficientOrderEquivDiscriminantOrder a b c D hres hK
  have hFG : F.toRingHom.comp E.toRingHom = G.toRingHom := by
    have hh := coefficientOrderEquivOfDiscriminant_trans a b c d e f
      1 (D%2) (((D%2)^2-D)/4) (hK.trans hL.symm)
      (hL.trans (discriminantOrder_coefficients D hres).symm)
    apply RingHom.ext
    intro z
    exact congrArg (fun H : CoefficientOrder a b c ≃ₐ[ℤ] DiscriminantOrder D => H z) hh
  have hmap : Ideal.map F.toRingHom (Ideal.map E.toRingHom (normIdeal a b c)) =
      Ideal.map G.toRingHom (normIdeal a b c) := by rw [Ideal.map_map,hFG]
  have hh := (proper_polynomial_matrix_iff_principal_scaling a b c d e f ha hd
    (hL ▸ hneg) (hK.trans hL.symm)).trans
      (principal_scaling_map_iff F.toRingEquiv (normIdeal d e f)
        (Ideal.map E.toRingHom (normIdeal a b c)))
  rw [hmap] at hh
  exact hh

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- The original proper lattice relation is exactly equality of content and
discriminant together with principal scaling of the normalized norm ideals.
Equal discriminant alone does not assert genus membership or proper
equivalence. -/
theorem isProperGlobalIsometry_iff_binaryNormIdeal_principal_scaling
    (K L : PositiveDefiniteIntegralLattice 2) :
    K.IsProperGlobalIsometry L ↔
    ∃ _hg : K.binaryContent = L.binaryContent,
    ∃ hD : K.binaryPrimitiveDiscriminant = L.binaryPrimitiveDiscriminant,
    ∃ x y : L.binaryCoefficientOrder, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * L.binaryNormIdeal =
        Ideal.span {y} * Ideal.map
          (BinaryNormIdeal.coefficientOrderEquivOfDiscriminant
            (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
            (2*K.pairingMatrix 0 1 / (K.binaryContent : ℤ))
            (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))
            (L.pairingMatrix 0 0 / (L.binaryContent : ℤ))
            (2*L.pairingMatrix 0 1 / (L.binaryContent : ℤ))
            (L.pairingMatrix 1 1 / (L.binaryContent : ℤ)) hD).toRingHom K.binaryNormIdeal := by
  have heq (hD : K.binaryPrimitiveDiscriminant = L.binaryPrimitiveDiscriminant) :=
    BinaryNormIdeal.proper_polynomial_matrix_iff_principal_scaling
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
      (2*K.pairingMatrix 0 1 / (K.binaryContent : ℤ))
      (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))
      (L.pairingMatrix 0 0 / (L.binaryContent : ℤ))
      (2*L.pairingMatrix 0 1 / (L.binaryContent : ℤ))
      (L.pairingMatrix 1 1 / (L.binaryContent : ℤ))
      K.binaryPrimitivePolynomial_leading_pos L.binaryPrimitivePolynomial_leading_pos
      L.binaryPrimitiveDiscriminant_neg hD
  constructor
  · intro h
    have hgen := isSameGenus_of_isGlobalIsometry (isGlobalIsometry_of_isProperGlobalIsometry h)
    refine ⟨hgen.binaryContent_eq, hgen.binaryPrimitiveDiscriminant_eq, ?_⟩
    apply (heq hgen.binaryPrimitiveDiscriminant_eq).mp
    obtain ⟨U,hU,hdet,hform⟩ := h
    refine ⟨U,hU,hdet,?_⟩
    intro v
    have hh := (binaryPrimitivePolynomialIsometryEquivOfMatrix K L U hU hform).map_app v
    rw [binaryPrimitivePolynomialIsometryEquivOfMatrix_apply] at hh
    simpa only [binaryPrimitivePolynomial_apply] using hh
  · rintro ⟨hg,hD,x,y,hx,hy,h⟩
    obtain ⟨U,hU,hdet,hp⟩ := (heq hD).mpr ⟨x,y,hx,hy,h⟩
    refine ⟨U,hU,hdet,?_⟩
    have hh := (binaryPrimitivePolynomialOver_matrix_congruence_iff K L hg U).mpr (by
      intro v
      simpa only [binaryPrimitivePolynomialOver_apply, Int.cast_id] using hp v)
    simpa only [Int.cast_id, Matrix.map_id] using hh

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.norm_pos_of_discriminant_neg
#assert_standard_axioms BinaryNormIdeal.exists_coordinates_equiv_of_principal_scaling

#assert_standard_axioms BinaryNormIdeal.determinant_of_scaled_coordinates
#assert_standard_axioms BinaryNormIdeal.exists_proper_polynomial_matrix_of_principal_scaling

#assert_standard_axioms BinaryNormIdeal.proper_polynomial_matrix_iff_principal_scaling
#assert_standard_axioms PositiveDefiniteIntegralLattice.isProperGlobalIsometry_iff_binaryNormIdeal_principal_scaling

#assert_standard_axioms BinaryNormIdeal.proper_polynomial_matrix_iff_commonOrder_principal_scaling
