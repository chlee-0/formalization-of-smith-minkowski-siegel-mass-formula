import SMSFormula.BinaryDiscriminantOrder

/-!
# Local norm models of primitive binary polynomials

A unit represented by ax²+bxy+cy² gives an explicit oriented norm model
in the actual scalar-extended coefficient order. The formulas work over
any commutative ring and do not divide by 2.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- Scalar-ring presentation of the coefficient order, including at p=2. -/
abbrev CoefficientAlgebra (a b c : R) := QuadraticAlgebra R (-a*c) b

/-- The original polynomial on the unchanged binary scalar carrier. -/
def polynomialOver (a b c : R) (x : Fin 2 → R) : R :=
  a*x 0^2+b*x 0*x 1+c*x 1^2

/-- Ordinary coefficient coordinates on the order, with their orientation. -/
def algebraCoordinates (a b c : R) : (Fin 2 → R) ≃ₗ[R] CoefficientAlgebra a b c where
  toFun x := ⟨x 0,x 1⟩
  invFun z := ![z.re,z.im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by apply QuadraticAlgebra.ext <;> rfl
  map_add' x y := by apply QuadraticAlgebra.ext <;> rfl
  map_smul' r x := by apply QuadraticAlgebra.ext <;> rfl

/-- A represented unit gives a norm model by exact coordinate formulas.
Its inverse sends z to (v0*z.re-c*v1*z.im,v1*z.re+(a*v0+b*v1)*z.im). -/
def unitValueNormEquiv (a b c : R) (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver a b c v = (u : R)) :
    (Fin 2 → R) ≃ₗ[R] CoefficientAlgebra a b c where
  toFun x := ⟨(↑(u⁻¹) : R)*((a*v 0+b*v 1)*x 0+c*v 1*x 1),
    (↑(u⁻¹) : R)*(v 0*x 1-v 1*x 0)⟩
  invFun z := ![v 0*z.re-c*v 1*z.im,v 1*z.re+(a*v 0+b*v 1)*z.im]
  left_inv x := by
    have hi : (↑(u⁻¹) : R)*(u : R)=1 := by simp
    change a*v 0^2+b*v 0*v 1+c*v 1^2=(u : R) at hv
    ext i
    fin_cases i
    · change v 0*((↑(u⁻¹) : R)*((a*v 0+b*v 1)*x 0+c*v 1*x 1)) -
        c*v 1*((↑(u⁻¹) : R)*(v 0*x 1-v 1*x 0))=x 0
      linear_combination ((↑(u⁻¹) : R)*x 0)*hv + x 0*hi
    · change v 1*((↑(u⁻¹) : R)*((a*v 0+b*v 1)*x 0+c*v 1*x 1)) +
        (a*v 0+b*v 1)*((↑(u⁻¹) : R)*(v 0*x 1-v 1*x 0))=x 1
      linear_combination ((↑(u⁻¹) : R)*x 1)*hv + x 1*hi
  right_inv z := by
    have hi : (↑(u⁻¹) : R)*(u : R)=1 := by simp
    change a*v 0^2+b*v 0*v 1+c*v 1^2=(u : R) at hv
    apply QuadraticAlgebra.ext <;>
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    · linear_combination ((↑(u⁻¹) : R)*z.re)*hv + z.re*hi
    · linear_combination ((↑(u⁻¹) : R)*z.im)*hv + z.im*hi
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp <;> ring
  map_smul' r x := by apply QuadraticAlgebra.ext <;> simp <;> ring

/-- The inverse map keeps the exact represented-unit norm scale. -/
lemma polynomial_unitValueNormEquiv_symm (a b c : R) (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver a b c v = (u : R)) (z : CoefficientAlgebra a b c) :
    polynomialOver a b c ((unitValueNormEquiv a b c v u hv).symm z) = (u : R)*z.norm := by
  change a*v 0^2+b*v 0*v 1+c*v 1^2=(u : R) at hv
  simp only [polynomialOver,unitValueNormEquiv,LinearEquiv.coe_symm_mk,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,QuadraticAlgebra.norm_def]
  linear_combination (z.re^2+b*z.re*z.im+a*c*z.im^2)*hv

/-- The actual polynomial equals the represented unit times the order norm. -/
lemma polynomial_eq_unit_mul_norm (a b c : R) (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver a b c v = (u : R)) (x : Fin 2 → R) :
    polynomialOver a b c x = (u : R)*(unitValueNormEquiv a b c v u hv x).norm := by
  simpa using polynomial_unitValueNormEquiv_symm a b c v u hv
    (unitValueNormEquiv a b c v u hv x)

/-- The inverse norm model has determinant exactly the represented unit. -/
lemma det_unitValueNormEquiv_symm (a b c : R) (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver a b c v = (u : R)) :
    (LinearMap.toMatrix' ((algebraCoordinates a b c).trans
      (unitValueNormEquiv a b c v u hv).symm).toLinearMap).det = (u : R) := by
  have hm : LinearMap.toMatrix' ((algebraCoordinates a b c).trans
      (unitValueNormEquiv a b c v u hv).symm).toLinearMap =
      !![v 0,-c*v 1;v 1,a*v 0+b*v 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply,algebraCoordinates,unitValueNormEquiv]
  rw [hm,Matrix.det_fin_two]
  change v 0*(a*v 0+b*v 1)-(-c*v 1)*v 1=(u : R)
  change a*v 0^2+b*v 0*v 1+c*v 1^2=(u : R) at hv
  linear_combination hv

/-- The unit values of the original polynomial are exactly a single coset
of norms of units in the actual coefficient algebra. -/
theorem exists_polynomial_eq_unit_iff (a b c : R) (v : Fin 2 → R) (u s : Rˣ)
    (hv : polynomialOver a b c v = (u : R)) :
    (∃ x, polynomialOver a b c x = (s : R)) ↔
      ∃ z : (CoefficientAlgebra a b c)ˣ, (s : R)=(u : R)*(z.val.norm) := by
  constructor
  · rintro ⟨x,hx⟩
    let w := unitValueNormEquiv a b c v u hv x
    have heq : (s : R)=(u : R)*w.norm := hx.symm.trans (polynomial_eq_unit_mul_norm a b c v u hv x)
    have hn : IsUnit w.norm := by
      have heq' : w.norm=(↑(u⁻¹) : R)*(s : R) := by rw [heq]; simp
      rw [heq']
      exact (u⁻¹).isUnit.mul s.isUnit
    obtain ⟨z,hz⟩ := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr hn
    exact ⟨z,by simpa only [hz] using heq⟩
  · rintro ⟨z,hz⟩
    exact ⟨(unitValueNormEquiv a b c v u hv).symm z.val,
      (polynomial_unitValueNormEquiv_symm a b c v u hv z.val).trans hz.symm⟩

/-- The actual two-generator ideal coordinates over the scalar ring. -/
def normVector (a b c : R) (x : Fin 2 → R) : CoefficientAlgebra a b c := ⟨a*x 0,x 1⟩

lemma norm_normVector (a b c : R) (x : Fin 2 → R) :
    (normVector a b c x).norm=a*polynomialOver a b c x := by
  simp only [normVector,QuadraticAlgebra.norm_def,polynomialOver]
  ring

/-- The inverse norm model is literally multiplication by the chosen ideal
element. No cancellation of the leading coefficient is used. -/
lemma normVector_unitValueNormEquiv_symm (a b c : R) (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver a b c v=(u : R)) (z : CoefficientAlgebra a b c) :
    normVector a b c ((unitValueNormEquiv a b c v u hv).symm z)=normVector a b c v*z := by
  apply QuadraticAlgebra.ext <;>
    simp [normVector,unitValueNormEquiv,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

/-- A unit value gives an explicit principal generator for the actual
extended ideal (a,theta), including when a itself is not a unit. -/
theorem span_eq_principal_of_unit_value (a b c : R) (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver a b c v=(u : R)) :
    Ideal.span {(algebraMap R (CoefficientAlgebra a b c) a),QuadraticAlgebra.omega}=
      Ideal.span {normVector a b c v} := by
  have h (x : Fin 2 → R) : normVector a b c x ∈ Ideal.span {normVector a b c v} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨unitValueNormEquiv a b c v u hv x,?_⟩
    simpa using normVector_unitValueNormEquiv_symm a b c v u hv (unitValueNormEquiv a b c v u hv x)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · simpa [normVector] using h ![1,0]
    · obtain rfl := Set.mem_singleton_iff.mp hz
      simpa [normVector] using h ![0,1]
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have hid : normVector a b c v=
        (algebraMap R (CoefficientAlgebra a b c) (v 0))*algebraMap R _ a+
          (algebraMap R (CoefficientAlgebra a b c) (v 1))*QuadraticAlgebra.omega := by
      apply QuadraticAlgebra.ext
      · simp [normVector,mul_comm]
      · simp [normVector]
    rw [hid]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- A generator translation over the actual scalar ring. -/
def coefficientAlgebraEquivOfShift (a b c a' b' c' k : R)
    (hb : b=b'+2*k) (hac : a*c=a'*c'+b'*k+k^2) :
    CoefficientAlgebra a b c ≃ₐ[R] CoefficientAlgebra a' b' c' where
  toFun z := ⟨z.re+k*z.im,z.im⟩
  invFun z := ⟨z.re-k*z.im,z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> simp
  right_inv z := by apply QuadraticAlgebra.ext <;> simp
  map_add' z w := by
    apply QuadraticAlgebra.ext
    · simp; ring
    · simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext
    · change (z*w).re+k*(z*w).im=_
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
      linear_combination (k*z.im*w.im)*hb-(z.im*w.im)*hac
    · change (z*w).im=_
      simp only [QuadraticAlgebra.im_mul]
      linear_combination (z.im*w.im)*hb
  commutes' r := by apply QuadraticAlgebra.ext <;> simp

lemma norm_coefficientAlgebraEquivOfShift (a b c a' b' c' k : R)
    (hb : b=b'+2*k) (hac : a*c=a'*c'+b'*k+k^2) (z : CoefficientAlgebra a b c) :
    (coefficientAlgebraEquivOfShift a b c a' b' c' k hb hac z).norm=z.norm := by
  change (z.re+k*z.im)*(z.re+k*z.im)+b'*(z.re+k*z.im)*z.im-
    (-a'*c')*z.im*z.im=_
  rw [QuadraticAlgebra.norm_def]
  linear_combination -(z.re*z.im)*hb-(z.im^2)*hac

private lemma int_discriminant_shift (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') :
    b=b'+2*((b-b')/2) ∧ a*c=a'*c'+b'*((b-b')/2)+((b-b')/2)^2 := by
  have h := congrArg (Int.castRingHom (ZMod 2)) hD
  have hh : (b : ZMod 2)^2=(b' : ZMod 2)^2 := by
    have hn : (4 : ZMod 2)=0 := by decide
    simpa only [map_sub,map_pow,map_mul,map_ofNat,map_intCast,hn,zero_mul,sub_zero] using h
  have hs (x : ZMod 2) : x^2=x := by fin_cases x <;> decide
  rw [hs,hs] at hh
  have hdiv := (ZMod.intCast_eq_intCast_iff_dvd_sub b' b 2).mp hh.symm
  have hm := Int.mul_ediv_cancel' hdiv
  have hb : b=b'+2*((b-b')/2) := by omega
  refine ⟨hb,?_⟩
  rw [hb] at hD
  nlinarith

/-- Equal integer discriminants identify the actual scalar-extended orders.
The half-trace difference is taken exactly in Z, before scalar extension. -/
def coefficientAlgebraEquivOfDiscriminant (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') :
    CoefficientAlgebra (a : R) (b : R) (c : R) ≃ₐ[R]
      CoefficientAlgebra (a' : R) (b' : R) (c' : R) :=
  coefficientAlgebraEquivOfShift _ _ _ _ _ _ (((b-b')/2 : ℤ) : R)
    (by simpa only [map_add,map_mul,map_ofNat,map_intCast] using
      congrArg (Int.castRingHom R) (int_discriminant_shift a b c a' b' c' hD).1)
    (by simpa only [map_add,map_mul,map_pow,map_intCast] using
      congrArg (Int.castRingHom R) (int_discriminant_shift a b c a' b' c' hD).2)

lemma norm_coefficientAlgebraEquivOfDiscriminant (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') (z : CoefficientAlgebra (a : R) (b : R) (c : R)) :
    (coefficientAlgebraEquivOfDiscriminant a b c a' b' c' hD z).norm=z.norm := by
  unfold coefficientAlgebraEquivOfDiscriminant
  apply norm_coefficientAlgebraEquivOfShift

/-- The unit-value norm model transported to another integer coefficient
presentation of the same order. -/
def unitValueNormEquivOfDiscriminant (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver (a : R) (b : R) (c : R) v=(u : R)) :
    (Fin 2 → R) ≃ₗ[R] CoefficientAlgebra (a' : R) (b' : R) (c' : R) :=
  (unitValueNormEquiv _ _ _ v u hv).trans
    (coefficientAlgebraEquivOfDiscriminant (R := R) a b c a' b' c' hD).toLinearEquiv

lemma polynomial_eq_unit_mul_norm_of_discriminant (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver (a : R) (b : R) (c : R) v=(u : R)) (x : Fin 2 → R) :
    polynomialOver (a : R) (b : R) (c : R) x =
      (u : R)*(unitValueNormEquivOfDiscriminant a b c a' b' c' hD v u hv x).norm := by
  change polynomialOver (a : R) (b : R) (c : R) x = (u : R)*
    (coefficientAlgebraEquivOfDiscriminant a b c a' b' c' hD
      (unitValueNormEquiv _ _ _ v u hv x)).norm
  rw [norm_coefficientAlgebraEquivOfDiscriminant]
  exact polynomial_eq_unit_mul_norm _ _ _ v u hv x

/-- The transported norm model retains its exact oriented determinant. -/
lemma det_unitValueNormEquivOfDiscriminant_symm (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver (a : R) (b : R) (c : R) v=(u : R)) :
    (LinearMap.toMatrix' ((algebraCoordinates (a' : R) (b' : R) (c' : R)).trans
      (unitValueNormEquivOfDiscriminant a b c a' b' c' hD v u hv).symm).toLinearMap).det=(u : R) := by
  let k : R := (((b-b')/2 : ℤ) : R)
  have hm : LinearMap.toMatrix' ((algebraCoordinates (a' : R) (b' : R) (c' : R)).trans
      (unitValueNormEquivOfDiscriminant a b c a' b' c' hD v u hv).symm).toLinearMap =
      !![v 0,-k*v 0-(c : R)*v 1;v 1,(a : R)*v 0+(b : R)*v 1-k*v 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply,algebraCoordinates,unitValueNormEquivOfDiscriminant,
        coefficientAlgebraEquivOfDiscriminant,coefficientAlgebraEquivOfShift,
        unitValueNormEquiv,k] <;> ring
  rw [hm,Matrix.det_fin_two]
  change v 0*((a : R)*v 0+(b : R)*v 1-k*v 1)-(-k*v 0-(c : R)*v 1)*v 1=(u : R)
  change (a : R)*v 0^2+(b : R)*v 0*v 1+(c : R)*v 1^2=(u : R) at hv
  linear_combination hv

/-- The scalar-extended order fixed by the original primitive discriminant. -/
abbrev DiscriminantAlgebra (R : Type*) [CommRing R] (D : ℤ) :=
  CoefficientAlgebra ((1 : ℤ) : R) ((D%2 : ℤ) : R) ((((D%2)^2-D)/4 : ℤ) : R)

private lemma det_matrix_symm_mul (e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) :
    (LinearMap.toMatrix' e.symm.toLinearMap).det *
      (LinearMap.toMatrix' e.toLinearMap).det=1 := by
  rw [← Matrix.det_mul,← LinearMap.toMatrix'_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by ext x i; simp
  rw [h]
  simp

private lemma norm_models_proper_matrix_iff (a b c : R)
    (q q' : (Fin 2 → R) → R) (e f : (Fin 2 → R) ≃ₗ[R] CoefficientAlgebra a b c)
    (u t : Rˣ) (he : ∀ x, q x=(u : R)*(e x).norm) (hf : ∀ x, q' x=(t : R)*(f x).norm)
    (hde : (LinearMap.toMatrix' ((algebraCoordinates a b c).trans e.symm).toLinearMap).det=(u : R))
    (hdf : (LinearMap.toMatrix' ((algebraCoordinates a b c).trans f.symm).toLinearMap).det=(t : R))
    (v : Fin 2 → R) (hv : q v=(u : R)) :
    (∃ U : Matrix (Fin 2) (Fin 2) R, IsUnit U ∧ U.det=1 ∧ ∀ x, q' (U.mulVec x)=q x) ↔
      ∃ z : (CoefficientAlgebra a b c)ˣ, (u : R)=(t : R)*z.val.norm := by
  constructor
  · rintro ⟨U,_,_,hp⟩
    have hnorm : (f (U.mulVec v)).norm=(↑(t⁻¹) : R)*(u : R) := by
      have hh := (hf (U.mulVec v)).symm.trans ((hp v).trans hv)
      rw [← hh]
      simp
    have hu : IsUnit (f (U.mulVec v)) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      (hnorm ▸ (t⁻¹).isUnit.mul u.isUnit)
    obtain ⟨z,hz⟩ := hu
    exact ⟨z,by rw [hz,← hf,hp,hv]⟩
  · rintro ⟨z,hz⟩
    let C := algebraCoordinates a b c
    let A := e.trans C.symm
    let B := (C.trans (z.mulLeftLinearEquiv R (CoefficientAlgebra a b c))).trans C.symm
    let D := C.trans f.symm
    let g := (A.trans B).trans D
    let U := LinearMap.toMatrix' g.toLinearMap
    have hA : (LinearMap.toMatrix' A.toLinearMap).det=(↑(u⁻¹) : R) := by
      have hh := det_matrix_symm_mul A
      have hs : A.symm=C.trans e.symm := rfl
      rw [hs,hde] at hh
      have hi : (↑(u⁻¹) : R)*(u : R)=1 := by simp
      linear_combination (↑(u⁻¹) : R)*hh - (LinearMap.toMatrix' A.toLinearMap).det*hi
    have hB : (LinearMap.toMatrix' B.toLinearMap).det=z.val.norm := by
      have hm : LinearMap.toMatrix' B.toLinearMap=
          !![z.val.re,-a*c*z.val.im;z.val.im,z.val.re+b*z.val.im] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [B,C,algebraCoordinates,LinearMap.toMatrix'_apply,
            QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
      rw [hm,Matrix.det_fin_two,QuadraticAlgebra.norm_def]
      change z.val.re*(z.val.re+b*z.val.im)-(-a*c*z.val.im)*z.val.im=_
      ring
    have hg : U.det=1 := by
      have hgmap : g.toLinearMap=D.toLinearMap.comp (B.toLinearMap.comp A.toLinearMap) := rfl
      dsimp only [U]
      rw [hgmap,LinearMap.toMatrix'_comp,LinearMap.toMatrix'_comp,Matrix.det_mul,Matrix.det_mul,
        hA,hB,hdf]
      rw [← mul_assoc,← hz]
      simp
    refine ⟨U,?_,hg,?_⟩
    · refine ⟨⟨U,LinearMap.toMatrix' g.symm.toLinearMap,?_,?_⟩,rfl⟩
      · rw [← LinearMap.toMatrix'_comp]
        have hh : g.toLinearMap.comp g.symm.toLinearMap=LinearMap.id := by ext x i; simp
        rw [hh]; simp
      · rw [← LinearMap.toMatrix'_comp]
        have hh : g.symm.toLinearMap.comp g.toLinearMap=LinearMap.id := by ext x i; simp
        rw [hh]; simp
    · intro x
      have hUx : U.mulVec x=f.symm (z.val*(e x)) := by
        change (LinearMap.toMatrix' g.toLinearMap).mulVec x=_
        rw [LinearMap.toMatrix'_mulVec]
        simp [g,A,B,D,C]
      rw [hUx,hf,f.apply_symm_apply,map_mul,he,hz]
      ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- The actual polynomial unit-value norm model in the common discriminant
order over the chosen scalar ring. -/
def binaryLocalNormEquiv (K : PositiveDefiniteIntegralLattice 2) (v : Fin 2 → R) (u : Rˣ)
    (hv : K.binaryPrimitivePolynomialOver R v=(u : R)) :
    (Fin 2 → R) ≃ₗ[R] DiscriminantAlgebra R K.binaryPrimitiveDiscriminant :=
  unitValueNormEquivOfDiscriminant
    (K.pairingMatrix 0 0/(K.binaryContent : ℤ))
    (2*K.pairingMatrix 0 1/(K.binaryContent : ℤ))
    (K.pairingMatrix 1 1/(K.binaryContent : ℤ))
    1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    (discriminantOrder_coefficients K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four).symm v u
    (by simpa [polynomialOver,binaryPrimitivePolynomialOver_apply] using hv)

/-- Exact norm scale in the actual common order, without an inverse of 2. -/
lemma binaryPrimitivePolynomialOver_eq_unit_mul_localNorm
    (K : PositiveDefiniteIntegralLattice 2) (v : Fin 2 → R) (u : Rˣ)
    (hv : K.binaryPrimitivePolynomialOver R v=(u : R)) (x : Fin 2 → R) :
    K.binaryPrimitivePolynomialOver R x=(u : R)*(K.binaryLocalNormEquiv v u hv x).norm := by
  unfold binaryLocalNormEquiv
  simpa only [binaryPrimitivePolynomialOver_apply,polynomialOver] using
    polynomial_eq_unit_mul_norm_of_discriminant
      (K.pairingMatrix 0 0/(K.binaryContent : ℤ)) (2*K.pairingMatrix 0 1/(K.binaryContent : ℤ))
      (K.pairingMatrix 1 1/(K.binaryContent : ℤ)) 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
      (discriminantOrder_coefficients K.binaryPrimitiveDiscriminant
        K.binaryPrimitiveDiscriminant_mod_four).symm v u _ x


/-- The original determinant-one orientation is retained by the norm model. -/
lemma det_binaryLocalNormEquiv_symm (K : PositiveDefiniteIntegralLattice 2) (v : Fin 2 → R) (u : Rˣ)
    (hv : K.binaryPrimitivePolynomialOver R v=(u : R)) :
    (LinearMap.toMatrix' ((algebraCoordinates ((1 : ℤ) : R)
      ((K.binaryPrimitiveDiscriminant%2 : ℤ) : R)
      ((((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4 : ℤ) : R)).trans
      (K.binaryLocalNormEquiv v u hv).symm).toLinearMap).det=(u : R) := by
  exact det_unitValueNormEquivOfDiscriminant_symm _ _ _ _ _ _ _ v u _

/-- All represented units form one coset modulo norms of units of the actual
common order. This proves independence of the chosen represented unit. -/
theorem binaryPrimitivePolynomialOver_unit_values_iff
    (K : PositiveDefiniteIntegralLattice 2) (v : Fin 2 → R) (u s : Rˣ)
    (hv : K.binaryPrimitivePolynomialOver R v=(u : R)) :
    (∃ x, K.binaryPrimitivePolynomialOver R x=(s : R)) ↔
      ∃ z : (DiscriminantAlgebra R K.binaryPrimitiveDiscriminant)ˣ,
        (s : R)=(u : R)*z.val.norm := by
  let e := K.binaryLocalNormEquiv v u hv
  have he (x) : K.binaryPrimitivePolynomialOver R x=(u : R)*(e x).norm :=
    K.binaryPrimitivePolynomialOver_eq_unit_mul_localNorm v u hv x
  constructor
  · rintro ⟨x,hx⟩
    have hnorm : (e x).norm=(↑(u⁻¹) : R)*(s : R) := by rw [← hx,he]; simp
    have hu : IsUnit (e x) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      (hnorm ▸ (u⁻¹).isUnit.mul s.isUnit)
    obtain ⟨z,hz⟩ := hu
    refine ⟨z,?_⟩
    rw [hz,← he,hx]
  · rintro ⟨z,hz⟩
    refine ⟨e.symm z.val,?_⟩
    rw [he,e.apply_symm_apply,hz]

/-- Every actual primitive p-adic polynomial has such a common-order norm
model, including the dyadic prime and every nonmaximal discriminant. -/
theorem exists_binaryLocalNormModel_padic (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ),
      K.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p]) ∧
      ∃ e : (Fin 2 → ℤ_[p]) ≃ₗ[ℤ_[p]] DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant,
        ∀ x, K.binaryPrimitivePolynomialOver ℤ_[p] x=(u : ℤ_[p])*(e x).norm := by
  obtain ⟨v,u,hu⟩ := K.binaryPrimitivePolynomialOver_padic_exists_unit p
  exact ⟨v,u,hu.symm,K.binaryLocalNormEquiv v u hu.symm,
    K.binaryPrimitivePolynomialOver_eq_unit_mul_localNorm v u hu.symm⟩


/-- Proper local polynomial isometry is exactly the relative norm-unit
condition in the common actual order. The chosen represented units are
arbitrary, and the statement works over any commutative scalar ring. -/
theorem binaryPrimitivePolynomialOver_proper_matrix_iff_norm_unit
    (K L : PositiveDefiniteIntegralLattice 2) (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (v w : Fin 2 → R) (u t : Rˣ)
    (hv : K.binaryPrimitivePolynomialOver R v=(u : R))
    (hw : L.binaryPrimitivePolynomialOver R w=(t : R)) :
    (∃ U : Matrix (Fin 2) (Fin 2) R, IsUnit U ∧ U.det=1 ∧
      ∀ x, L.binaryPrimitivePolynomialOver R (U.mulVec x)=K.binaryPrimitivePolynomialOver R x) ↔
      ∃ z : (DiscriminantAlgebra R K.binaryPrimitiveDiscriminant)ˣ,
        (u : R)=(t : R)*z.val.norm := by
  let D := K.binaryPrimitiveDiscriminant
  let a := L.pairingMatrix 0 0/(L.binaryContent : ℤ)
  let b := 2*L.pairingMatrix 0 1/(L.binaryContent : ℤ)
  let c := L.pairingMatrix 1 1/(L.binaryContent : ℤ)
  have hDL : b^2-4*a*c=(D%2)^2-4*1*(((D%2)^2-D)/4) :=
    hD.trans (discriminantOrder_coefficients D K.binaryPrimitiveDiscriminant_mod_four).symm
  have hw' : polynomialOver (a : R) (b : R) (c : R) w=(t : R) := by
    simpa only [polynomialOver,binaryPrimitivePolynomialOver_apply] using hw
  let f := unitValueNormEquivOfDiscriminant a b c 1 (D%2) (((D%2)^2-D)/4) hDL w t hw'
  have hf (x) : L.binaryPrimitivePolynomialOver R x=(t : R)*(f x).norm := by
    simpa only [binaryPrimitivePolynomialOver_apply,polynomialOver] using
      polynomial_eq_unit_mul_norm_of_discriminant a b c 1 (D%2) (((D%2)^2-D)/4) hDL w t hw' x
  exact norm_models_proper_matrix_iff _ _ _ _ _ (K.binaryLocalNormEquiv v u hv) f u t
    (K.binaryPrimitivePolynomialOver_eq_unit_mul_localNorm v u hv) hf
    (K.det_binaryLocalNormEquiv_symm v u hv)
    (det_unitValueNormEquivOfDiscriminant_symm a b c 1 (D%2) (((D%2)^2-D)/4) hDL w t hw') v hv


/-- The same criterion with the original polynomial isometry carrier and
its determinant-one field. -/
theorem binaryPrimitivePolynomialOver_proper_isometry_iff_norm_unit
    (K L : PositiveDefiniteIntegralLattice 2) (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (v w : Fin 2 → R) (u t : Rˣ)
    (hv : K.binaryPrimitivePolynomialOver R v=(u : R))
    (hw : L.binaryPrimitivePolynomialOver R w=(t : R)) :
    (∃ e : (K.binaryPrimitivePolynomialOver R).IsometryEquiv (L.binaryPrimitivePolynomialOver R),
      (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det=1) ↔
      ∃ z : (DiscriminantAlgebra R K.binaryPrimitiveDiscriminant)ˣ,
        (u : R)=(t : R)*z.val.norm := by
  rw [← binaryPrimitivePolynomialOver_proper_matrix_iff_norm_unit K L hD v w u t hv hw]
  constructor
  · rintro ⟨e,hd⟩
    refine ⟨LinearMap.toMatrix' e.toLinearEquiv.toLinearMap,?_,hd,?_⟩
    · rw [Matrix.isUnit_iff_isUnit_det,hd]; exact isUnit_one
    · intro x
      rw [LinearMap.toMatrix'_mulVec]
      exact e.map_app x
  · rintro ⟨U,hU,hd,hp⟩
    let e : (K.binaryPrimitivePolynomialOver R).IsometryEquiv (L.binaryPrimitivePolynomialOver R) :=
      { toLinearEquiv := Matrix.toLinearEquiv' U hU.invertible
        map_app' := fun x => by simpa [Matrix.toLinearEquiv'_apply,Matrix.toLin'_apply] using hp x }
    refine ⟨e,?_⟩
    change (LinearMap.toMatrix' (Matrix.toLin' U)).det=1
    rw [LinearMap.toMatrix'_toLin',hd]

/-- Relative unit-value norm condition in the actual common discriminant
order. This is a local norm predicate, not a definition of genus. -/
def binaryLocalUnitNormCondition (K L : PositiveDefiniteIntegralLattice 2) (R : Type*) [CommRing R] : Prop :=
  ∃ (v w : Fin 2 → R) (u t : Rˣ),
    K.binaryPrimitivePolynomialOver R v=(u : R) ∧
    L.binaryPrimitivePolynomialOver R w=(t : R) ∧
    ∃ z : (DiscriminantAlgebra R K.binaryPrimitiveDiscriminant)ˣ,
      (u : R)=(t : R)*z.val.norm

/-- At every finite prime the actual proper-local isometry carrier is
classified by the unit norm group of the actual order, including p=2. -/
theorem binaryPrimitivePolynomialOver_padic_proper_iff_localUnitNormCondition
    (K L : PositiveDefiniteIntegralLattice 2) (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (∃ e : (K.binaryPrimitivePolynomialOver ℤ_[p]).IsometryEquiv
      (L.binaryPrimitivePolynomialOver ℤ_[p]),
      (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det=1) ↔
      K.binaryLocalUnitNormCondition L ℤ_[p] := by
  constructor
  · intro he
    obtain ⟨v,u,hu⟩ := K.binaryPrimitivePolynomialOver_padic_exists_unit p
    obtain ⟨w,t,ht⟩ := L.binaryPrimitivePolynomialOver_padic_exists_unit p
    exact ⟨v,w,u,t,hu.symm,ht.symm,
      (binaryPrimitivePolynomialOver_proper_isometry_iff_norm_unit K L hD v w u t hu.symm ht.symm).mp he⟩
  · rintro ⟨v,w,u,t,hu,ht,hz⟩
    exact (binaryPrimitivePolynomialOver_proper_isometry_iff_norm_unit K L hD v w u t hu ht).mpr hz

/-- The original genus is classified by equal actual content/discriminant,
actual finite-place order-unit norms, and the original real isometry clause.
No maximal-order norm group or new genus definition is substituted. -/
theorem isSameGenus_iff_binaryLocalUnitNormCondition (K L : PositiveDefiniteIntegralLattice 2) :
    K.IsSameGenus L ↔ K.binaryContent=L.binaryContent ∧
      L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant ∧
      (∀ (p : ℕ) [Fact (Nat.Prime p)], K.binaryLocalUnitNormCondition L ℤ_[p]) ∧
      Nonempty ((K.binaryPrimitivePolynomialOver ℝ).IsometryEquiv
        (L.binaryPrimitivePolynomialOver ℝ)) := by
  constructor
  · intro h
    have hD := h.binaryPrimitiveDiscriminant_eq.symm
    obtain ⟨hg,hfinite,hinfty⟩ :=
      (isSameGenus_iff_binaryPrimitivePolynomialOver_proper_local_isometries K L).mp h
    refine ⟨hg,hD,?_,hinfty⟩
    intro p hp
    exact (binaryPrimitivePolynomialOver_padic_proper_iff_localUnitNormCondition K L hD p).mp (hfinite p)
  · rintro ⟨hg,hD,hfinite,hinfty⟩
    apply (isSameGenus_iff_binaryPrimitivePolynomialOver_proper_local_isometries K L).mpr
    refine ⟨hg,?_,hinfty⟩
    intro p hp
    exact (binaryPrimitivePolynomialOver_padic_proper_iff_localUnitNormCondition K L hD p).mpr (hfinite p)

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.CoefficientAlgebra
#assert_standard_axioms BinaryNormIdeal.polynomialOver
#assert_standard_axioms BinaryNormIdeal.algebraCoordinates
#assert_standard_axioms BinaryNormIdeal.unitValueNormEquiv
#assert_standard_axioms BinaryNormIdeal.polynomial_unitValueNormEquiv_symm
#assert_standard_axioms BinaryNormIdeal.polynomial_eq_unit_mul_norm
#assert_standard_axioms BinaryNormIdeal.det_unitValueNormEquiv_symm
#assert_standard_axioms BinaryNormIdeal.exists_polynomial_eq_unit_iff
#assert_standard_axioms BinaryNormIdeal.normVector
#assert_standard_axioms BinaryNormIdeal.norm_normVector
#assert_standard_axioms BinaryNormIdeal.normVector_unitValueNormEquiv_symm
#assert_standard_axioms BinaryNormIdeal.span_eq_principal_of_unit_value
#assert_standard_axioms BinaryNormIdeal.coefficientAlgebraEquivOfShift
#assert_standard_axioms BinaryNormIdeal.norm_coefficientAlgebraEquivOfShift
#assert_standard_axioms BinaryNormIdeal.coefficientAlgebraEquivOfDiscriminant
#assert_standard_axioms BinaryNormIdeal.norm_coefficientAlgebraEquivOfDiscriminant
#assert_standard_axioms BinaryNormIdeal.unitValueNormEquivOfDiscriminant
#assert_standard_axioms BinaryNormIdeal.polynomial_eq_unit_mul_norm_of_discriminant
#assert_standard_axioms BinaryNormIdeal.det_unitValueNormEquivOfDiscriminant_symm
#assert_standard_axioms BinaryNormIdeal.DiscriminantAlgebra
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormEquiv
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_eq_unit_mul_localNorm
#assert_standard_axioms PositiveDefiniteIntegralLattice.det_binaryLocalNormEquiv_symm
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_unit_values_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryLocalNormModel_padic
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_proper_matrix_iff_norm_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_proper_isometry_iff_norm_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalUnitNormCondition
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_padic_proper_iff_localUnitNormCondition
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_iff_binaryLocalUnitNormCondition
