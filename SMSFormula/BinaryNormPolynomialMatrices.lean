import SMSFormula.BinaryTraceNormFiber

/-!
# Raw polynomial matrices and original binary norm counts

The carrier contains every matrix preserving the quadratic polynomial.
An exact column bijection separates the norm-one first column from the
literal generator trace/norm fiber, in every commutative scalar ring.
-/

noncomputable section

namespace BinaryNormIdeal

variable {R : Type*} [CommRing R]

/-- The raw matrix carrier, with no invertibility or determinant filter. -/
def RawPolynomialIsometries (q : (Fin 2 → R) → R) :=
  {U : Matrix (Fin 2) (Fin 2) R // ∀ x, q (U.mulVec x)=q x}

/-- The two original coefficient columns, in their unchanged order. -/
def normMatrixColumnsEquiv (T N : R) : Matrix (Fin 2) (Fin 2) R ≃
    CoefficientAlgebra 1 T N × CoefficientAlgebra 1 T N where
  toFun U := (⟨U 0 0,U 1 0⟩,⟨U 0 1,U 1 1⟩)
  invFun v := !![v.1.re,v.2.re;v.1.im,v.2.im]
  left_inv U := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  right_inv v := by apply Prod.ext <;> apply QuadraticAlgebra.ext <;> rfl

/-- The exact mixed coefficient is the literal algebra trace. -/
theorem normPolynomial_mulVec_columns (T N : R) (U : Matrix (Fin 2) (Fin 2) R)
    (x : Fin 2 → R) :
    polynomialOver 1 T N (U.mulVec x)=
      (normMatrixColumnsEquiv T N U).1.norm*x 0^2+
      Algebra.trace R (CoefficientAlgebra 1 T N)
        (star (normMatrixColumnsEquiv T N U).1*(normMatrixColumnsEquiv T N U).2)*x 0*x 1+
      (normMatrixColumnsEquiv T N U).2.norm*x 1^2 := by
  rw [algebraTrace_eq_coefficients]
  simp only [polynomialOver,Matrix.mulVec,dotProduct,Fin.sum_univ_two,normMatrixColumnsEquiv,
    Equiv.coe_fn_mk,QuadraticAlgebra.norm_def,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  ring

/-- Evaluating at the two basis vectors and their sum recovers every
coefficient, including in characteristic two. -/
theorem raw_normPolynomial_iff_columns (T N : R) (U : Matrix (Fin 2) (Fin 2) R) :
    (∀ x, polynomialOver 1 T N (U.mulVec x)=polynomialOver 1 T N x) ↔
      (normMatrixColumnsEquiv T N U).1.norm=1 ∧
      Algebra.trace R (CoefficientAlgebra 1 T N)
        (star (normMatrixColumnsEquiv T N U).1*(normMatrixColumnsEquiv T N U).2)=T ∧
      (normMatrixColumnsEquiv T N U).2.norm=N := by
  constructor
  · intro h
    have h0 := h ![1,0]
    have h1 := h ![0,1]
    have h2 := h ![1,1]
    rw [normPolynomial_mulVec_columns] at h0 h1 h2
    simp only [polynomialOver,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      one_pow,zero_pow (by decide : (2 : ℕ)≠0),mul_one,mul_zero,zero_add,add_zero] at h0 h1 h2
    refine ⟨h0,?_,h1⟩
    linear_combination h2-h0-h1
  · rintro ⟨h0,ht,h1⟩ x
    rw [normPolynomial_mulVec_columns,h0,ht,h1]
    simp only [polynomialOver,one_mul]

/-- Exact coefficient-column presentation of all raw norm-polynomial matrices. -/
def rawNormMatricesEquivColumns (T N : R) :
    RawPolynomialIsometries (polynomialOver 1 T N) ≃
      {v : CoefficientAlgebra 1 T N × CoefficientAlgebra 1 T N //
        v.1.norm=1 ∧ Algebra.trace R (CoefficientAlgebra 1 T N) (star v.1*v.2)=T ∧ v.2.norm=N} where
  toFun U := ⟨normMatrixColumnsEquiv T N U.val,(raw_normPolynomial_iff_columns T N U.val).mp U.prop⟩
  invFun v := ⟨(normMatrixColumnsEquiv T N).symm v.val,
    (raw_normPolynomial_iff_columns T N _).mpr (by
      rw [(normMatrixColumnsEquiv T N).apply_symm_apply]
      exact v.prop)⟩
  left_inv U := by apply Subtype.ext; exact (normMatrixColumnsEquiv T N).symm_apply_apply U.val
  right_inv v := by apply Subtype.ext; exact (normMatrixColumnsEquiv T N).apply_symm_apply v.val

/-- The first column has norm one and inverse equal to its conjugate.
The second column then gives exactly the actual trace/norm fiber. -/
def normColumnsEquivNormOneFiber (T N : R) :
    {v : CoefficientAlgebra 1 T N × CoefficientAlgebra 1 T N //
      v.1.norm=1 ∧ Algebra.trace R (CoefficientAlgebra 1 T N) (star v.1*v.2)=T ∧ v.2.norm=N} ≃
      {z : CoefficientAlgebra 1 T N // z.norm=1} × TraceNormFiber T N := by
  have hstar (z : CoefficientAlgebra (1 : R) T N) (hz : z.norm=1) : z*star z=1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star,hz,map_one]
  have hstar' (z : CoefficientAlgebra (1 : R) T N) (hz : z.norm=1) : star z*z=1 := by
    rw [mul_comm,hstar z hz]
  refine
    { toFun := fun v => (⟨v.val.1,v.prop.1⟩,⟨star v.val.1*v.val.2,⟨v.prop.2.1,by
        rw [map_mul,QuadraticAlgebra.norm_star,v.prop.1,v.prop.2.2,one_mul]⟩⟩)
      invFun := fun z => ⟨(z.1.val,z.1.val*z.2.val),⟨z.1.prop,?_,?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← mul_assoc,hstar' z.1.val z.1.prop,one_mul]
    exact z.2.prop.1
  · rw [map_mul,z.1.prop,z.2.prop.2,one_mul]
  · intro v
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change v.val.1*(star v.val.1*v.val.2)=v.val.2
      rw [← mul_assoc,hstar v.val.1 v.prop.1,one_mul]
  · intro z
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      change star z.1.val*(z.1.val*z.2.val)=z.2.val
      rw [← mul_assoc,hstar' z.1.val z.1.prop,one_mul]

/-- The full raw matrix bijection, without an added GL2 condition. -/
def rawNormMatricesEquivNormOneFiber (T N : R) :
    RawPolynomialIsometries (polynomialOver 1 T N) ≃
      {z : CoefficientAlgebra 1 T N // z.norm=1} × TraceNormFiber T N :=
  (rawNormMatricesEquivColumns T N).trans (normColumnsEquivNormOneFiber T N)

/-- Raw polynomial matrix cardinality is exactly the product of its two
actual column factors. No finite norm-one lifting is used. -/
theorem card_rawNormMatrices (T N : R) :
    Nat.card (RawPolynomialIsometries (polynomialOver 1 T N))=
      Nat.card {z : CoefficientAlgebra 1 T N // z.norm=1}*Nat.card (TraceNormFiber T N) := by
  rw [Nat.card_congr (rawNormMatricesEquivNormOneFiber T N),Nat.card_prod]

/-- The factor is the original finite unit-norm kernel on its actual carrier. -/
theorem card_rawDiscriminantNormMatrices (R : Type*) [CommRing R] (D : ℤ) :
    Nat.card (RawPolynomialIsometries (polynomialOver (1 : R) ((D%2 : ℤ) : R)
      ((((D%2)^2-D)/4 : ℤ) : R))) =
      Nat.card (orderUnitNorm R D).ker *
        Nat.card (TraceNormFiber ((D%2 : ℤ) : R) ((((D%2)^2-D)/4 : ℤ) : R)) := by
  rw [card_rawNormMatrices]
  have h := Nat.card_congr (orderUnitNormKernelEquivNormOne R D)
  unfold DiscriminantAlgebra at h
  conv at h =>
    rhs
    rw [Int.cast_one]
  rw [← h]

/-- Coordinate conjugation on all matrices through an actual linear equivalence. -/
def conjugatePolynomialMatrix (e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R))
    (U : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  LinearMap.toMatrix' (e.toLinearMap.comp ((Matrix.toLin' U).comp e.symm.toLinearMap))

theorem conjugatePolynomialMatrix_mulVec (e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R))
    (U : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) :
    (conjugatePolynomialMatrix e U).mulVec x=e (U.mulVec (e.symm x)) := by
  rw [conjugatePolynomialMatrix,LinearMap.toMatrix'_mulVec]
  rfl

/-- Raw matrix conjugation is a bijection before any isometry condition. -/
def conjugatePolynomialMatrixEquiv (e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) :
    Matrix (Fin 2) (Fin 2) R ≃ Matrix (Fin 2) (Fin 2) R where
  toFun := conjugatePolynomialMatrix e
  invFun := conjugatePolynomialMatrix e.symm
  left_inv U := by
    apply Matrix.toLin'.injective
    ext x
    simp [conjugatePolynomialMatrix,LinearMap.comp_apply]
  right_inv U := by
    apply Matrix.toLin'.injective
    ext x
    simp [conjugatePolynomialMatrix,LinearMap.comp_apply]

/-- A unit-scaled polynomial norm model transports the exact raw matrix
carrier by conjugation. Only the scalar unit is canceled. -/
def rawPolynomialIsometriesEquivOfLinearEquiv
    (q q' : (Fin 2 → R) → R) (e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R))
    (u : Rˣ) (h : ∀ x, q x=(u : R)*q' (e x)) :
    RawPolynomialIsometries q ≃ RawPolynomialIsometries q' where
  toFun U := ⟨conjugatePolynomialMatrix e U.val,by
    intro x
    rw [conjugatePolynomialMatrix_mulVec]
    have hh := U.prop (e.symm x)
    rw [h,h,LinearEquiv.apply_symm_apply] at hh
    have hc := congrArg (fun r : R => (↑(u⁻¹) : R)*r) hh
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hc⟩
  invFun V := ⟨conjugatePolynomialMatrix e.symm V.val,by
    intro x
    rw [h,h,conjugatePolynomialMatrix_mulVec]
    simp only [LinearEquiv.symm_symm,LinearEquiv.apply_symm_apply]
    exact congrArg (fun r : R => (u : R)*r) (V.prop (e x))⟩
  left_inv U := by
    apply Subtype.ext
    exact (conjugatePolynomialMatrixEquiv e).left_inv U.val
  right_inv V := by
    apply Subtype.ext
    exact (conjugatePolynomialMatrixEquiv e).right_inv V.val

/-- The exact raw matrix equivalence for a unit-scaled norm model in the
Original discriminant algebra. No coordinate or genus certificate is added. -/
def rawPolynomialMatricesEquivOfDiscriminantNormModel
    (q : (Fin 2 → R) → R) (D : ℤ)
    (e : (Fin 2 → R) ≃ₗ[R] DiscriminantAlgebra R D) (u : Rˣ)
    (h : ∀ x, q x=(u : R)*(e x).norm) :
    RawPolynomialIsometries q ≃
      RawPolynomialIsometries (polynomialOver (1 : R) ((D%2 : ℤ) : R)
        ((((D%2)^2-D)/4 : ℤ) : R)) := by
  let c := algebraCoordinates ((1 : ℤ) : R) ((D%2 : ℤ) : R)
    ((((D%2)^2-D)/4 : ℤ) : R)
  have hc (x : Fin 2 → R) : (c x).norm=
      polynomialOver (1 : R) ((D%2 : ℤ) : R) ((((D%2)^2-D)/4 : ℤ) : R) x := by
    change (⟨x 0,x 1⟩ : CoefficientAlgebra ((1 : ℤ) : R) ((D%2 : ℤ) : R)
      ((((D%2)^2-D)/4 : ℤ) : R)).norm=polynomialOver (1 : R) ((D%2 : ℤ) : R)
        ((((D%2)^2-D)/4 : ℤ) : R) x
    simp only [QuadraticAlgebra.norm_def,polynomialOver,Int.cast_one]
    ring
  let g := e.trans c.symm
  apply rawPolynomialIsometriesEquivOfLinearEquiv q _ g u
  intro x
  rw [h,← hc]
  change (u : R)*(e x).norm=(u : R)*(c (c.symm (e x))).norm
  rw [c.apply_symm_apply]

/-- Unit-scaled norm models preserve the same raw matrix cardinality. -/
theorem card_rawPolynomialMatrices_of_normModel
    (q : (Fin 2 → R) → R) (D : ℤ)
    (e : (Fin 2 → R) ≃ₗ[R] DiscriminantAlgebra R D) (u : Rˣ)
    (h : ∀ x, q x=(u : R)*(e x).norm) :
    Nat.card (RawPolynomialIsometries q)=
      Nat.card (orderUnitNorm R D).ker*
        Nat.card (TraceNormFiber ((D%2 : ℤ) : R) ((((D%2)^2-D)/4 : ℤ) : R)) := by
  rw [Nat.card_congr (rawPolynomialMatricesEquivOfDiscriminantNormModel q D e u h),
    card_rawDiscriminantNormMatrices]

/-- Exact finite raw norm-polynomial matrix count in the original
order discriminant sign, before any maximal-field substitution. -/
theorem card_rawDiscriminantNormMatrices_prime_power (p : ℕ) [Fact p.Prime]
    (k : ℕ) (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hD0 : D≠0)
    (hk : padicValNat p D.natAbs<k) (hk2 : p=2 → 3≤k) :
    (Nat.card (RawPolynomialIsometries (polynomialOver (1 : ZMod (p^k))
      ((D%2 : ℤ) : ZMod (p^k)) ((((D%2)^2-D)/4 : ℤ) : ZMod (p^k)))) : ℤ)=
        2*(Nat.card (OrderUnitNormQuotient ℤ_[p] D) : ℤ)*
          ((p : ℤ)-conductorPrimeSign D p)*(p : ℤ)^(k-1+padicValNat p D.natAbs) := by
  rw [card_rawDiscriminantNormMatrices,Nat.cast_mul,
    card_orderUnitNorm_ker_prime_power p k (by omega) hk2 D hD,
    card_traceNormFiber_prime_power p k D hD hD0 hk (fun hp => by have hh := hk2 hp; omega)]
  push_cast
  have hpow : (p : ℤ)^(k-1+padicValNat p D.natAbs)=
      (p : ℤ)^(k-1)*(p : ℤ)^(padicValNat p D.natAbs) := pow_add _ _ _
  rw [hpow]
  ring

/-- Literal finite raw matrices, with the original universal polynomial
condition and no added determinant or GL2 filter. -/
def rawPolynomialMatrixResidues (n : ℕ) [NeZero n] (a b c : ℤ) :
    Finset (Matrix (Fin 2) (Fin 2) (ZMod n)) :=
  Finset.univ.filter (fun U => ∀ x : Fin 2 → ZMod n,
    polynomialOver (a : ZMod n) (b : ZMod n) (c : ZMod n) (U.mulVec x)=
      polynomialOver (a : ZMod n) (b : ZMod n) (c : ZMod n) x)

theorem card_rawPolynomialIsometries_eq_residues (n : ℕ) [NeZero n] (a b c : ℤ) :
    Nat.card (RawPolynomialIsometries
      (polynomialOver (a : ZMod n) (b : ZMod n) (c : ZMod n)))=
      (rawPolynomialMatrixResidues n a b c).card := by
  simp only [RawPolynomialIsometries,rawPolynomialMatrixResidues,
    Nat.card_eq_fintype_card,Fintype.card_subtype]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The actual primitive polynomial represents a unit in every finite
prime-power scalar ring, by reduction of its actual integral unit value. -/
theorem binaryPrimitivePolynomialOver_zmod_pow_exists_unit (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ∃ (v : Fin 2 → ZMod (p^k)) (u : (ZMod (p^k))ˣ),
      K.binaryPrimitivePolynomialOver (ZMod (p^k)) v=(u : ZMod (p^k)) := by
  obtain ⟨v,u,hu⟩ := K.binaryPrimitivePolynomialOver_padic_exists_unit p
  let f := PadicInt.toZModPow (p := p) k
  refine ⟨fun i => f (v i),Units.map f.toMonoidHom u,?_⟩
  have hh := congrArg f hu.symm
  simp only [binaryPrimitivePolynomialOver_apply,map_add,map_mul,map_pow,map_intCast] at hh
  simpa only [binaryPrimitivePolynomialOver_apply] using hh

/-- The raw matrices preserving the original primitive polynomial have
exactly the norm-kernel times trace/norm-fiber cardinality. -/
theorem card_rawBinaryPrimitiveMatrices (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Nat.card (RawPolynomialIsometries (K.binaryPrimitivePolynomialOver (ZMod (p^k)))) =
      Nat.card (orderUnitNorm (ZMod (p^k)) K.binaryPrimitiveDiscriminant).ker*
        Nat.card (TraceNormFiber ((K.binaryPrimitiveDiscriminant%2 : ℤ) : ZMod (p^k))
          ((((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4 : ℤ) : ZMod (p^k))) := by
  obtain ⟨v,u,hv⟩ := K.binaryPrimitivePolynomialOver_zmod_pow_exists_unit p k
  exact card_rawPolynomialMatrices_of_normModel _ K.binaryPrimitiveDiscriminant
    (K.binaryLocalNormEquiv v u hv) u
    (K.binaryPrimitivePolynomialOver_eq_unit_mul_localNorm v u hv)

/-- Evaluated raw primitive-polynomial matrix count, for the same actual
lattice, field, conductor and original local norm index. -/
theorem card_rawBinaryPrimitiveMatrices_prime_power (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : padicValNat p K.binaryPrimitiveDiscriminant.natAbs<k) (hk2 : p=2 → 3≤k) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (Nat.card (RawPolynomialIsometries (K.binaryPrimitivePolynomialOver (ZMod (p^k)))) : ℚ) =
      2*(Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℚ)*
        (p : ℚ)^(k+padicValNat p K.binaryPrimitiveDiscriminant.natAbs)*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℚ)/(p : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have ht : (Nat.card (TraceNormFiber ((K.binaryPrimitiveDiscriminant%2 : ℤ) : ZMod (p^k))
      ((((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4 : ℤ) : ZMod (p^k))) : ℚ) =
      2*(p : ℚ)^(padicValNat p K.binaryPrimitiveDiscriminant.natAbs) := by
    exact_mod_cast card_traceNormFiber_prime_power p k K.binaryPrimitiveDiscriminant
      K.binaryPrimitiveDiscriminant_mod_four (ne_of_lt K.binaryPrimitiveDiscriminant_neg) hk
      (fun hp => by have hh := hk2 hp; omega)
  rw [K.card_rawBinaryPrimitiveMatrices,Nat.cast_mul,
    K.card_binaryOrderNormKernel_prime_power p k (by omega) hk2,ht]
  have hpow : (p : ℚ)^(k+padicValNat p K.binaryPrimitiveDiscriminant.natAbs)=
      (p : ℚ)^k*(p : ℚ)^(padicValNat p K.binaryPrimitiveDiscriminant.natAbs) := pow_add _ _ _
  rw [hpow]
  ring

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.RawPolynomialIsometries
#assert_standard_axioms BinaryNormIdeal.normMatrixColumnsEquiv
#assert_standard_axioms BinaryNormIdeal.normPolynomial_mulVec_columns
#assert_standard_axioms BinaryNormIdeal.raw_normPolynomial_iff_columns
#assert_standard_axioms BinaryNormIdeal.rawNormMatricesEquivColumns
#assert_standard_axioms BinaryNormIdeal.normColumnsEquivNormOneFiber
#assert_standard_axioms BinaryNormIdeal.rawNormMatricesEquivNormOneFiber
#assert_standard_axioms BinaryNormIdeal.card_rawNormMatrices
#assert_standard_axioms BinaryNormIdeal.card_rawDiscriminantNormMatrices
#assert_standard_axioms BinaryNormIdeal.conjugatePolynomialMatrix
#assert_standard_axioms BinaryNormIdeal.conjugatePolynomialMatrix_mulVec
#assert_standard_axioms BinaryNormIdeal.conjugatePolynomialMatrixEquiv
#assert_standard_axioms BinaryNormIdeal.rawPolynomialIsometriesEquivOfLinearEquiv
#assert_standard_axioms BinaryNormIdeal.rawPolynomialMatricesEquivOfDiscriminantNormModel
#assert_standard_axioms BinaryNormIdeal.card_rawPolynomialMatrices_of_normModel
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomialOver_zmod_pow_exists_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryPrimitiveMatrices
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryPrimitiveMatrices_prime_power
#assert_standard_axioms BinaryNormIdeal.card_rawDiscriminantNormMatrices_prime_power
#assert_standard_axioms BinaryNormIdeal.rawPolynomialMatrixResidues
#assert_standard_axioms BinaryNormIdeal.card_rawPolynomialIsometries_eq_residues
