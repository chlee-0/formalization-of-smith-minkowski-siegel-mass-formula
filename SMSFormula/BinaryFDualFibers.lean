import SMSFormula.BinaryContentMatrixLifts
import SMSFormula.LocalDensity

/-!
# Raw polynomial matrices and the original binary F-dual quotient

The universal quadratic predicate descends through the original integral
F-dual denominator. This keeps all primes and all raw matrices.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The two quotient columns form an additive map for any denominator
inclusion. This map acts on all families, before imposing a predicate. -/
def binaryQuotientFamilyAddHom {D E : Submodule ℤ (Fin 2 → ℤ)} (hDE : D≤E) :
    (Fin 2 → localDualQuotientTarget D) →+ (Fin 2 → localDualQuotientTarget E) where
  toFun := localDualQuotientFamilyOfLE hDE
  map_zero' := by ext i; exact map_zero _
  map_add' X Y := by ext i; exact map_add _ _ _

/-- The actual two-column kernel is the product of the two actual
one-column kernels. No matrix-unit condition occurs. -/
def binaryQuotientFamilyKernelEquiv {D E : Submodule ℤ (Fin 2 → ℤ)} (hDE : D≤E) :
    (binaryQuotientFamilyAddHom hDE).ker ≃
      (Fin 2 → (localDualQuotientMapOfLE hDE).ker) where
  toFun Y i := ⟨Y.val i,by
    change localDualQuotientMapOfLE hDE (Y.val i)=0
    exact congr_fun Y.prop i⟩
  invFun z := ⟨fun i=>(z i).val,by ext i; exact (z i).prop⟩
  left_inv Y := by apply Subtype.ext; rfl
  right_inv z := by ext i; rfl

/-- Exact cardinal effect of enlarging an admissible denominator on
universal-representative solution families, at every prime. -/
theorem binary_coordinateDualCount_eq_mul_subquotient
    (K : PositiveDefiniteIntegralLattice 2) (p k : ℕ) [Fact p.Prime]
    (D E : Submodule ℤ (Fin 2 → ℤ)) (hD : Module.finrank ℤ D=2)
    (hE : IsDualQuotientAdmissible K p k E) (hDE : D≤E) :
    coordinateLocalDualQuotientCount K p k D hD=
      coordinateLocalDualQuotientCount K p k E hE.1*
        Nat.card (E ⧸ D.comap E.subtype)^2 := by
  let f := binaryQuotientFamilyAddHom hDE
  have hf : Function.Surjective f := by
    intro Y
    choose Z hZ using fun i=>localDualQuotientMapOfLE_surjective hDE (Y i)
    exact ⟨Z,by ext i; exact hZ i⟩
  let S : Set (Fin 2 → localDualQuotientTarget E) :=
    {Y | Y∈localDualQuotientSolutionFamilies K p k E hE.1}
  have he (Y : Fin 2 → localDualQuotientTarget D) :
      Y∈localDualQuotientSolutionFamilies K p k D hD ↔ f Y∈S := by
    constructor
    · exact localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
        (hE := hE) hDE
    · intro hY
      exact localDualQuotientFamilyOfLE_preimage_mem_localDualQuotientSolutionFamilies
        hDE hY rfl
  have hker : Nat.card f.ker=Nat.card (E ⧸ D.comap E.subtype)^2 := by
    rw [Nat.card_congr (binaryQuotientFamilyKernelEquiv hDE),Nat.card_fun,Nat.card_fin]
    rw [localDualQuotientMapOfLE_ker_card_eq_subquotient hDE]
  have hc : Nat.card {Y // Y∈localDualQuotientSolutionFamilies K p k D hD}=
      Nat.card S*Nat.card f.ker := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight he),
      Nat.card_congr (additivePreimageEquiv f hf S),Nat.card_prod]
  rw [hker] at hc
  change Nat.card {Y // Y∈localDualQuotientSolutionFamilies K p k D hD}=
    Nat.card {Y // Y∈localDualQuotientSolutionFamilies K p k E hE.1}*
      Nat.card (E ⧸ D.comap E.subtype)^2 at hc
  simpa only [coordinateLocalDualQuotientCount,Nat.card_eq_fintype_card,
    Fintype.card_coe] using hc

/-- Exact scalar extension of the actual original norm, in any scalar ring. -/
theorem binary_quadForm_intCast_over (K : PositiveDefiniteIntegralLattice 2)
    {R : Type*} [CommRing R] (x : Fin 2 → ℤ) :
    (K.quadForm x : R)=dotProduct (fun i=>(x i : R))
      ((K.pairingMatrix.map (Int.cast : ℤ → R)).mulVec (fun i=>(x i : R))) := by
  simp [quadForm_eq_dotProduct,dotProduct,Matrix.mulVec]

/-- The clean quotient's exact universal-representative predicate is the
Original quadratic polynomial predicate on its residue matrix, even at two. -/
theorem binary_cleanFamily_mem_iff_raw (K : PositiveDefiniteIntegralLattice 2)
    (p k : ℕ) [Fact p.Prime]
    (Y : Fin 2 → localDualQuotientTarget (primePowCoordinateSubmodule (n := 2) p k)) :
    Y∈localDualQuotientSolutionFamilies K p k (primePowCoordinateSubmodule p k)
      (primePowCoordinateSubmodule_rank p k) ↔
    ∀ v : Fin 2 → ZMod (p^k),
      dotProduct ((localDualQuotientFamilyMatrix p k Y).mulVec v)
        ((K.pairingMatrix.map (Int.cast : ℤ → ZMod (p^k))).mulVec
          ((localDualQuotientFamilyMatrix p k Y).mulVec v))=
      dotProduct v ((K.pairingMatrix.map (Int.cast : ℤ → ZMod (p^k))).mulVec v) := by
  let D := primePowCoordinateSubmodule (n := 2) p k
  have hv (x y : Fin 2 → ℤ) (hxy : quotientBasisFamilyMap D Y x=D.mkQ y) :
      (localDualQuotientFamilyMatrix p k Y).mulVec (fun i=>(x i : ZMod (p^k)))=
        (fun i=>(y i : ZMod (p^k))) := by
    have hm := localDualQuotientFamilyMatrix_mulVec_eq p k Y x
    rw [hxy,primePowQuotientVector_mkQ] at hm
    exact hm
  rw [mem_localDualQuotientSolutionFamilies_iff]
  constructor
  · intro h v
    let x : Fin 2 → ℤ := fun i=>(v i).val
    have hx : (fun i=>(x i : ZMod (p^k)))=v := by
      ext i
      change (((v i).val : ℤ) : ZMod (p^k))=v i
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (v i)
    let y : Fin 2 → ℤ := Quotient.out (quotientBasisFamilyMap D Y x)
    have hxy : quotientBasisFamilyMap D Y x=D.mkQ y :=
      (Submodule.Quotient.mk_out _).symm
    have hh := h x y hxy
    rw [K.binary_quadForm_intCast_over,K.binary_quadForm_intCast_over] at hh
    rw [← hx,hv x y hxy]
    exact hh
  · intro h x y hxy
    have hh := h (fun i=>(x i : ZMod (p^k)))
    rw [hv x y hxy] at hh
    simpa only [K.binary_quadForm_intCast_over] using hh

/-- Raw original polynomial matrices and clean quotient solution families
are in exact bijection. Only the columns are reduced; no GL2 filter occurs. -/
def binaryRawMatricesEquivCleanFamilies (K : PositiveDefiniteIntegralLattice 2)
    (p k : ℕ) [Fact p.Prime] :
    RawPolynomialIsometries (fun v : Fin 2 → ZMod (p^k) =>
      dotProduct v ((K.pairingMatrix.map (Int.cast : ℤ → ZMod (p^k))).mulVec v)) ≃
    {Y : Fin 2 → localDualQuotientTarget (primePowCoordinateSubmodule (n := 2) p k) //
      Y∈localDualQuotientSolutionFamilies K p k (primePowCoordinateSubmodule p k)
        (primePowCoordinateSubmodule_rank p k)} where
  toFun U := ⟨localDualQuotientLiftFamily p k U.val,by
    rw [K.binary_cleanFamily_mem_iff_raw,localDualQuotientFamilyMatrix_liftFamily]
    exact U.prop⟩
  invFun Y := ⟨localDualQuotientFamilyMatrix p k Y.val,
    (K.binary_cleanFamily_mem_iff_raw p k Y.val).mp Y.prop⟩
  left_inv U := by apply Subtype.ext; exact localDualQuotientFamilyMatrix_liftFamily p k U.val
  right_inv Y := by apply Subtype.ext; exact localDualQuotientLiftFamily_familyMatrix p k Y.val

/-- The exact all-prime original F-dual fiber identity. The denominator
subquotient is literal, before evaluating it by the original determinant. -/
theorem card_rawBinaryMatrices_eq_dualCount_mul_subquotient (K : PositiveDefiniteIntegralLattice 2)
    (p k : ℕ) [Fact p.Prime] :
    Nat.card (RawPolynomialIsometries (fun v : Fin 2 → ZMod (p^k) =>
      dotProduct v ((K.pairingMatrix.map (Int.cast : ℤ → ZMod (p^k))).mulVec v)))=
      localDualQuotientCount K p k*
        Nat.card (pairingMatrixLocalDualCoordinateSubmodule K p k ⧸
          (primePowCoordinateSubmodule (n := 2) p k).comap
            (pairingMatrixLocalDualCoordinateSubmodule K p k).subtype)^2 := by
  rw [Nat.card_congr (K.binaryRawMatricesEquivCleanFamilies p k)]
  have hc : Nat.card {Y : Fin 2 → localDualQuotientTarget
      (primePowCoordinateSubmodule (n := 2) p k) //
      Y∈localDualQuotientSolutionFamilies K p k (primePowCoordinateSubmodule p k)
        (primePowCoordinateSubmodule_rank p k)}=
      coordinateLocalDualQuotientCount K p k (primePowCoordinateSubmodule p k)
        (primePowCoordinateSubmodule_rank p k) := by
    simp only [coordinateLocalDualQuotientCount,Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [hc,binary_coordinateDualCount_eq_mul_subquotient K p k _ _
    (primePowCoordinateSubmodule_rank p k) (pairingMatrixLocalDualCoordinateSubmodule_admissible K p k)
    (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule K p k),
    ← K.localDualQuotientCount_eq_pairingMatrixLocalDual]

/-- Smith normal form evaluates the original one-column F-dual
subquotient at every depth bounding det(F)'s valuation, including two. -/
theorem binary_FDual_subquotient_card (K : PositiveDefiniteIntegralLattice 2)
    (p k : ℕ) [Fact p.Prime] (hk : padicValInt p K.pairingDeterminant≤k) :
    Nat.card (pairingMatrixLocalDualCoordinateSubmodule K p k ⧸
      (primePowCoordinateSubmodule (n := 2) p k).comap
        (pairingMatrixLocalDualCoordinateSubmodule K p k).subtype)=
      p^padicValInt p K.pairingDeterminant := by
  have hdet : K.pairingMatrix.det≠0 := ne_of_gt K.pairingDeterminant_pos
  obtain ⟨P,Q,d,hP,hQ,hdiag⟩ := exists_integral_diagonalization_of_det_ne_zero K.pairingMatrix hdet
  have hPdet : IsUnit P.det := by rwa [Matrix.isUnit_iff_isUnit_det] at hP
  have hQdet : IsUnit Q.det := by rwa [Matrix.isUnit_iff_isUnit_det] at hQ
  have hprod : (∏ i : Fin 2,d i)≠0 := by
    have hh : (Matrix.diagonal d).det≠0 := by
      rw [← hdiag,Matrix.det_mul,Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero hPdet.ne_zero hdet) hQdet.ne_zero
    simpa only [Matrix.det_diagonal] using hh
  have hd (i : Fin 2) : d i≠0 := by
    intro hi
    exact hprod (Finset.prod_eq_zero_iff.mpr ⟨i,Finset.mem_univ i,hi⟩)
  have hsum : (∑ i : Fin 2,padicValInt p (d i))=padicValInt p K.pairingDeterminant :=
    (padicValInt_det_eq_sum_diagonal_of_left_right_mul_eq_diagonal
      K.pairingMatrix P Q p d hP hQ hdiag hd).symm
  have hdval (i : Fin 2) : padicValInt p (d i)≤k := by
    have hi : padicValInt p (d i)≤∑ j : Fin 2,padicValInt p (d j) :=
      Finset.single_le_sum (fun j _=>Nat.zero_le (padicValInt p (d j))) (Finset.mem_univ i)
    rw [hsum] at hi
    exact hi.trans hk
  let v : Fin 2 → ℕ := fun i=>truncatedPadicValInt p k (d i)
  have hv (i : Fin 2) : v i≤k := truncatedPadicValInt_le p k (d i)
  have hfac (i : Fin 2) : ∃ u : ℤ,
      (v i<k → IsUnit (u : ZMod (primePowModulus p k : ℕ))) ∧
      d i=u*(p^v i : ℤ) := exists_unit_factor_truncatedPadicValInt p k (d i)
  choose u hu using hfac
  have hdiag' : P*K.pairingMatrix*Q=Matrix.diagonal (fun i=>u i*(p^v i : ℤ)) := by
    rw [hdiag]
    congr 1
    funext i
    exact (hu i).2
  have hh := pairingMatrixLocalDualCoordinateSubmodule_subquotient_card_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
    K P Q p k u v hv (fun i=>(hu i).1) hP hQ hdiag'
  rw [sum_truncatedPadicValInt_eq_padicValInt_det_of_left_right_mul_eq_diagonal
    K.pairingMatrix P Q p k d hP hQ hdiag hdval hd] at hh
  exact hh

/-- The original F-dual numerator comparison has exact factor
p^(2*v_p(det F)). Both columns use the actual integral F. -/
theorem card_rawBinaryMatrices_eq_dualCount_mul_prime_power (K : PositiveDefiniteIntegralLattice 2)
    (p k : ℕ) [Fact p.Prime] (hk : padicValInt p K.pairingDeterminant≤k) :
    Nat.card (RawPolynomialIsometries (fun v : Fin 2 → ZMod (p^k) =>
      dotProduct v ((K.pairingMatrix.map (Int.cast : ℤ → ZMod (p^k))).mulVec v)))=
      localDualQuotientCount K p k*p^(2*padicValInt p K.pairingDeterminant) := by
  rw [K.card_rawBinaryMatrices_eq_dualCount_mul_subquotient,
    K.binary_FDual_subquotient_card p k hk,← pow_mul,mul_comm (padicValInt p K.pairingDeterminant) 2]

/-- The all-prime original F-dual/content comparison as a natural-number
identity. No negative natural exponent or caller denominator certificate occurs. -/
theorem binary_dualCount_mul_detPower_eq_content_mul_primitive (K : PositiveDefiniteIntegralLattice 2)
    (p k : ℕ) [Fact p.Prime]
    (hk : padicValInt p K.pairingDeterminant≤k+padicValNat p K.binaryContent) :
    p^(2*padicValInt p K.pairingDeterminant)*
      localDualQuotientCount K p (k+padicValNat p K.binaryContent)=
      p^(4*padicValNat p K.binaryContent)*Nat.card (RawPolynomialIsometries
        (K.binaryPrimitivePolynomialOver (ZMod (p^k)))) := by
  rw [mul_comm,← K.card_rawBinaryMatrices_eq_dualCount_mul_prime_power p _ hk,
    K.card_rawBinaryOriginalMatrices_content]

/-- The original polar discriminant has valuation 2h+a, with actual
content h and actual primitive discriminant valuation a. -/
theorem binary_polarDeterminant_val_eq_content (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    padicValInt p K.polarDeterminant=2*padicValNat p K.binaryContent+
      padicValNat p K.binaryPrimitiveDiscriminant.natAbs := by
  have he : K.polarDeterminant=-((K.binaryContent : ℤ)^2*K.binaryPrimitiveDiscriminant) := by
    rw [K.polarDeterminant_eq_two_pow_mul_pairingDeterminant,
      K.binaryContent_sq_mul_binaryPrimitiveDiscriminant]
    norm_num
  have ha : K.polarDeterminant.natAbs=K.binaryContent^2*K.binaryPrimitiveDiscriminant.natAbs := by
    rw [he,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
  rw [padicValInt,ha,padicValNat.mul (pow_ne_zero _ (ne_of_gt K.binaryContent_pos))
    (Int.natAbs_ne_zero.mpr (ne_of_lt K.binaryPrimitiveDiscriminant_neg)),
    padicValNat.pow _ (ne_of_gt K.binaryContent_pos)]

/-- The density's existing preferred depth is the content lift of the
explicit stable primitive depth h+a+3. -/
theorem binary_preferredDepth_eq_contentDepth (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    localDensityHenselExponent K p=
      (padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3)+
        padicValNat p K.binaryContent := by
  rw [localDensityHenselExponent,K.binary_polarDeterminant_val_eq_content]
  omega

/-- The actual preferred-depth F-dual count is bound to the stable
primitive matrix count with no caller depth or denominator certificate. -/
theorem binary_dualCount_preferred_mul_detPower (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    p^(2*padicValInt p K.pairingDeterminant)*
      localDualQuotientCount K p (localDensityHenselExponent K p)=
      p^(4*padicValNat p K.binaryContent)*Nat.card (RawPolynomialIsometries
        (K.binaryPrimitivePolynomialOver
          (ZMod (p^(padicValNat p K.binaryContent+
            padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3))))) := by
  rw [K.binary_preferredDepth_eq_contentDepth]
  apply K.binary_dualCount_mul_detPower_eq_content_mul_primitive
  have hh := K.padicValInt_pairingDeterminant_le_polarDeterminant p
  rw [K.binary_polarDeterminant_val_eq_content] at hh
  omega

/-- Evaluated original F-dual count at the native density depth. This
keeps the exact positive determinant power on the left, rather than
introducing negative natural exponents. -/
theorem binary_dualCount_preferred_evaluated (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (p : ℚ)^(2*padicValInt p K.pairingDeterminant)*
      (localDualQuotientCount K p (localDensityHenselExponent K p) : ℚ)=
      2*(Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℚ)*
        (p : ℚ)^((padicValNat p K.binaryContent+
            padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3)+
          4*padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs)*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℚ)/(p : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have hc : (p : ℚ)^(2*padicValInt p K.pairingDeterminant)*
      (localDualQuotientCount K p (localDensityHenselExponent K p) : ℚ)=
      (p : ℚ)^(4*padicValNat p K.binaryContent)*
        (Nat.card (RawPolynomialIsometries (K.binaryPrimitivePolynomialOver
          (ZMod (p^(padicValNat p K.binaryContent+
            padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3))))) : ℚ) := by
    exact_mod_cast K.binary_dualCount_preferred_mul_detPower p
  rw [hc,K.card_rawBinaryPrimitiveMatrices_prime_power p _ (by omega) (by omega)]
  rw [show (padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3)+
      4*padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs=
    4*padicValNat p K.binaryContent+
      ((padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3)+
        padicValNat p K.binaryPrimitiveDiscriminant.natAbs) by omega,pow_add]
  ring

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryQuotientFamilyAddHom
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryQuotientFamilyKernelEquiv
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_coordinateDualCount_eq_mul_subquotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_quadForm_intCast_over
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_cleanFamily_mem_iff_raw
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryRawMatricesEquivCleanFamilies
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryMatrices_eq_dualCount_mul_subquotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_FDual_subquotient_card
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryMatrices_eq_dualCount_mul_prime_power
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_dualCount_mul_detPower_eq_content_mul_primitive
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_polarDeterminant_val_eq_content
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_preferredDepth_eq_contentDepth
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_dualCount_preferred_mul_detPower
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_dualCount_preferred_evaluated
