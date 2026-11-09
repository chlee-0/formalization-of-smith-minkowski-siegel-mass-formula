import SMSFormula.Applications.Unimodular.ModEightTransport.FiniteCertificates
import SMSFormula.Applications.Unimodular.StableIdentityComparison.NativeQuadraticLift
import SMSFormula.Applications.Unimodular.StableIdentityComparison.FixedLine
import SMSFormula.Applications.Unimodular.GenusMass
import SMSFormula.StandardAxiomsGuard

/-!
# Generic native dyadic-count transport

This generalizes the native-count adapter for the seed lattice
to an arbitrary lattice.  The final transport theorem takes
an explicit finite quadratic equivalence as a hypothesis; this module does not
construct it.  No classification hypothesis or density
value is hidden in a definition.
-/

noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice UnimodularMass

namespace TypeIIModEightNativeTransport

variable {n : ℕ}

/-- Native quadratic form on mod-four coordinates, with values mod eight. -/
def norm (L : PositiveDefiniteIntegralLattice n) (v : Fin n → ZMod 4) : ZMod 8 :=
  L.zmodQuadForm 8 (fun i => zmodFourLiftToZModEight (v i))

lemma norm_intCast (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    norm L (fun i => (x i : ZMod 4)) = (L.quadForm x : ZMod 8) := by
  unfold norm
  rw [StableIdentityComparisonSeedNativeAdapter.zmodQuadForm_lift_intCast_eq]
  exact L.zmodQuadForm_intCast 8 x

/-- Reduce an integral matrix modulo four. -/
def intMatrixModFour (U : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod 4) :=
  U.map (Int.cast : ℤ → ZMod 4)

/-- Reduce an integral matrix modulo eight. -/
def intMatrixModEight (U : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod 8) :=
  U.map (Int.cast : ℤ → ZMod 8)

lemma intMatrix_mulVec_intCast_zmod (m : ℕ) (U : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    (fun i => ((U.mulVec x i : ℤ) : ZMod m)) =
      (U.map (Int.cast : ℤ → ZMod m)).mulVec (fun i => ((x i : ℤ) : ZMod m)) := by
  funext i
  change (((∑ j, U i j * x j : ℤ) : ZMod m)) =
    ∑ j, ((U i j : ℤ) : ZMod m) * ((x j : ℤ) : ZMod m)
  simp

/-- A matrix congruence modulo `m` transports the existing reduced quadratic form. -/
theorem zmodQuadForm_conj_of_mod_congruence (m : ℕ)
    (L M : PositiveDefiniteIntegralLattice n) (U : Matrix (Fin n) (Fin n) (ZMod m))
    (hU : U.transpose * M.pairingMatrix.map (Int.cast : ℤ → ZMod m) * U =
      L.pairingMatrix.map (Int.cast : ℤ → ZMod m))
    (x : Fin n → ZMod m) :
    M.zmodQuadForm m (U.mulVec x) = L.zmodQuadForm m x := by
  have hM :
      M.zmodQuadForm m (U.mulVec x) =
        dotProduct (U.mulVec x)
          ((M.pairingMatrix.map (Int.cast : ℤ → ZMod m)).mulVec (U.mulVec x)) := by
    simp [PositiveDefiniteIntegralLattice.zmodQuadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
    ring_nf
  have hL :
      L.zmodQuadForm m x =
        dotProduct x ((L.pairingMatrix.map (Int.cast : ℤ → ZMod m)).mulVec x) := by
    simp [PositiveDefiniteIntegralLattice.zmodQuadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
    ring_nf
  rw [hM, hL]
  calc
    dotProduct (U.mulVec x) ((M.pairingMatrix.map (Int.cast : ℤ → ZMod m)).mulVec (U.mulVec x)) =
        (((U.mulVec x) ᵥ* M.pairingMatrix.map (Int.cast : ℤ → ZMod m)) ⬝ᵥ
          (U.mulVec x)) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (x ᵥ* (Uᵀ * M.pairingMatrix.map (Int.cast : ℤ → ZMod m))) ⬝ᵥ (U.mulVec x) := by
          rw [Matrix.vecMul_mulVec]
    _ = ((x ᵥ* (Uᵀ * M.pairingMatrix.map (Int.cast : ℤ → ZMod m))) ᵥ* U) ⬝ᵥ x := by
          rw [Matrix.dotProduct_mulVec]
    _ = (x ᵥ* (Uᵀ * M.pairingMatrix.map (Int.cast : ℤ → ZMod m) * U)) ⬝ᵥ x := by
          rw [Matrix.vecMul_vecMul]
    _ = (x ᵥ* L.pairingMatrix.map (Int.cast : ℤ → ZMod m)) ⬝ᵥ x := by
          rw [hU]
    _ = dotProduct x ((L.pairingMatrix.map (Int.cast : ℤ → ZMod m)).mulVec x) := by
          rw [Matrix.dotProduct_mulVec]

/-- An integral mod-eight Gram congruence gives the finite norm identity on
mod-four coordinates required by the native transport adapter. -/
theorem norm_intMatrixModFour_mulVec_eq_of_modEight_congruence
    (L M : PositiveDefiniteIntegralLattice n) (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : (intMatrixModEight U).transpose * M.pairingMatrix.map (Int.cast : ℤ → ZMod 8) *
      intMatrixModEight U = L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) :
    ∀ x : Fin n → ZMod 4, norm M ((intMatrixModFour U).mulVec x) = norm L x := by
  intro x
  let xZ : Fin n → ℤ := fun i => (x i).val
  have hx : (fun i : Fin n => ((xZ i : ℤ) : ZMod 4)) = x := by
    funext i
    dsimp [xZ]
    exact ZMod.natCast_zmod_val (x i)
  have hmul4 :
      (fun i : Fin n => (((U.mulVec xZ) i : ℤ) : ZMod 4)) =
        (intMatrixModFour U).mulVec x := by
    rw [intMatrix_mulVec_intCast_zmod (n := n) 4 U xZ, hx]
    rfl
  have hmul8 :
      (fun i : Fin n => (((U.mulVec xZ) i : ℤ) : ZMod 8)) =
        (intMatrixModEight U).mulVec (fun i : Fin n => ((xZ i : ℤ) : ZMod 8)) := by
    rw [intMatrix_mulVec_intCast_zmod (n := n) 8 U xZ]
    rfl
  calc
    norm M ((intMatrixModFour U).mulVec x) =
        norm M (fun i : Fin n => (((U.mulVec xZ) i : ℤ) : ZMod 4)) := by
          rw [hmul4]
    _ = ((M.quadForm (U.mulVec xZ) : ℤ) : ZMod 8) := norm_intCast M (U.mulVec xZ)
    _ = M.zmodQuadForm 8 (fun i : Fin n => (((U.mulVec xZ) i : ℤ) : ZMod 8)) := by
          rw [M.zmodQuadForm_intCast]
    _ = M.zmodQuadForm 8 ((intMatrixModEight U).mulVec
          (fun i : Fin n => ((xZ i : ℤ) : ZMod 8))) := by
          rw [hmul8]
    _ = L.zmodQuadForm 8 (fun i : Fin n => ((xZ i : ℤ) : ZMod 8)) :=
          zmodQuadForm_conj_of_mod_congruence 8 L M (intMatrixModEight U) hU _
    _ = ((L.quadForm xZ : ℤ) : ZMod 8) := L.zmodQuadForm_intCast 8 xZ
    _ = norm L (fun i : Fin n => ((xZ i : ℤ) : ZMod 4)) := (norm_intCast L xZ).symm
    _ = norm L x := by rw [hx]

/-- The canonical reduction map from `ZMod 8` to `ZMod 4`. -/
def zmodEightToFour : ZMod 8 →+* ZMod 4 :=
  ZMod.castHom (by omega : 4 ∣ 8) (ZMod 4)

/-- Reduce a mod-eight matrix modulo four. -/
def zmodEightMatrixModFour (U : Matrix (Fin n) (Fin n) (ZMod 8)) :
    Matrix (Fin n) (Fin n) (ZMod 4) :=
  U.map zmodEightToFour

/-- Choose the least nonnegative integer representatives of a mod-eight matrix. -/
def zmodEightMatrixIntLift (U : Matrix (Fin n) (Fin n) (ZMod 8)) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (U i j).val

lemma zmodEightToFour_val (a : ZMod 8) :
    (((a.val : ℕ) : ℤ) : ZMod 4) = zmodEightToFour a := by
  change ((a.val : ℕ) : ZMod 4) = zmodEightToFour a
  unfold zmodEightToFour
  rw [ZMod.castHom_apply]
  calc
    ((a.val : ℕ) : ZMod 4) = ((a.val : ZMod 8).cast : ZMod 4) := by
      rw [ZMod.cast_natCast (by omega : 4 ∣ 8)]
    _ = a.cast := by rw [ZMod.natCast_zmod_val]

lemma intMatrixModEight_zmodEightMatrixIntLift
    (U : Matrix (Fin n) (Fin n) (ZMod 8)) :
    intMatrixModEight (zmodEightMatrixIntLift U) = U := by
  ext i j
  change ((((U i j).val : ℕ) : ℤ) : ZMod 8) = U i j
  exact_mod_cast ZMod.natCast_zmod_val (U i j)

lemma intMatrixModFour_zmodEightMatrixIntLift
    (U : Matrix (Fin n) (Fin n) (ZMod 8)) :
    intMatrixModFour (zmodEightMatrixIntLift U) = zmodEightMatrixModFour U := by
  ext i j
  exact zmodEightToFour_val (U i j)

/-- A mod-eight Gram congruence gives the mod-four norm identity required by
the native transport adapter.  This version consumes the finite certificates
directly over `ZMod 8`; the integral lift is internal. -/
theorem norm_zmodEightMatrixModFour_mulVec_eq_of_congruence
    (L M : PositiveDefiniteIntegralLattice n) (U : Matrix (Fin n) (Fin n) (ZMod 8))
    (hU : U.transpose * M.pairingMatrix.map (Int.cast : ℤ → ZMod 8) * U =
      L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) :
    ∀ x : Fin n → ZMod 4, norm M ((zmodEightMatrixModFour U).mulVec x) = norm L x := by
  have hUint :
      (intMatrixModEight (zmodEightMatrixIntLift U)).transpose *
          M.pairingMatrix.map (Int.cast : ℤ → ZMod 8) *
        intMatrixModEight (zmodEightMatrixIntLift U) =
          L.pairingMatrix.map (Int.cast : ℤ → ZMod 8) := by
    simpa [intMatrixModEight_zmodEightMatrixIntLift U] using hU
  intro x
  have hnorm := norm_intMatrixModFour_mulVec_eq_of_modEight_congruence
    L M (zmodEightMatrixIntLift U) hUint x
  simpa [intMatrixModFour_zmodEightMatrixIntLift U] using hnorm

lemma zmodEightMatrixModFour_mul
    (U V : Matrix (Fin n) (Fin n) (ZMod 8)) :
    zmodEightMatrixModFour (U * V) =
      zmodEightMatrixModFour U * zmodEightMatrixModFour V := by
  change (U * V).map zmodEightToFour = U.map zmodEightToFour * V.map zmodEightToFour
  exact Matrix.map_mul (L := U) (M := V) (f := zmodEightToFour)

lemma zmodEightMatrixModFour_one :
    zmodEightMatrixModFour (1 : Matrix (Fin n) (Fin n) (ZMod 8)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [zmodEightMatrixModFour, zmodEightToFour]
  · simp [zmodEightMatrixModFour, h]

lemma zmodEightMatrixModFour_mul_inverse_of_mul_inverse
    (U V : Matrix (Fin n) (Fin n) (ZMod 8)) (hUV : U * V = 1) :
    zmodEightMatrixModFour U * zmodEightMatrixModFour V = 1 := by
  rw [← zmodEightMatrixModFour_mul, hUV, zmodEightMatrixModFour_one]

abbrev normIsometry (L : PositiveDefiniteIntegralLattice n) := StableIdentityFixedLine.Iso (norm L)

abbrev nativeMatrix (L : PositiveDefiniteIntegralLattice n) :=
  {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus 2 2 : ℕ)) //
    localDualQuotientLiftFamily (n := n) 2 2 X ∈
      localDualQuotientSolutionFamilies L 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2)}

instance (L : PositiveDefiniteIntegralLattice n) : Fintype (nativeMatrix L) := by
  classical
  unfold nativeMatrix
  infer_instance

/-- This is the generic version of the seed adapter; no evenness is used. -/
theorem nativeMatrix_preserves (L : PositiveDefiniteIntegralLattice n) (X : nativeMatrix L) :
    ∀ v : Fin n → ZMod 4, norm L (X.1.mulVec v) = norm L v := by
  intro v
  let x : Fin n → ℤ := fun i => (v i).val
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) 2 2
  let Y : Fin n → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := n) 2 2 X.1
  let q : localDualQuotientTarget D := quotientBasisFamilyMap D Y x
  let y : Fin n → ℤ := Quotient.out q
  have hq : quotientBasisFamilyMap D Y x = D.mkQ y := by
    change q = D.mkQ y
    exact (Submodule.Quotient.mk_out q).symm
  have hquad :
      (L.quadForm y : ZMod (primePowModulus 2 3 : ℕ)) =
        (L.quadForm x : ZMod (primePowModulus 2 3 : ℕ)) :=
    (mem_localDualQuotientSolutionFamilies_iff.mp X.2) x y hq
  have hxv : (fun i : Fin n => (x i : ZMod 4)) = v := by
    funext i
    dsimp [x]
    exact ZMod.natCast_zmod_val (v i)
  have hvec :
      (fun i : Fin n => (y i : ZMod (primePowModulus 2 2 : ℕ))) = X.1.mulVec v := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := n) 2 2 Y x
    have hqcoord :
        primePowQuotientVector (n := n) 2 2 (quotientBasisFamilyMap D Y x) =
          fun i : Fin n => (y i : ZMod (primePowModulus 2 2 : ℕ)) := by
      rw [hq]
      exact primePowQuotientVector_mkQ (n := n) 2 2 y
    have hm : localDualQuotientFamilyMatrix (n := n) 2 2 Y = X.1 :=
      localDualQuotientFamilyMatrix_liftFamily (n := n) 2 2 X.1
    calc
      (fun i : Fin n => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
          (localDualQuotientFamilyMatrix (n := n) 2 2 Y).mulVec
            (fun j : Fin n => (x j : ZMod (primePowModulus 2 2 : ℕ))) :=
        (hmat.trans hqcoord).symm
      _ = X.1.mulVec v := by
        rw [hm]
        change X.1.mulVec (fun j : Fin n => (x j : ZMod 4)) = X.1.mulVec v
        rw [hxv]
  calc
    norm L (X.1.mulVec v) = norm L (fun i => (y i : ZMod 4)) :=
      congrArg (norm L) hvec.symm
    _ = (L.quadForm y : ZMod 8) := norm_intCast L y
    _ = (L.quadForm x : ZMod 8) := by simpa [primePowModulus] using hquad
    _ = norm L (fun i => (x i : ZMod 4)) := (norm_intCast L x).symm
    _ = norm L v := by rw [hxv]

/-- Converse to the generic native matrix adapter. -/
theorem normIsometry_native_mem (L : PositiveDefiniteIntegralLattice n) (X : normIsometry L) :
    localDualQuotientLiftFamily (n := n) 2 2 X.1 ∈
      localDualQuotientSolutionFamilies L 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) 2 2
  let Y : Fin n → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := n) 2 2 X.1
  have hvec : (fun i : Fin n => (y i : ZMod 4)) =
      X.1.mulVec (fun j : Fin n => (x j : ZMod 4)) := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := n) 2 2 Y x
    have hq := congrArg (primePowQuotientVector (n := n) 2 2) hxy
    have hm : localDualQuotientFamilyMatrix (n := n) 2 2 Y = X.1 :=
      localDualQuotientFamilyMatrix_liftFamily (n := n) 2 2 X.1
    exact (primePowQuotientVector_mkQ (n := n) 2 2 y).symm.trans
      (hq.symm.trans (hmat.symm.trans
        (congrArg (fun M : Matrix (Fin n) (Fin n) (ZMod 4) =>
          M.mulVec (fun j : Fin n => (x j : ZMod 4))) hm)))
  change (L.quadForm y : ZMod 8) = (L.quadForm x : ZMod 8)
  exact (norm_intCast L y).symm.trans
    ((congrArg (norm L) hvec).trans ((X.2 _).trans (norm_intCast L x)))

/-- Actual finite types, not simply an equality of proposed counting formulas. -/
def nativeMatrixEquivNorm (L : PositiveDefiniteIntegralLattice n) : nativeMatrix L ≃ normIsometry L where
  toFun X := ⟨X.1, nativeMatrix_preserves L X⟩
  invFun X := ⟨X.1, normIsometry_native_mem L X⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl

abbrev nativeFamily (L : PositiveDefiniteIntegralLattice n) :=
  {Y : Fin n → localDualQuotientTarget (primePowCoordinateSubmodule (n := n) 2 2) //
    Y ∈ localDualQuotientSolutionFamilies L 2 3
      (primePowCoordinateSubmodule (n := n) 2 2)
      (primePowCoordinateSubmodule_rank (n := n) 2 2)}

def nativeMatrixEquivFamily (L : PositiveDefiniteIntegralLattice n) : nativeMatrix L ≃ nativeFamily L where
  toFun X := ⟨localDualQuotientLiftFamily (n := n) 2 2 X.1, X.2⟩
  invFun Y := ⟨localDualQuotientFamilyMatrix (n := n) 2 2 Y.1, by
    rw [localDualQuotientLiftFamily_familyMatrix]
    simp⟩
  left_inv X := by
    apply Subtype.ext
    exact localDualQuotientFamilyMatrix_liftFamily (n := n) 2 2 X.1
  right_inv Y := by
    apply Subtype.ext
    exact localDualQuotientLiftFamily_familyMatrix (n := n) 2 2 Y.1

lemma nativeFamily_natCard (L : PositiveDefiniteIntegralLattice n) :
    Nat.card (nativeFamily L) =
      coordinateLocalDualQuotientCount L 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) := by
  unfold nativeFamily coordinateLocalDualQuotientCount
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- General native count adapter. Classical unimodularity, not Type II, is the input. -/
theorem normIsometry_natCard_eq_native (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) :
    Nat.card (normIsometry L) = associatedBilinearDualQuotientCount L 2 3 := by
  rw [associatedBilinearDualQuotientCount_two_three_eq_primePowCoordinateSubmodule
    (n := n) (L := L) hL]
  rw [← nativeFamily_natCard L]
  exact Nat.card_congr ((nativeMatrixEquivNorm L).symm.trans (nativeMatrixEquivFamily L))

/-- A mod-four quadratic equivalence gives equality of the existing native counts. -/
theorem native_count_eq_of_finite_norm_equiv
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (U V : Matrix (Fin n) (Fin n) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x, norm M (U.mulVec x) = norm L x) :
    associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3 := by
  rw [← normIsometry_natCard_eq_native L hL, ← normIsometry_natCard_eq_native M hM]
  exact Nat.card_congr (StableIdentityFixedLine.isometryCongr (norm L) (norm M) U V hUV hVU hQ)

/-- A finite mod-eight Gram congruence with a mod-eight inverse certificate gives
equality of the existing native counts. -/
theorem native_count_eq_of_zmodEight_congruence
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (U V : Matrix (Fin n) (Fin n) (ZMod 8))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : U.transpose * M.pairingMatrix.map (Int.cast : ℤ → ZMod 8) * U =
      L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) :
    associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3 :=
  native_count_eq_of_finite_norm_equiv L M hL hM
    (zmodEightMatrixModFour U) (zmodEightMatrixModFour V)
    (zmodEightMatrixModFour_mul_inverse_of_mul_inverse U V hUV)
    (zmodEightMatrixModFour_mul_inverse_of_mul_inverse V U hVU)
    (norm_zmodEightMatrixModFour_mulVec_eq_of_congruence L M U hQ)

/-- A packaged finite mod-eight Gram-congruence certificate gives equality of
the existing native counts.  The certificate direction is from the `M` Gram
matrix to the `L` Gram matrix, matching the conjugation convention
`Uᵀ * G_M * U = G_L`. -/
theorem native_count_eq_of_gram_certificate
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))) :
    associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3 :=
  native_count_eq_of_zmodEight_congruence L M hL hM C.changeMatrix C.inverseMatrix
    C.mul_inverse C.inverse_mul C.congruence

/-- If two unimodular lattices have finite mod-eight certificates to a common target,
their existing native dyadic counts are equal.  This is the interface needed by
the normal-form route: it only has to produce certificates from each form to the
same split target. -/
theorem native_count_eq_of_common_target_certificate
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    {target : Matrix (Fin n) (Fin n) (ZMod 8)}
    (CL : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target)
    (CM : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target) :
    associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3 :=
  native_count_eq_of_gram_certificate L M hL hM (CM.trans CL.symm)

/-- Equal native counts at the fixed Hensel depth have the same normalization. -/
theorem localFactor_eq_of_native_count
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (hC : associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3) :
    L.massLocalFactor 2 = M.massLocalFactor 2 := by
  rw [massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_valuationFactor_of_isUnimodular hL,
    massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_valuationFactor_of_isUnimodular hM,
    hC]

/-- Common-target finite certificates transport the dyadic local factor through
the existing native-count normalization. -/
theorem localFactor_eq_of_common_target_certificate
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    {target : Matrix (Fin n) (Fin n) (ZMod 8)}
    (CL : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target)
    (CM : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target) :
    L.massLocalFactor 2 = M.massLocalFactor 2 :=
  localFactor_eq_of_native_count L M hL hM
    (native_count_eq_of_common_target_certificate L M hL hM CL CM)

/-- A packaged finite mod-eight Gram-congruence certificate transports the
dyadic local factor through the existing native-count normalization. -/
theorem localFactor_eq_of_gram_certificate
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))) :
    L.massLocalFactor 2 = M.massLocalFactor 2 :=
  localFactor_eq_of_native_count L M hL hM
    (native_count_eq_of_gram_certificate L M hL hM C)

/-- No same-genus hypothesis is needed to compare these two masses. -/
theorem mass_eq_of_native_count_evenHalf
    {m : ℕ} (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice (2 * m)) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (hC : associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3) :
    L.ordinaryGenusMass = M.ordinaryGenusMass := by
  have hfactor := localFactor_eq_of_native_count L M hL hM hC
  have hprefix : massPartialPrimeInverseProduct L 2 =
      massPartialPrimeInverseProduct M 2 := by
    rw [massPartialPrimeInverseProduct_two,
      massPartialPrimeInverseProduct_two, hfactor]
  have h1 := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic hm heven L hL
  have h2 := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic hm heven M hM
  rw [hprefix] at h1
  have hden : (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) ≠ 0 :=
    ne_of_gt (typeIEvenRankSignDen_pos m hm)
  have hreal : (L.ordinaryGenusMass : ℝ) = (M.ordinaryGenusMass : ℝ) :=
    mul_left_cancel₀ hden (h1.trans h2.symm)
  exact Rat.cast_injective hreal

/-- The even-half ordinary masses agree along a supplied quadratic equivalence of the norms
modulo four.  The equivalence is a hypothesis.  For Type II in rank `8*k` it has a
mathematical construction from the finite certificates, which is not formalized in this
module. -/
theorem mass_eq_of_finite_norm_equiv_evenHalf
    {m : ℕ} (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice (2 * m)) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (U V : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x, norm M (U.mulVec x) = norm L x) :
    L.ordinaryGenusMass = M.ordinaryGenusMass :=
  mass_eq_of_native_count_evenHalf hm heven L M hL hM
    (native_count_eq_of_finite_norm_equiv L M hL hM U V hUV hVU hQ)

/-- A finite mod-eight Gram congruence with an inverse certificate transports
the even-half ordinary masses through the existing native-count adapter. -/
theorem mass_eq_of_zmodEight_congruence_evenHalf
    {m : ℕ} (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice (2 * m)) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (U V : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 8))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : U.transpose * M.pairingMatrix.map (Int.cast : ℤ → ZMod 8) * U =
      L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) :
    L.ordinaryGenusMass = M.ordinaryGenusMass :=
  mass_eq_of_native_count_evenHalf hm heven L M hL hM
    (native_count_eq_of_zmodEight_congruence L M hL hM U V hUV hVU hQ)

/-- Common-target finite certificates transport the even-half ordinary masses
through the existing native-count adapter. -/
theorem mass_eq_of_common_target_certificate_evenHalf
    {m : ℕ} (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice (2 * m)) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    {target : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 8)}
    (CL : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target)
    (CM : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target) :
    L.ordinaryGenusMass = M.ordinaryGenusMass :=
  mass_eq_of_native_count_evenHalf hm heven L M hL hM
    (native_count_eq_of_common_target_certificate L M hL hM CL CM)

/-- Native-count mass transport with the rank given by an equation.  This lets callers
state the rank in a natural form such as `8*k` while reusing the even-half
result at rank `2*m`. -/
theorem mass_eq_of_native_count_evenHalf_of_rank_eq
    {n m : ℕ} (hn : n = 2 * m) (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (hC : associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount M 2 3) :
    L.ordinaryGenusMass = M.ordinaryGenusMass := by
  subst n
  exact mass_eq_of_native_count_evenHalf hm heven L M hL hM hC

/-- Common-target finite-certificate mass transport with the rank given by an equation. -/
theorem mass_eq_of_common_target_certificate_evenHalf_of_rank_eq
    {n m : ℕ} (hn : n = 2 * m) (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    {target : Matrix (Fin n) (Fin n) (ZMod 8)}
    (CL : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target)
    (CM : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8)) target) :
    L.ordinaryGenusMass = M.ordinaryGenusMass := by
  subst n
  exact mass_eq_of_common_target_certificate_evenHalf hm heven L M hL hM CL CM

/-- A packaged finite mod-eight Gram-congruence certificate transports the
even-half ordinary masses. -/
theorem mass_eq_of_gram_certificate_evenHalf
    {m : ℕ} (hm : 1 < m) (heven : Even m)
    (L M : PositiveDefiniteIntegralLattice (2 * m)) (hL : L.IsUnimodular) (hM : M.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (M.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))) :
    L.ordinaryGenusMass = M.ordinaryGenusMass :=
  mass_eq_of_native_count_evenHalf hm heven L M hL hM
    (native_count_eq_of_gram_certificate L M hL hM C)

end TypeIIModEightNativeTransport

#assert_standard_axioms TypeIIModEightNativeTransport.norm_intCast
#assert_standard_axioms TypeIIModEightNativeTransport.intMatrix_mulVec_intCast_zmod
#assert_standard_axioms TypeIIModEightNativeTransport.zmodQuadForm_conj_of_mod_congruence
#assert_standard_axioms TypeIIModEightNativeTransport.norm_intMatrixModFour_mulVec_eq_of_modEight_congruence
#assert_standard_axioms TypeIIModEightNativeTransport.zmodEightToFour_val
#assert_standard_axioms TypeIIModEightNativeTransport.intMatrixModEight_zmodEightMatrixIntLift
#assert_standard_axioms TypeIIModEightNativeTransport.intMatrixModFour_zmodEightMatrixIntLift
#assert_standard_axioms TypeIIModEightNativeTransport.norm_zmodEightMatrixModFour_mulVec_eq_of_congruence
#assert_standard_axioms TypeIIModEightNativeTransport.zmodEightMatrixModFour_mul_inverse_of_mul_inverse
#assert_standard_axioms TypeIIModEightNativeTransport.nativeMatrixEquivNorm
#assert_standard_axioms TypeIIModEightNativeTransport.normIsometry_natCard_eq_native
#assert_standard_axioms TypeIIModEightNativeTransport.native_count_eq_of_finite_norm_equiv
#assert_standard_axioms TypeIIModEightNativeTransport.native_count_eq_of_zmodEight_congruence
#assert_standard_axioms TypeIIModEightNativeTransport.native_count_eq_of_gram_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.native_count_eq_of_common_target_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.localFactor_eq_of_native_count
#assert_standard_axioms TypeIIModEightNativeTransport.localFactor_eq_of_common_target_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.localFactor_eq_of_gram_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_native_count_evenHalf
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_finite_norm_equiv_evenHalf
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_zmodEight_congruence_evenHalf
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_common_target_certificate_evenHalf
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_native_count_evenHalf_of_rank_eq
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_common_target_certificate_evenHalf_of_rank_eq
#assert_standard_axioms TypeIIModEightNativeTransport.mass_eq_of_gram_certificate_evenHalf
