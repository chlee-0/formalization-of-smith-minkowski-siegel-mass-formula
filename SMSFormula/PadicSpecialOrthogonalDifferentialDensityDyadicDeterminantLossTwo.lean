import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledCayley
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicFormCoordinateMass
import SMSFormula.PadicSpecialOrthogonalDifferentialSignSeparatedDensityDepth

/-!
# Multiplication by two on the enlarged dyadic determinant-loss carrier

The scaled dyadic Cayley residue is twice the original density residue.  To
keep that factor explicit, this module packages multiplication by two on
the enlarged dyadic determinant-loss carrier `T₂`.  It proves the exact
ambient formula and computes both its kernel and its range.

The kernel is one residue layer, of cardinal `2 ^ d`; the range has cardinal
`2 ^ (v₂(pairingDeterminant) * d)`.  The latter formula includes the endpoint
`v₂(pairingDeterminant) = 0`, where the range is the zero subgroup.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- In `ZMod (2^m)`, for positive `m`, an element is killed by two exactly
when its residue one level lower is zero. -/
theorem zmod_two_nsmul_eq_zero_iff_castHom_pred_eq_zero
    (m : ℕ) (hm : 1 ≤ m) (a : ZMod (2 ^ m)) :
    2 • a = 0 ↔
      ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
        (ZMod (2 ^ (m - 1))) a = 0 := by
  symm
  obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  subst m
  simp only [Nat.succ_sub_one]
  change (ZMod.cast a : ZMod (2 ^ r)) = 0 ↔ 2 • a = 0
  rw [ZMod.cast_eq_val]
  have hleft : (a.val : ZMod (2 ^ r)) = 0 ↔ 2 ^ r ∣ a.val :=
    ZMod.natCast_eq_zero_iff _ _
  have hright : 2 • a = 0 ↔ 2 ^ (r + 1) ∣ a.val + a.val := by
    calc
      2 • a = 0 ↔
          ((a.val + a.val : ℕ) : ZMod (2 ^ (r + 1))) = 0 := by
        rw [two_nsmul, Nat.cast_add, a.natCast_zmod_val]
      _ ↔ 2 ^ (r + 1) ∣ a.val + a.val :=
        ZMod.natCast_eq_zero_iff _ _
  rw [hleft, hright]
  simpa only [pow_succ, Nat.mul_comm, two_mul] using
    (Nat.mul_dvd_mul_iff_left (a := 2) (b := 2 ^ r) (c := a.val)
      (by norm_num : 0 < 2)).symm

/-- A two-torsion residue at level `m` restricts to zero at every level at
most `m-1`. -/
theorem zmod_castHom_eq_zero_of_two_nsmul_eq_zero
    (m t : ℕ) (hm : 1 ≤ m) (ht : t ≤ m - 1)
    (a : ZMod (2 ^ m)) (ha : 2 • a = 0) :
    ZMod.castHom (pow_dvd_pow 2 (ht.trans (Nat.sub_le m 1)))
      (ZMod (2 ^ t)) a = 0 := by
  have hstep :
      ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
          (ZMod (2 ^ (m - 1))) a = 0 :=
    (zmod_two_nsmul_eq_zero_iff_castHom_pred_eq_zero m hm a).1 ha
  have hcomp := ZMod.castHom_comp
    (pow_dvd_pow 2 ht)
    (pow_dvd_pow 2 (Nat.sub_le m 1))
  have happ := DFunLike.congr_fun hcomp a
  rw [RingHom.comp_apply, hstep, map_zero] at happ
  exact happ.symm

/-- Restriction of twice a residue to level `k` vanishes exactly when the
original residue restricts to level `k-1`. -/
theorem zmod_castHom_two_nsmul_eq_zero_iff_castHom_pred_eq_zero
    (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (a : ZMod (2 ^ m)) :
    ZMod.castHom (pow_dvd_pow 2 hkm) (ZMod (2 ^ k)) (2 • a) = 0 ↔
      ZMod.castHom
        (pow_dvd_pow 2 ((Nat.sub_le k 1).trans hkm))
        (ZMod (2 ^ (k - 1))) a = 0 := by
  rw [map_nsmul]
  rw [zmod_two_nsmul_eq_zero_iff_castHom_pred_eq_zero k hk]
  have hcomp := ZMod.castHom_comp
    (pow_dvd_pow 2 (Nat.sub_le k 1))
    (pow_dvd_pow 2 hkm)
  have happ := DFunLike.congr_fun hcomp a
  rw [RingHom.comp_apply] at happ
  rw [happ]

/-- A residue that vanishes at a positive level `k` is twice a residue that
vanishes at level `k-1`.  This is the literal one-coordinate division bridge
used to characterize the image on `T₂`. -/
theorem exists_two_nsmul_eq_of_castHom_eq_zero
    (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (a : ZMod (2 ^ m))
    (ha : ZMod.castHom (pow_dvd_pow 2 hkm) (ZMod (2 ^ k)) a = 0) :
    ∃ b : ZMod (2 ^ m), 2 • b = a ∧
      ZMod.castHom
        (pow_dvd_pow 2 ((Nat.sub_le k 1).trans hkm))
        (ZMod (2 ^ (k - 1))) b = 0 := by
  have ha' : (a.val : ZMod (2 ^ k)) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at ha
    exact ha
  have hdvd : 2 ^ k ∣ a.val :=
    (ZMod.natCast_eq_zero_iff _ _).1 ha'
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨r, hr⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  subst k
  simp only [Nat.succ_sub_one] at *
  refine ⟨(2 ^ r * q : ℕ), ?_, ?_⟩
  · rw [two_nsmul, ← a.natCast_zmod_val]
    rw [hq, pow_succ]
    push_cast
    ring
  · change
      ZMod.castHom
          (pow_dvd_pow 2 ((Nat.sub_le (r + 1) 1).trans hkm))
          (ZMod (2 ^ r))
          ((2 ^ r * q : ℕ) : ZMod (2 ^ m)) = 0
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).2 ⟨q, rfl⟩

/-- The kernel of coordinatewise multiplication by two is the product of the
one-coordinate two-torsion kernels. -/
def functionTwoNsmulKernelEquiv
    {ι : Type*} (m : ℕ) :
    (nsmulAddMonoidHom 2 :
        (ι → ZMod (2 ^ m)) →+ (ι → ZMod (2 ^ m))).ker ≃
      (ι →
        (nsmulAddMonoidHom 2 :
          ZMod (2 ^ m) →+ ZMod (2 ^ m)).ker) where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun y := ⟨fun i ↦ (y i).1, funext fun i ↦ (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinatewise two-torsion at a positive dyadic level has one binary
choice in every coordinate. -/
theorem natCard_functionTwoNsmulKernel
    {ι : Type*} [Fintype ι] (m : ℕ) (hm : 1 ≤ m) :
    Nat.card
        (nsmulAddMonoidHom 2 :
          (ι → ZMod (2 ^ m)) →+ (ι → ZMod (2 ^ m))).ker =
      2 ^ Fintype.card ι := by
  have hone : Nat.card
      (nsmulAddMonoidHom 2 :
        ZMod (2 ^ m) →+ ZMod (2 ^ m)).ker = 2 := by
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
    exact Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow 2 hm)
  calc
    Nat.card
        (nsmulAddMonoidHom 2 :
          (ι → ZMod (2 ^ m)) →+ (ι → ZMod (2 ^ m))).ker =
        Nat.card
          (ι →
            (nsmulAddMonoidHom 2 :
              ZMod (2 ^ m) →+ ZMod (2 ^ m)).ker) :=
      Nat.card_congr (functionTwoNsmulKernelEquiv m)
    _ = ∏ _ : ι,
          Nat.card
            (nsmulAddMonoidHom 2 :
              ZMod (2 ^ m) →+ ZMod (2 ^ m)).ker := Nat.card_pi
    _ = ∏ _ : ι, 2 := by rw [hone]
    _ = 2 ^ Fintype.card ι := by simp

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Multiplication by two on the enlarged dyadic determinant-loss carrier. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue →+
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
  nsmulAddMonoidHom 2

/-- The ambient residue of the dyadic multiplication map is twice the original
residue. -/
@[simp]
theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue) :
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo
      x).1 = 2 • x.1 :=
  rfl

/-- An enlarged dyadic determinant-loss residue is in the image of
multiplication by two exactly when its direct residue at the unshifted selected
depth is zero. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoRange_iff_restrictsToZero
    (L : PositiveDefiniteIntegralLattice n)
    (y : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue) :
    y ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.range ↔
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossRestriction
        2 y.1 = 0 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let m :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      2
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hk : 1 ≤ k := by
    dsimp [k]
    exact le_trans (by norm_num) <|
      L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hkm : k ≤ m := by
    dsimp [k, m]
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    omega
  constructor
  · rintro ⟨x, rfl⟩
    funext i
    exact
      (zmod_castHom_two_nsmul_eq_zero_iff_castHom_pred_eq_zero
        m k hk hkm (x.1 i)).2 (congrFun x.2 i)
  · intro hy
    have hycoord : ∀ i,
        ZMod.castHom (pow_dvd_pow 2 hkm) (ZMod (2 ^ k)) (y.1 i) = 0 := by
      intro i
      exact congrFun hy i
    choose x hxmul hxzero using fun i ↦
      exists_two_nsmul_eq_of_castHom_eq_zero
        m k hk hkm (y.1 i) (hycoord i)
    let xT :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
      ⟨x, by
        funext i
        exact hxzero i⟩
    refine ⟨xT, ?_⟩
    apply Subtype.ext
    funext i
    exact hxmul i

/-- The two-torsion kernel inside `T₂` is literally the full coordinatewise
two-torsion kernel at the original residue level.  The defining restriction
condition of `T₂` is automatic because the selected outer depth is at least
one level lower. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoKernelEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.ker ≃
      (nsmulAddMonoidHom 2 :
        skewAdjointFormElementaryPadicCoordinateResidue
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2)
            L.rationalFormMatrix →+
          skewAdjointFormElementaryPadicCoordinateResidue
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2)
            L.rationalFormMatrix).ker where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    exact congrArg Subtype.val x.2
  invFun x := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hm : 1 ≤
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2 := by
      unfold
        localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      have hk :=
        L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
      omega
    have ht :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1 ≤
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 - 1 := by
      unfold
        localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      omega
    let y :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
      ⟨x.1, by
        funext i
        exact zmod_castHom_eq_zero_of_two_nsmul_eq_zero
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
          hm ht (x.1 i) (congrFun x.2 i)⟩
    exact ⟨y, by
      apply Subtype.ext
      exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The multiplication-by-two kernel on `T₂` has exactly one binary residue
layer in every tangent coordinate. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoKernel
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.ker =
      2 ^ Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  rw [Nat.card_congr
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoKernelEquiv]
  have hm : 1 ≤
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2 := by
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    have hk :=
      L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
    omega
  simpa only [Fintype.card_fin] using
    (natCard_functionTwoNsmulKernel
      (ι := Fin
        (Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2) hm)

/-- The range of multiplication by two on `T₂` has exactly the unshifted
determinant-loss cardinality.  For determinant valuation zero this says that
the range is a singleton. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoRange
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.range =
      2 ^
        (padicValInt 2 L.pairingDeterminant *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
  let f :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo
  have hcard := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoKernel,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue]
    at hcard
  have hpow :
      2 ^
          ((padicValInt 2 L.pairingDeterminant + 1) *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) =
        2 ^ Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) *
          2 ^
            (padicValInt 2 L.pairingDeterminant *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
    rw [Nat.add_mul, one_mul, Nat.pow_add]
    ac_rfl
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_left
    (pow_pos (by norm_num : 0 < 2)
      (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))
    hcard

/-- At determinant valuation zero, multiplication by two on `T₂` has only the
zero residue in its range. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoRange_eq_bot_of_pairingDeterminantVal_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (hv : padicValInt 2 L.pairingDeterminant = 0) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.range =
      ⊥ := by
  apply AddSubgroup.eq_bot_of_card_eq
  rw [L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwoRange,
    hv, zero_mul, pow_zero]

end PositiveDefiniteIntegralLattice
