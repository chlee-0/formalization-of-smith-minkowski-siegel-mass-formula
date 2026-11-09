import SMSFormula.QuadraticOrbitDeterminantComparison
import SMSFormula.SkewAdjointRationalElementaryBasis

/-!
# The rational orbit determinant in the form-adapted elementary bases

The rational orbit determinant `J = ω_B(frame)` is taken in the fixed bases
`Module.finBasis` of the skew-adjoint tangents.  Comparing with the form-adapted elementary
bases `F⁻¹(E_ij − E_ji)` (whose determinants in the fixed bases are the scalars `e_B, e_W`),

`|J| = |e_B| · |det F_W| / |e_W|`.

The lower part of the frame is the embedded fixed lower basis, whose coordinates in the embedded
lower elementary basis have determinant `e_W⁻¹`; the transverse lifts of the coordinate vectors
are `lift(e_j) = Σ_k (F_W)_{kj} F_B⁻¹(E_{k,last} − E_{last,k})`.  The arbitrary reindexings only
change the sign.  Nothing is chosen.
-/

noncomputable section

open Matrix

namespace RationalQuadraticSpaceMatrix

section Generic

variable {n : ℕ}

/-- The inverse of the block matrix `diag(F, a)`. -/
theorem nonisotropicLastBlockMatrix_inv (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    {a : ℚ} (ha : a ≠ 0) :
    (nonisotropicLastBlockMatrix F a)⁻¹ = nonisotropicLastBlockMatrix F⁻¹ a⁻¹ := by
  apply Matrix.inv_eq_right_inv
  have hFu : IsUnit F.det := isUnit_iff_ne_zero.mpr hF
  unfold nonisotropicLastBlockMatrix
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_nonsing_inv F hFu]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv.symm : Fin (n + 1) ≃ Fin n ⊕ Fin 1),
    ← Matrix.fromBlocks_one]
  congr 2
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, ha]

/-- The natural map `StrictUpperPair n ⊕ Fin n → StrictUpperPair (n + 1)`: lower pairs are
cast, and `k` goes to the pair `(k, last)`. -/
def strictUpperPairLastSplit : StrictUpperPair n ⊕ Fin n → StrictUpperPair (n + 1)
  | Sum.inl q => ⟨(q.1.1.castSucc, q.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.mpr q.2⟩
  | Sum.inr k => ⟨(k.castSucc, Fin.last n), Fin.castSucc_lt_last k⟩

theorem strictUpperPairLastSplit_injective :
    Function.Injective (strictUpperPairLastSplit (n := n)) := by
  intro x y h
  rcases x with q | k <;> rcases y with q' | k'
  · have h2 := congrArg (fun p : StrictUpperPair (n + 1) ↦ p.1) h
    simp only [strictUpperPairLastSplit, Prod.mk.injEq, Fin.castSucc_inj] at h2
    exact congrArg Sum.inl (Subtype.ext (Prod.ext h2.1 h2.2))
  · have h2 := congrArg (fun p : StrictUpperPair (n + 1) ↦ p.1.2) h
    simp only [strictUpperPairLastSplit] at h2
    exact absurd h2 (Fin.castSucc_ne_last _)
  · have h2 := congrArg (fun p : StrictUpperPair (n + 1) ↦ p.1.2) h
    simp only [strictUpperPairLastSplit] at h2
    exact absurd h2.symm (Fin.castSucc_ne_last _)
  · have h2 := congrArg (fun p : StrictUpperPair (n + 1) ↦ p.1.1) h
    simp only [strictUpperPairLastSplit, Fin.castSucc_inj] at h2
    exact congrArg Sum.inr h2

/-- The natural bijection `StrictUpperPair n ⊕ Fin n ≃ StrictUpperPair (n + 1)`. -/
def strictUpperPairLastSplitEquiv : StrictUpperPair n ⊕ Fin n ≃ StrictUpperPair (n + 1) :=
  Equiv.ofBijective strictUpperPairLastSplit
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨strictUpperPairLastSplit_injective, by
      rw [Fintype.card_sum, StrictUpperPair.card, StrictUpperPair.card, Fintype.card_fin,
        Nat.choose_succ_succ', Nat.choose_one_right, add_comm]⟩)

@[simp]
theorem strictUpperPairLastSplitEquiv_apply (x : StrictUpperPair n ⊕ Fin n) :
    strictUpperPairLastSplitEquiv x = strictUpperPairLastSplit x := rfl

/-- Block matrices multiply blockwise. -/
theorem nonisotropicLastBlockMatrix_mul (G X : Matrix (Fin n) (Fin n) ℚ) (c d : ℚ) :
    nonisotropicLastBlockMatrix G c * nonisotropicLastBlockMatrix X d =
      nonisotropicLastBlockMatrix (G * X) (c * d) := by
  unfold nonisotropicLastBlockMatrix
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 2
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply]

theorem single_castSucc_castSucc_eq_zeroLastBlockMatrix (i j : Fin n) :
    (Matrix.single i.castSucc j.castSucc (1 : ℚ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) =
      zeroLastBlockMatrix (Matrix.single i j 1) := by
  ext r c
  cases r using Fin.lastCases with
  | last =>
      cases c using Fin.lastCases with
      | last => simp
      | cast c => simp
  | cast r =>
      cases c using Fin.lastCases with
      | last => simp
      | cast c => simp [Matrix.single_apply]

theorem mul_single_one_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ) (i j r c : Fin m) :
    (M * Matrix.single i j (1 : ℚ)) r c = if c = j then M r i else 0 := by
  by_cases hc : c = j
  · subst hc; simp
  · rw [if_neg hc]
    simp [Matrix.mul_apply, Ne.symm hc]

theorem coe_skewAdjoint_finset_sum {m : ℕ} {ι : Type*} (F : Matrix (Fin m) (Fin m) ℚ)
    (s : Finset ι) (f : ι → skewAdjointMatricesLieSubalgebra F) :
    ((∑ i ∈ s, f i : skewAdjointMatricesLieSubalgebra F) : Matrix (Fin m) (Fin m) ℚ) =
      ∑ i ∈ s, (f i : Matrix (Fin m) (Fin m) ℚ) :=
  map_sum ((skewAdjointMatricesLieSubalgebra F).incl.toLinearMap) f s

theorem coe_skewAdjoint_add {m : ℕ} (F : Matrix (Fin m) (Fin m) ℚ)
    (X Y : skewAdjointMatricesLieSubalgebra F) :
    ((X + Y : skewAdjointMatricesLieSubalgebra F) : Matrix (Fin m) (Fin m) ℚ) =
      (X : Matrix (Fin m) (Fin m) ℚ) + (Y : Matrix (Fin m) (Fin m) ℚ) := rfl

theorem coe_skewAdjoint_smul {m : ℕ} (F : Matrix (Fin m) (Fin m) ℚ) (c : ℚ)
    (X : skewAdjointMatricesLieSubalgebra F) :
    ((c • X : skewAdjointMatricesLieSubalgebra F) : Matrix (Fin m) (Fin m) ℚ) =
      c • (X : Matrix (Fin m) (Fin m) ℚ) := rfl

/-- A basis determinant from explicit coordinates. -/
theorem _root_.Module.Basis.det_eq_det_of_eq_sum {ι R M : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [AddCommGroup M] [Module R M] (b : Module.Basis ι R M) (N : Matrix ι ι R)
    (v : ι → M) (hv : ∀ c, v c = ∑ c', N c' c • b c') : b.det v = N.det := by
  rw [Module.Basis.det_apply]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply, hv, b.repr_sum_self]

/-- Basis change plus a permutation: `|b.det (v ∘ idx)| = |b.det (e.reindex ε)| · |det N|` when
`v ∘ φ` has coordinate matrix `N` in `e`. -/
theorem _root_.Module.Basis.abs_det_eq_of_coordinates {ι κ ι' M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [AddCommGroup M] [Module ℚ M]
    (b : Module.Basis ι ℚ M) (e : Module.Basis κ ℚ M) (ε : κ ≃ ι) (v : ι' → M) (idx : ι ≃ ι')
    (φ : κ ≃ ι') (N : Matrix κ κ ℚ) (hv : ∀ c, v (φ c) = ∑ c', N c' c • e c') :
    |b.det (v ∘ idx)| = |b.det (e.reindex ε)| * |N.det| := by
  have hbasis := AlternatingMap.eq_smul_basis_det (e.reindex ε) b.det
  have h1 : b.det (v ∘ idx) = b.det (e.reindex ε) * (e.reindex ε).det (v ∘ idx) := by
    conv_lhs => rw [hbasis]
    rfl
  set σ : Equiv.Perm κ := (ε.trans idx).trans φ.symm
  have h2 : v ∘ idx ∘ ε = (v ∘ φ) ∘ σ := by
    funext q; simp [σ]
  have h3 := e.det.map_perm (v ∘ φ) σ
  have h4 := e.det_eq_det_of_eq_sum N (v ∘ φ) hv
  rw [h1, Module.Basis.det_reindex, Function.comp_assoc, h2, h3, h4, abs_mul]
  congr 1
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end Generic

section Elementary

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

theorem nonisotropicLastExtension_pairingMatrix_inv :
    (W.nonisotropicLastExtension a ha).pairingMatrix⁻¹ =
      nonisotropicLastBlockMatrix W.pairingMatrix⁻¹ a⁻¹ :=
  nonisotropicLastBlockMatrix_inv _ W.form_det_ne_zero ha

/-- The block elementary vector of a lower pair is the embedded lower elementary vector. -/
theorem coe_skewAdjointFormElementaryRationalBasis_lastSplit_inl (q : StrictUpperPair n) :
    ((skewAdjointFormElementaryRationalBasis (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_symm
        (W.nonisotropicLastExtension a ha).form_det_ne_zero
        (strictUpperPairLastSplit (Sum.inl q)) :
        skewAdjointMatricesLieSubalgebra (W.nonisotropicLastExtension a ha).pairingMatrix) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) =
      zeroLastBlockMatrix ((skewAdjointFormElementaryRationalBasis W.pairingMatrix W.form_symm
        W.form_det_ne_zero q : skewAdjointMatricesLieSubalgebra W.pairingMatrix) :
          Matrix (Fin n) (Fin n) ℚ) := by
  rw [coe_skewAdjointFormElementaryRationalBasis_apply,
    coe_skewAdjointFormElementaryRationalBasis_apply, nonisotropicLastExtension_pairingMatrix_inv]
  simp only [strictUpperPairLastSplit]
  rw [single_castSucc_castSucc_eq_zeroLastBlockMatrix,
    single_castSucc_castSucc_eq_zeroLastBlockMatrix]
  unfold zeroLastBlockMatrix
  rw [show nonisotropicLastBlockMatrix (Matrix.single q.1.1 q.1.2 (1 : ℚ)) 0 -
      nonisotropicLastBlockMatrix (Matrix.single q.1.2 q.1.1 1) 0 =
      nonisotropicLastBlockMatrix (Matrix.single q.1.1 q.1.2 1 - Matrix.single q.1.2 q.1.1 1) 0 by
    ext r c
    cases r using Fin.lastCases <;> cases c using Fin.lastCases <;> simp,
    nonisotropicLastBlockMatrix_mul, mul_zero]

/-- The transverse lift of a coordinate vector in block elementary vectors:
`lift(e_j) = Σ_k (F_W)_{kj} · F_B⁻¹ (E_{k,last} − E_{last,k})`. -/
theorem coe_lastOrbitLift_basisFun_eq_sum (j : Fin n) :
    ((W.lastOrbitLift a ha ℚ (Pi.basisFun ℚ (Fin n) j)).1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) =
      ∑ k : Fin n, W.pairingMatrix k j • ((W.nonisotropicLastExtension a ha).pairingMatrix⁻¹ *
        (Matrix.single k.castSucc (Fin.last n) (1 : ℚ) - Matrix.single (Fin.last n) k.castSucc 1)) := by
  have hFB : (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ =
      nonisotropicLastBlockMatrix W.pairingMatrix a := by
    ext r c; simp [specialOrthogonalMappedFormMatrix]
  change Matrix.nonisotropicOrbitTangentLift
    ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ) lastCoordinateVector
    (Fin.snoc (Pi.basisFun ℚ (Fin n) j) 0) = _
  rw [hFB, nonisotropicLastExtension_pairingMatrix_inv]
  have hu : IsUnit W.pairingMatrix.det := isUnit_iff_ne_zero.mpr W.form_det_ne_zero
  have hGG : W.pairingMatrix⁻¹ * W.pairingMatrix = 1 := Matrix.nonsing_inv_mul _ hu
  set G := W.pairingMatrix
  have hx : (nonisotropicLastBlockMatrix G a) *ᵥ (lastCoordinateVector : Fin (n + 1) → ℚ) =
      fun r ↦ Fin.lastCases a (fun _ ↦ 0) r := by
    funext r
    cases r using Fin.lastCases <;> simp [Matrix.mulVec, dotProduct, lastCoordinateVector,
      Pi.single_apply]
  have hxx : dotProduct (lastCoordinateVector : Fin (n + 1) → ℚ)
      ((nonisotropicLastBlockMatrix G a) *ᵥ lastCoordinateVector) = a := by
    rw [hx]; simp [dotProduct, lastCoordinateVector, Pi.single_apply]
  have hy : (nonisotropicLastBlockMatrix G a) *ᵥ
      (Fin.snoc (Pi.basisFun ℚ (Fin n) j) 0 : Fin (n + 1) → ℚ) =
      fun r ↦ Fin.lastCases 0 (fun r' ↦ G r' j) r := by
    funext r
    cases r using Fin.lastCases <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
      Pi.single_apply]
  unfold Matrix.nonisotropicOrbitTangentLift
  rw [hxx, hx, hy]
  ext r c
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.sum_apply, Matrix.mul_sub, mul_single_one_apply]
  have hl : ∀ x : Fin n, (Fin.last n = x.castSucc) ↔ False :=
    fun x ↦ iff_false_intro (Fin.castSucc_ne_last x).symm
  cases r using Fin.lastCases with
  | last =>
      cases c using Fin.lastCases with
      | last => simp [lastCoordinateVector, hl]
      | cast c =>
          simp [lastCoordinateVector, Fin.castSucc_inj]
          ring
  | cast r =>
      cases c using Fin.lastCases with
      | last =>
          have hsum : ∑ k : Fin n, G k j * G⁻¹ r k = if r = j then 1 else 0 := by
            have := congrFun (congrFun hGG r) j
            rw [Matrix.mul_apply, Matrix.one_apply] at this
            rw [← this]; exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
          simp [lastCoordinateVector, hl, hsum, Pi.single_apply]
          split_ifs <;> field_simp
      | cast c =>
          simp [lastCoordinateVector, Pi.single_apply, Fin.castSucc_ne_last]

/-- The coordinate matrix of the lower-first frame in the block elementary basis. -/
def lastOrbitElementaryCoordinateMatrix :
    Matrix (StrictUpperPair (n + 1)) (StrictUpperPair (n + 1)) ℚ :=
  (Matrix.fromBlocks
      (fun q' q ↦ (skewAdjointFormElementaryRationalBasis W.pairingMatrix W.form_symm
        W.form_det_ne_zero).repr (skewAdjointFinBasis W.pairingMatrix
          (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q)) q')
      0 0 W.pairingMatrix).submatrix strictUpperPairLastSplitEquiv.symm
    strictUpperPairLastSplitEquiv.symm

/-- The natural index map from strict upper pairs of the block to the frame index. -/
def lastOrbitNaturalIndexEquiv :
    StrictUpperPair (n + 1) ≃ Fin (Module.finrank ℚ W.skewAdjointTangent) ⊕ Fin n :=
  strictUpperPairLastSplitEquiv.symm.trans
    (Equiv.sumCongr (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm
      W.form_det_ne_zero) (Equiv.refl _))

/-- The frame in the natural index order has the block coordinate matrix. -/
theorem lastOrbitFrame_naturalIndex_eq_sum (c : StrictUpperPair (n + 1)) :
    (W.lastOrbitFrame a ha ℚ (W.lastOrbitNaturalIndexEquiv c) :
        skewAdjointMatricesLieSubalgebra (W.nonisotropicLastExtension a ha).pairingMatrix) =
      ∑ c', W.lastOrbitElementaryCoordinateMatrix c' c •
        skewAdjointFormElementaryRationalBasis (W.nonisotropicLastExtension a ha).pairingMatrix
          (W.nonisotropicLastExtension a ha).form_symm
          (W.nonisotropicLastExtension a ha).form_det_ne_zero c' := by
  obtain ⟨y, rfl⟩ := strictUpperPairLastSplitEquiv.surjective c
  rw [← Equiv.sum_comp strictUpperPairLastSplitEquiv, Fintype.sum_sum_type]
  apply Subtype.ext
  rw [coe_skewAdjoint_add, coe_skewAdjoint_finset_sum, coe_skewAdjoint_finset_sum]
  simp only [coe_skewAdjoint_smul, lastOrbitElementaryCoordinateMatrix,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, lastOrbitNaturalIndexEquiv, Equiv.trans_apply]
  rcases y with q | j
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, lastOrbitFrame_inl,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, strictUpperPairLastSplitEquiv_apply]
    change zeroLastBlockMatrix (skewAdjointScalarExtensionFinBasis (K := ℚ) W.pairingMatrix _).1 = _
    simp only [skewAdjointScalarExtensionFinBasis]
    rw [coe_skewAdjointScalarExtensionBasis_apply]
    simp only [coe_skewAdjointFormElementaryRationalBasis_lastSplit_inl]
    rw [show (skewAdjointFinBasis W.pairingMatrix
        (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q) :
          Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℚ) =
        (skewAdjointFinBasis W.pairingMatrix
          (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q) :
            Matrix (Fin n) (Fin n) ℚ) by ext; simp]
    conv_lhs => rw [← (skewAdjointFormElementaryRationalBasis W.pairingMatrix W.form_symm
      W.form_det_ne_zero).sum_repr (skewAdjointFinBasis W.pairingMatrix
        (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q))]
    rw [coe_skewAdjoint_finset_sum]
    simp only [coe_skewAdjoint_smul]
    exact map_sum (zeroLastBlockMatrixLinearMap (R := ℚ) (n := n)) _ _ |>.trans
      (Finset.sum_congr rfl fun q' _ ↦ (zeroLastBlockMatrixLinearMap (R := ℚ) (n := n)).map_smul _ _)
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, lastOrbitFrame_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add, strictUpperPairLastSplitEquiv_apply]
    rw [coe_lastOrbitLift_basisFun_eq_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [coe_skewAdjointFormElementaryRationalBasis_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The rational orbit determinant in elementary bases: `|J| = |e_B| · |det F_W| / |e_W|`. -/
theorem abs_lastOrbitDeterminant_eq :
    |W.lastOrbitDeterminant a ha ℚ| =
      |Matrix.skewAdjointFixedFormElementaryDetScalar (W.nonisotropicLastExtension a ha).pairingMatrix
          (W.nonisotropicLastExtension a ha).form_symm
          (W.nonisotropicLastExtension a ha).form_det_ne_zero| *
        |W.pairingMatrix.det| /
        |Matrix.skewAdjointFixedFormElementaryDetScalar W.pairingMatrix W.form_symm
          W.form_det_ne_zero| := by
  -- (1) the determinant in the fixed basis
  have hQ := skewAdjointScalarExtensionDetForm_apply (K := ℚ)
    (W.nonisotropicLastExtension a ha).pairingMatrix
    (fun j ↦ W.lastOrbitFrame a ha ℚ (W.lastOrbitIndexEquiv a ha j))
  simp only [← W.lastOrbitFrame_scalarExtension a ha ℚ] at hQ
  have hJ : W.lastOrbitDeterminant a ha ℚ =
      (skewAdjointFinBasis (W.nonisotropicLastExtension a ha).pairingMatrix).det
        (fun j ↦ (W.lastOrbitFrame a ha ℚ (W.lastOrbitIndexEquiv a ha j) :
          skewAdjointMatricesLieSubalgebra (W.nonisotropicLastExtension a ha).pairingMatrix)) := by
    unfold lastOrbitDeterminant lastOrbitGroupForm
    rw [AlternatingMap.domDomCongr_apply]
    exact hQ.trans (by simp; rfl)
  have hN := Module.Basis.abs_det_eq_of_coordinates
    (skewAdjointFinBasis (W.nonisotropicLastExtension a ha).pairingMatrix)
    (skewAdjointFormElementaryRationalBasis (W.nonisotropicLastExtension a ha).pairingMatrix
      (W.nonisotropicLastExtension a ha).form_symm
      (W.nonisotropicLastExtension a ha).form_det_ne_zero)
    (skewAdjointFormElementaryIndexEquiv (W.nonisotropicLastExtension a ha).pairingMatrix
      (W.nonisotropicLastExtension a ha).form_symm
      (W.nonisotropicLastExtension a ha).form_det_ne_zero)
    (fun i ↦ (W.lastOrbitFrame a ha ℚ i :
      skewAdjointMatricesLieSubalgebra (W.nonisotropicLastExtension a ha).pairingMatrix))
    (W.lastOrbitIndexEquiv a ha) W.lastOrbitNaturalIndexEquiv
    W.lastOrbitElementaryCoordinateMatrix (W.lastOrbitFrame_naturalIndex_eq_sum a ha)
  have h5 : W.lastOrbitElementaryCoordinateMatrix.det =
      ((skewAdjointFormElementaryRationalBasis W.pairingMatrix W.form_symm W.form_det_ne_zero).toMatrix
        (fun q ↦ skewAdjointFinBasis W.pairingMatrix
          (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q))).det *
        W.pairingMatrix.det := by
    unfold lastOrbitElementaryCoordinateMatrix
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    rfl
  have h6 : ((skewAdjointFormElementaryRationalBasis W.pairingMatrix W.form_symm
        W.form_det_ne_zero).toMatrix
        (fun q ↦ skewAdjointFinBasis W.pairingMatrix
          (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q))).det =
      (Matrix.skewAdjointFixedFormElementaryDetScalar W.pairingMatrix W.form_symm
        W.form_det_ne_zero)⁻¹ := by
    rw [← Module.Basis.det_apply]
    have hr : (skewAdjointFormElementaryRationalBasis W.pairingMatrix W.form_symm
          W.form_det_ne_zero).det (fun q ↦ skewAdjointFinBasis W.pairingMatrix
            (skewAdjointFormElementaryIndexEquiv W.pairingMatrix W.form_symm W.form_det_ne_zero q)) =
        (skewAdjointFormElementaryRationalFinBasis W.pairingMatrix W.form_symm
          W.form_det_ne_zero).det (skewAdjointFinBasis W.pairingMatrix) :=
      (Module.Basis.det_reindex _ _ _).symm
    rw [hr]
    have hm := Module.Basis.det_mul_det (skewAdjointFinBasis W.pairingMatrix)
      (skewAdjointFormElementaryRationalFinBasis W.pairingMatrix W.form_symm W.form_det_ne_zero)
      (skewAdjointFinBasis W.pairingMatrix)
    rw [Module.Basis.det_self] at hm
    exact eq_inv_of_mul_eq_one_right hm
  rw [hJ]
  have hJ' : (skewAdjointFinBasis (W.nonisotropicLastExtension a ha).pairingMatrix).det
      (fun j ↦ (W.lastOrbitFrame a ha ℚ (W.lastOrbitIndexEquiv a ha j) :
        skewAdjointMatricesLieSubalgebra (W.nonisotropicLastExtension a ha).pairingMatrix)) =
      (skewAdjointFinBasis (W.nonisotropicLastExtension a ha).pairingMatrix).det
        ((fun i ↦ (W.lastOrbitFrame a ha ℚ i :
          skewAdjointMatricesLieSubalgebra (W.nonisotropicLastExtension a ha).pairingMatrix)) ∘
          W.lastOrbitIndexEquiv a ha) := rfl
  rw [hJ', hN, h5, h6, abs_mul, abs_inv]
  unfold Matrix.skewAdjointFixedFormElementaryDetScalar Matrix.skewAdjointFormElementaryRationalFinBasis
  ring

end Elementary

end RationalQuadraticSpaceMatrix
