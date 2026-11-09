import SMSFormula.CliffordBlockIdempotentSplitting
import SMSFormula.BlockConjugationCoordinates
import SMSFormula.RationalCliffordSpinBlockIntrinsicStabilizer
import SMSFormula.RationalCliffordSpinBlockCentralizer

/-!
# The diagonal block product map `Spin(T) × Spin(T) → Spin(T ⊥ ⟨f₀f₁f₂⟩)`

Let `T` be the rational ternary space with diagonal Gram matrix `⟨f₀, f₁, f₂⟩` and let
`U = T ⊥ ⟨f₀f₁f₂⟩` be the nonisotropic last extension.  Over every commutative rational
algebra `A`, in the commutative Clifford model, the complement Clifford map `ι : C(T) → C(U)`
and the central idempotents `p± = (1 ± z)/2` (`z = e₀e₁e₂e₃/(f₀f₁f₂)`) give the block map

`Φ(x, y) = ι(x) p₊ + ι(y) p₋`.

Its explicit linear inverse is read off from the block normal form `g = ι(α) + ι(β) e₃`:
`Ψ(g) = (α − βν, α + βν)`, `ν = e₀e₁e₂`.  Nothing is chosen: `Φ` and `Ψ` are canonical.
-/

noncomputable section

open CliffordAlgebra Matrix

namespace RationalQuadraticSpaceMatrix

attribute [local instance] rationalAlgebraInvertibleTwo

/-! ## Diagonal forms in the commutative model -/

section DiagonalForm

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (A : Type*) [CommRing A] [Algebra ℚ A]

theorem commutativeScalarExtensionQuadraticForm_diagonal {w : Fin n → ℚ}
    (hV : V.pairingMatrix = diagonal w) (x : Fin n → A) :
    V.commutativeScalarExtensionQuadraticForm A x = ∑ i, algebraMap ℚ A (w i) * (x i * x i) := by
  change (Matrix.toLinearMap₂' A (V.commutativeScalarExtensionFormMatrix A)) x x = _
  rw [Matrix.toLinearMap₂'_apply', commutativeScalarExtensionFormMatrix, hV,
    diagonal_map (map_zero _)]
  simp only [dotProduct, mulVec_diagonal]
  change (∑ index : Fin n, x index * (algebraMap ℚ A (w index) * x index)) = _
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  ring

theorem commutativeScalarExtensionQuadraticForm_single_of_diagonal {w : Fin n → ℚ}
    (hV : V.pairingMatrix = diagonal w) (i : Fin n) :
    V.commutativeScalarExtensionQuadraticForm A (Pi.single i 1) = algebraMap ℚ A (w i) := by
  rw [V.commutativeScalarExtensionQuadraticForm_diagonal A hV]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

theorem commutativeScalarExtensionQuadraticForm_isOrtho_of_diagonal {w : Fin n → ℚ}
    (hV : V.pairingMatrix = diagonal w) {i j : Fin n} (hij : i ≠ j) :
    (V.commutativeScalarExtensionQuadraticForm A).IsOrtho (Pi.single i 1) (Pi.single j 1) := by
  rw [QuadraticMap.isOrtho_def, V.commutativeScalarExtensionQuadraticForm_diagonal A hV,
    V.commutativeScalarExtensionQuadraticForm_diagonal A hV,
    V.commutativeScalarExtensionQuadraticForm_diagonal A hV, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
    · simp [hki, hkj]

theorem single_mem_span_range (m : Fin n → A) :
    m ∈ Submodule.span A (Set.range fun i : Fin n ↦ (Pi.single i 1 : Fin n → A)) := by
  rw [show m = ∑ i, m i • (Pi.single i 1 : Fin n → A) from
    (commutativeScalarExtension_single_sum A m).symm]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end DiagonalForm

/-! ## General Clifford facts -/

theorem _root_.CliffordAlgebra.algebraMap_injective_of_invertible_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) [Invertible (2 : R)] :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r s h
  have := congrArg (CliffordAlgebra.equivExterior Q) h
  simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap] at this
  exact (ExteriorAlgebra.algebraMap_leftInverse M).injective this

theorem _root_.CliffordAlgebra.mem_evenOdd_zero_iff_mem_even {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) {x : CliffordAlgebra Q} :
    x ∈ evenOdd Q 0 ↔ x ∈ even Q := by
  rw [← even_toSubmodule, Subalgebra.mem_toSubmodule]

/-- The coordinate vectors `Φ(c)` of the quaternion bookkeeping agree with the Clifford ones. -/
theorem _root_.CliffordAlgebra.BlockSplitting.conjCoords_eq_coordinates {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (v : Fin 4 → M)
    (hD : Q (v 3) = Q (v 0) * Q (v 1) * Q (v 2)) (dinv u0 u1 u2 : R) (h k c : Fin 4 → R) :
    BlockSplitting.conjCoords Q v dinv u0 u1 u2 h k c =
      BlockConjugationCoordinates.conjCoords (Q (v 0)) (Q (v 1)) (Q (v 2)) u0 u1 u2 dinv h k c := by
  have hθ : BlockSplitting.theta Q v c =
      BlockConjugationCoordinates.theta (Q (v 0)) (Q (v 1)) (Q (v 2)) c := by
    unfold BlockSplitting.theta BlockConjugationCoordinates.theta
    rw [hD]
  unfold BlockSplitting.conjCoords BlockConjugationCoordinates.conjCoords
  rw [hθ]
  rfl

/-! ## The block data -/

/-- The standard coordinate vectors. -/
abbrev stdVec (n : ℕ) (A : Type*) [CommRing A] : Fin n → Fin n → A := fun i ↦ Pi.single i 1

/-- The weights `⟨f₀, f₁, f₂, f₀f₁f₂⟩` of the block form. -/
def diagonalBlockWeights (f : Fin 3 → ℚ) : Fin 4 → ℚ := ![f 0, f 1, f 2, f 0 * f 1 * f 2]

/-- The scalar `d = (f₀f₁f₂)⁻¹` of the normalized volume element. -/
def diagonalBlockScalar (f : Fin 3 → ℚ) (A : Type*) [CommRing A] [Algebra ℚ A] : A :=
  algebraMap ℚ A (f 0 * f 1 * f 2)⁻¹

/-- The special-orthogonal matrix of `Φ(h, k)` in quaternion coordinates. -/
def diagonalBlockConjMatrix (f : Fin 3 → ℚ) (A : Type*) [CommRing A] [Algebra ℚ A] (h k : Fin 4 → A) :
    Matrix (Fin 4) (Fin 4) A :=
  BlockConjugationCoordinates.conjMatrix (algebraMap ℚ A (f 0)) (algebraMap ℚ A (f 1))
    (algebraMap ℚ A (f 2)) (algebraMap ℚ A (f 0)⁻¹) (algebraMap ℚ A (f 1)⁻¹) (algebraMap ℚ A (f 2)⁻¹)
    (diagonalBlockScalar f A) h k

/-- The quaternion norm in the weights `fᵢ`. -/
abbrev diagonalBlockNorm (f : Fin 3 → ℚ) (A : Type*) [CommRing A] [Algebra ℚ A] (h : Fin 4 → A) : A :=
  BlockConjugationCoordinates.qnorm (algebraMap ℚ A (f 0)) (algebraMap ℚ A (f 1)) (algebraMap ℚ A (f 2)) h

section Block

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "QT" => commutativeScalarExtensionQuadraticForm T A
local notation "QU" =>
  commutativeScalarExtensionQuadraticForm (nonisotropicLastExtension T (f 0 * f 1 * f 2) hδ) A
local notation "ιTU" => nonisotropicLastComplementCliffordMap T (f 0 * f 1 * f 2) hδ A

include hT in
theorem nonisotropicLastExtension_pairingMatrix_eq_diagonal :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).pairingMatrix =
      diagonal (diagonalBlockWeights f) := by
  rw [nonisotropicLastExtension_pairingMatrix, hT]
  ext i j
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last =>
      rw [nonisotropicLastBlockMatrix_last_last, diagonal_apply_eq]
      rfl
    | cast j =>
      rw [nonisotropicLastBlockMatrix_last_castSucc, diagonal_apply_ne]
      exact (Fin.castSucc_lt_last j).ne'
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      rw [nonisotropicLastBlockMatrix_castSucc_last, diagonal_apply_ne]
      exact (Fin.castSucc_lt_last i).ne
    | cast j =>
      rw [nonisotropicLastBlockMatrix_castSucc_castSucc]
      by_cases hij : i = j
      · subst hij
        rw [diagonal_apply_eq, diagonal_apply_eq]
        fin_cases i <;> rfl
      · rw [diagonal_apply_ne _ hij,
          diagonal_apply_ne _ fun h ↦ hij (Fin.castSucc_injective _ h)]

include hT in
theorem diagonalBlock_qT_single (i : Fin 3) : QT (Pi.single i 1) = algebraMap ℚ A (f i) :=
  T.commutativeScalarExtensionQuadraticForm_single_of_diagonal A hT i

include hT in
theorem diagonalBlock_qU_single (j : Fin 4) :
    QU (Pi.single j 1) = algebraMap ℚ A (diagonalBlockWeights f j) :=
  (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeScalarExtensionQuadraticForm_single_of_diagonal
    A (T.nonisotropicLastExtension_pairingMatrix_eq_diagonal hT hδ) j

include hT in
theorem diagonalBlock_orthoT : ∀ i j, i ≠ j → QuadraticMap.IsOrtho QT (stdVec 3 A i) (stdVec 3 A j) :=
  fun _ _ hij ↦ T.commutativeScalarExtensionQuadraticForm_isOrtho_of_diagonal A hT hij

include hT in
theorem diagonalBlock_orthoU : ∀ i j, i ≠ j → QuadraticMap.IsOrtho QU (stdVec 4 A i) (stdVec 4 A j) :=
  fun _ _ hij ↦
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeScalarExtensionQuadraticForm_isOrtho_of_diagonal
      A (T.nonisotropicLastExtension_pairingMatrix_eq_diagonal hT hδ) hij

theorem diagonalBlock_spanT : ∀ m : Fin 3 → A, m ∈ Submodule.span A (Set.range (stdVec 3 A)) :=
  single_mem_span_range A

theorem diagonalBlock_spanU : ∀ m : Fin 4 → A, m ∈ Submodule.span A (Set.range (stdVec 4 A)) :=
  single_mem_span_range A

include hT in
theorem diagonalBlock_hD :
    QU (stdVec 4 A 3) = QU (stdVec 4 A 0) * QU (stdVec 4 A 1) * QU (stdVec 4 A 2) := by
  simp only [stdVec, T.diagonalBlock_qU_single hT hδ A, diagonalBlockWeights, ← map_mul]
  rfl

include hT in
theorem diagonalBlock_hdinv : diagonalBlockScalar f A * QU (stdVec 4 A 3) = 1 := by
  rw [stdVec, T.diagonalBlock_qU_single hT hδ A, diagonalBlockScalar, ← map_mul]
  change algebraMap ℚ A ((f 0 * f 1 * f 2)⁻¹ * (f 0 * f 1 * f 2)) = 1
  rw [inv_mul_cancel₀ hδ, map_one]

include hT in
theorem diagonalBlock_hd :
    QU (stdVec 4 A 0) * QU (stdVec 4 A 1) * QU (stdVec 4 A 2) * QU (stdVec 4 A 3) *
      (diagonalBlockScalar f A * diagonalBlockScalar f A) = 1 := by
  rw [← T.diagonalBlock_hD hT hδ A, show ∀ q d : A, q * q * (d * d) = (d * q) * (d * q) by
    intros; ring, T.diagonalBlock_hdinv hT hδ A, one_mul]

theorem nonisotropicLastComplementInclude_single (i : Fin 3) :
    nonisotropicLastComplementInclude (Pi.single i (1 : A)) = Pi.single (Fin.castSucc i) 1 := by
  ext j
  cases j using Fin.lastCases with
  | last =>
    simp only [nonisotropicLastComplementInclude, Fin.lastCases_last]
    rw [Pi.single_apply, if_neg (Fin.castSucc_lt_last i).ne']
  | cast j => simp [Pi.single_apply]

theorem complementCliffordMap_ι_single (i : Fin 3) :
    ιTU (ι QT (Pi.single i 1)) = ι QU (Pi.single (Fin.castSucc i) 1) := by
  rw [nonisotropicLastComplementCliffordMap_ι, nonisotropicLastComplementInclude_single]

theorem complementCliffordMap_evenElem (h : Fin 4 → A) :
    ιTU (OrthogonalTriple.evenElem QT (stdVec 3 A) h) =
      OrthogonalTriple.evenElem QU (BlockSplitting.tv (stdVec 4 A)) h := by
  simp only [OrthogonalTriple.evenElem, OrthogonalTriple.gen, map_add, map_smul, map_mul,
    AlgHom.commutes, stdVec, complementCliffordMap_ι_single, BlockSplitting.tv]

theorem complementCliffordMap_volume :
    ιTU (OrthogonalTriple.volume QT (stdVec 3 A)) =
      OrthogonalTriple.volume QU (BlockSplitting.tv (stdVec 4 A)) := by
  simp only [OrthogonalTriple.volume, OrthogonalTriple.gen, map_mul, stdVec,
    complementCliffordMap_ι_single, BlockSplitting.tv]

theorem complementCliffordMap_mem_even {x : CliffordAlgebra QT} (hx : x ∈ even QT) :
    ιTU x ∈ evenOdd QU 0 := by
  rw [CliffordAlgebra.mem_evenOdd_zero_iff_mem_even, mem_even_iff_involute_eq_of_invertible_two,
    ← nonisotropicLastComplementCliffordMap_involute, (mem_even_iff_involute_eq_of_invertible_two).1 hx]

/-! ## The block map `Φ(x, y) = ι(x) p₊ + ι(y) p₋` and its inverse -/

/-- The block Clifford map `Φ(x, y) = ι(x) p₊ + ι(y) p₋`. -/
def diagonalBlockClifford (x y : CliffordAlgebra QT) : CliffordAlgebra QU :=
  ιTU x * OrthogonalQuadruple.idemPlus QU (stdVec 4 A) (diagonalBlockScalar f A) +
    ιTU y * OrthogonalQuadruple.idemMinus QU (stdVec 4 A) (diagonalBlockScalar f A)

/-- The inverse `Ψ(ι(α) + ι(β) e₃) = (α − βν, α + βν)`, read off from the normal form. -/
def diagonalBlockCliffordInv (g : CliffordAlgebra QU) : CliffordAlgebra QT × CliffordAlgebra QT :=
  (((T.nonisotropicLastBlockCliffordNormalFormLinearEquiv (f 0 * f 1 * f 2) hδ A).symm g).1 -
      ((T.nonisotropicLastBlockCliffordNormalFormLinearEquiv (f 0 * f 1 * f 2) hδ A).symm g).2 *
        OrthogonalTriple.volume QT (stdVec 3 A),
    ((T.nonisotropicLastBlockCliffordNormalFormLinearEquiv (f 0 * f 1 * f 2) hδ A).symm g).1 +
      ((T.nonisotropicLastBlockCliffordNormalFormLinearEquiv (f 0 * f 1 * f 2) hδ A).symm g).2 *
        OrthogonalTriple.volume QT (stdVec 3 A))

include hT in
theorem diagonalBlockClifford_inv (g : CliffordAlgebra QU) :
    T.diagonalBlockClifford hδ A (T.diagonalBlockCliffordInv hδ A g).1
        (T.diagonalBlockCliffordInv hδ A g).2 = g := by
  obtain ⟨⟨α, β⟩, rfl⟩ :=
    (T.nonisotropicLastBlockCliffordNormalFormLinearEquiv (f 0 * f 1 * f 2) hδ A).surjective g
  simp only [diagonalBlockCliffordInv]
  rw [LinearEquiv.symm_apply_apply, nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply]
  unfold diagonalBlockClifford
  rw [map_sub, map_add, map_mul, complementCliffordMap_volume]
  have key : ∀ X Y ν P M : CliffordAlgebra QU,
      (X - Y * ν) * P + (X + Y * ν) * M = X * (P + M) - Y * (ν * (P - M)) := by
    intros; noncomm_ring
  rw [key, OrthogonalQuadruple.idemPlus_add_idemMinus, BlockSplitting.idemPlus_sub_idemMinus,
    BlockSplitting.triple_volume_mul_normVolume QU (stdVec 4 A) (T.diagonalBlock_orthoU hT hδ A)
      (T.diagonalBlock_hD hT hδ A) (T.diagonalBlock_hdinv hT hδ A), mul_one, mul_neg,
    sub_neg_eq_add]
  rfl

include hT in
theorem diagonalBlockCliffordInv_clifford (x y : CliffordAlgebra QT) :
    T.diagonalBlockCliffordInv hδ A (T.diagonalBlockClifford hδ A x y) = (x, y) := by
  let ν := OrthogonalTriple.volume QT (stdVec 3 A)
  let d := diagonalBlockScalar f A
  have key : T.diagonalBlockClifford hδ A x y =
      T.nonisotropicLastBlockCliffordNormalFormLinearEquiv (f 0 * f 1 * f 2) hδ A
        (⅟(2 : A) • (x + y), (⅟(2 : A) * d) • ((x - y) * ν)) := by
    rw [nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply]
    unfold diagonalBlockClifford
    rw [BlockSplitting.mul_idemPlus_add_mul_idemMinus, map_smul, map_smul, map_add, map_mul,
      map_sub, complementCliffordMap_volume]
    unfold OrthogonalQuadruple.normVolume
    rw [BlockSplitting.volume_eq_triple_mul_last]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
    rfl
  have hνν := OrthogonalTriple.volume_mul_volume QT (stdVec 3 A) (T.diagonalBlock_orthoT hT A)
  simp only [stdVec, T.diagonalBlock_qT_single hT A] at hνν
  have hscal : (⅟(2 : A) * diagonalBlockScalar f A) *
      (algebraMap ℚ A (f 0) * algebraMap ℚ A (f 1) * algebraMap ℚ A (f 2)) = ⅟(2 : A) := by
    rw [diagonalBlockScalar, mul_assoc, ← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hδ, map_one,
      mul_one]
  have hsq : ((⅟(2 : A) * d) • ((x - y) * ν)) * ν = -(⅟(2 : A) • (x - y)) := by
    rw [smul_mul_assoc, mul_assoc]
    change (⅟(2 : A) * d) • ((x - y) * (OrthogonalTriple.volume QT (stdVec 3 A) *
      OrthogonalTriple.volume QT (stdVec 3 A))) = _
    rw [hνν, mul_neg, ← Algebra.commutes, ← Algebra.smul_def, smul_neg, smul_smul, hscal]
  rw [key]
  simp only [diagonalBlockCliffordInv]
  rw [LinearEquiv.symm_apply_apply]
  change (⅟(2 : A) • (x + y) - ((⅟(2 : A) * d) • ((x - y) * ν)) * ν,
    ⅟(2 : A) • (x + y) + ((⅟(2 : A) * d) • ((x - y) * ν)) * ν) = (x, y)
  rw [hsq]
  refine Prod.ext ?_ ?_
  · change ⅟(2 : A) • (x + y) - -(⅟(2 : A) • (x - y)) = x
    calc ⅟(2 : A) • (x + y) - -(⅟(2 : A) • (x - y)) = (⅟(2 : A) + ⅟(2 : A)) • x := by module
      _ = x := by rw [invOf_two_add_invOf_two, one_smul]
  · change ⅟(2 : A) • (x + y) + -(⅟(2 : A) • (x - y)) = y
    calc ⅟(2 : A) • (x + y) + -(⅟(2 : A) • (x - y)) = (⅟(2 : A) + ⅟(2 : A)) • y := by module
      _ = y := by rw [invOf_two_add_invOf_two, one_smul]

include hT in
theorem diagonalBlockClifford_injective {x y x' y' : CliffordAlgebra QT}
    (h : T.diagonalBlockClifford hδ A x y = T.diagonalBlockClifford hδ A x' y') : x = x' ∧ y = y' := by
  have := congrArg (T.diagonalBlockCliffordInv hδ A) h
  rw [T.diagonalBlockCliffordInv_clifford hT hδ A, T.diagonalBlockCliffordInv_clifford hT hδ A] at this
  exact Prod.mk.inj this

omit [Algebra ℚ A] in
theorem block_mul_aux {B : Type*} [Ring B] {X Y X' Y' P M : B} (hPP : P * P = P) (hMM : M * M = M)
    (hPM : P * M = 0) (hMP : M * P = 0) (h1 : X' * P = P * X') (h2 : X' * M = M * X')
    (h3 : Y' * P = P * Y') (h4 : Y' * M = M * Y') :
    X * X' * P + Y * Y' * M = (X * P + Y * M) * (X' * P + Y' * M) := by
  simp only [add_mul, mul_add, mul_assoc]
  rw [← mul_assoc P X', ← h1, mul_assoc, hPP, ← mul_assoc P Y', ← h3, mul_assoc, hPM,
    ← mul_assoc M X', ← h2, mul_assoc, hMP, ← mul_assoc M Y', ← h4, mul_assoc, hMM]
  simp only [mul_zero, zero_add, add_zero]

include hT in
/-- `Φ` is multiplicative on even second factors. -/
theorem diagonalBlockClifford_mul (x y : CliffordAlgebra QT) {x' y' : CliffordAlgebra QT}
    (hx' : x' ∈ even QT) (hy' : y' ∈ even QT) :
    T.diagonalBlockClifford hδ A (x * x') (y * y') =
      T.diagonalBlockClifford hδ A x y * T.diagonalBlockClifford hδ A x' y' := by
  have hvU := T.diagonalBlock_orthoU hT hδ A
  have hsU := diagonalBlock_spanU A
  have hd := T.diagonalBlock_hd hT hδ A
  unfold diagonalBlockClifford
  rw [map_mul, map_mul]
  exact block_mul_aux (OrthogonalQuadruple.idemPlus_mul_self _ _ hvU hd)
    (OrthogonalQuadruple.idemMinus_mul_self _ _ hvU hd)
    (OrthogonalQuadruple.idemPlus_mul_idemMinus _ _ hvU hd)
    (OrthogonalQuadruple.idemMinus_mul_idemPlus _ _ hvU hd)
    (OrthogonalQuadruple.even_mul_idemPlus QU (stdVec 4 A) hvU hsU
      (T.complementCliffordMap_mem_even hδ A hx'))
    (OrthogonalQuadruple.even_mul_idemMinus QU (stdVec 4 A) hvU hsU
      (T.complementCliffordMap_mem_even hδ A hx'))
    (OrthogonalQuadruple.even_mul_idemPlus QU (stdVec 4 A) hvU hsU
      (T.complementCliffordMap_mem_even hδ A hy'))
    (OrthogonalQuadruple.even_mul_idemMinus QU (stdVec 4 A) hvU hsU
      (T.complementCliffordMap_mem_even hδ A hy'))

theorem diagonalBlockClifford_involute (x y : CliffordAlgebra QT) :
    involute (T.diagonalBlockClifford hδ A x y) =
      T.diagonalBlockClifford hδ A (involute x) (involute y) := by
  unfold diagonalBlockClifford
  rw [map_add, map_mul, map_mul, ← T.nonisotropicLastComplementCliffordMap_involute _ hδ A x,
    ← T.nonisotropicLastComplementCliffordMap_involute _ hδ A y,
    OrthogonalQuadruple.involute_idemPlus QU (stdVec 4 A),
    OrthogonalQuadruple.involute_idemMinus QU (stdVec 4 A)]

include hT in
theorem diagonalBlockClifford_reverse {x y : CliffordAlgebra QT} (hx : x ∈ even QT)
    (hy : y ∈ even QT) :
    reverse (T.diagonalBlockClifford hδ A x y) =
      T.diagonalBlockClifford hδ A (reverse x) (reverse y) := by
  have hvU := T.diagonalBlock_orthoU hT hδ A
  have hsU := diagonalBlock_spanU A
  have hrx : reverse x ∈ even QT := by
    rw [← CliffordAlgebra.mem_evenOdd_zero_iff_mem_even, reverse_mem_evenOdd_iff,
      CliffordAlgebra.mem_evenOdd_zero_iff_mem_even]
    exact hx
  have hry : reverse y ∈ even QT := by
    rw [← CliffordAlgebra.mem_evenOdd_zero_iff_mem_even, reverse_mem_evenOdd_iff,
      CliffordAlgebra.mem_evenOdd_zero_iff_mem_even]
    exact hy
  unfold diagonalBlockClifford
  rw [map_add, reverse.map_mul, reverse.map_mul, OrthogonalQuadruple.reverse_idemPlus _ _ hvU,
    OrthogonalQuadruple.reverse_idemMinus _ _ hvU,
    ← T.nonisotropicLastComplementCliffordMap_reverse _ hδ A x,
    ← T.nonisotropicLastComplementCliffordMap_reverse _ hδ A y,
    OrthogonalQuadruple.even_mul_idemPlus QU (stdVec 4 A) hvU hsU
      (T.complementCliffordMap_mem_even hδ A hrx),
    OrthogonalQuadruple.even_mul_idemMinus QU (stdVec 4 A) hvU hsU
      (T.complementCliffordMap_mem_even hδ A hry)]

theorem diagonalBlockClifford_one : T.diagonalBlockClifford hδ A 1 1 = 1 := by
  unfold diagonalBlockClifford
  rw [map_one, one_mul, one_mul, OrthogonalQuadruple.idemPlus_add_idemMinus]

theorem diagonalBlockClifford_self (x : CliffordAlgebra QT) : T.diagonalBlockClifford hδ A x x = ιTU x := by
  unfold diagonalBlockClifford
  rw [← mul_add, OrthogonalQuadruple.idemPlus_add_idemMinus, mul_one]

/-! ## Φ is a Spin point -/

include hδ in
theorem diagonalBlock_f_ne_zero (i : Fin 3) : f i ≠ 0 := by
  fin_cases i
  · exact left_ne_zero_of_mul (left_ne_zero_of_mul hδ)
  · exact right_ne_zero_of_mul (left_ne_zero_of_mul hδ)
  · exact right_ne_zero_of_mul hδ

include hδ in
theorem diagonalBlock_inv_mul (i : Fin 3) : algebraMap ℚ A (f i)⁻¹ * algebraMap ℚ A (f i) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (diagonalBlock_f_ne_zero hδ i), map_one]

include hδ in
theorem diagonalBlock_scalar_mul :
    diagonalBlockScalar f A * (algebraMap ℚ A (f 0) * algebraMap ℚ A (f 1) * algebraMap ℚ A (f 2)) = 1 := by
  rw [diagonalBlockScalar, ← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hδ, map_one]

include hT in
theorem diagonalBlock_mappedFormMatrix :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).specialOrthogonalMappedFormMatrix A =
      diagonal ![algebraMap ℚ A (f 0), algebraMap ℚ A (f 1), algebraMap ℚ A (f 2),
        algebraMap ℚ A (f 0) * algebraMap ℚ A (f 1) * algebraMap ℚ A (f 2)] := by
  rw [specialOrthogonalMappedFormMatrix, T.nonisotropicLastExtension_pairingMatrix_eq_diagonal hT hδ,
    diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [diagonalBlockWeights]

include hT in
theorem diagonalBlockConjMatrix_mem {h k : Fin 4 → A} (hh : diagonalBlockNorm f A h = 1)
    (hk : diagonalBlockNorm f A k = 1) :
    (diagonalBlockConjMatrix f A h k)ᵀ *
          (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).specialOrthogonalMappedFormMatrix A *
        diagonalBlockConjMatrix f A h k =
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).specialOrthogonalMappedFormMatrix A ∧
      (diagonalBlockConjMatrix f A h k).det = 1 := by
  rw [T.diagonalBlock_mappedFormMatrix hT hδ A]
  exact ⟨BlockConjugationCoordinates.conjMatrix_orthogonal (diagonalBlock_inv_mul hδ A 0)
      (diagonalBlock_inv_mul hδ A 1) (diagonalBlock_inv_mul hδ A 2) (diagonalBlock_scalar_mul hδ A) hh hk,
    BlockConjugationCoordinates.det_conjMatrix_eq_one (diagonalBlock_inv_mul hδ A 0)
      (diagonalBlock_inv_mul hδ A 1) (diagonalBlock_inv_mul hδ A 2) (diagonalBlock_scalar_mul hδ A) hh hk⟩

include hT in
theorem diagonalBlock_evenNorm (h : Fin 4 → A) :
    OrthogonalTriple.evenNorm QT (stdVec 3 A) h = diagonalBlockNorm f A h := by
  simp only [OrthogonalTriple.evenNorm, stdVec, T.diagonalBlock_qT_single hT A]
  rfl

include hT in
theorem diagonalBlock_exists_coords {x : CliffordAlgebra QT} (hx : x ∈ even QT) :
    ∃ h : Fin 4 → A, x = OrthogonalTriple.evenElem QT (stdVec 3 A) h :=
  OrthogonalTriple.exists_evenElem_of_mem_evenSpan QT _ (T.diagonalBlock_orthoT hT A)
    (OrthogonalTriple.mem_evenSpan_of_mem_even QT _ (T.diagonalBlock_orthoT hT A)
      (diagonalBlock_spanT A) ((CliffordAlgebra.mem_evenOdd_zero_iff_mem_even QT).2 hx))

include hT in
theorem diagonalBlockNorm_eq_one {h : Fin 4 → A}
    (hr : OrthogonalTriple.evenElem QT (stdVec 3 A) h *
      reverse (OrthogonalTriple.evenElem QT (stdVec 3 A) h) = 1) :
    diagonalBlockNorm f A h = 1 := by
  rw [OrthogonalTriple.evenElem_mul_reverse QT _ (T.diagonalBlock_orthoT hT A),
    ← map_one (algebraMap A (CliffordAlgebra QT))] at hr
  rw [← T.diagonalBlock_evenNorm hT A]
  exact CliffordAlgebra.algebraMap_injective_of_invertible_two QT hr

theorem diagonalBlockClifford_evenElem (h k : Fin 4 → A) :
    T.diagonalBlockClifford hδ A (OrthogonalTriple.evenElem QT (stdVec 3 A) h)
        (OrthogonalTriple.evenElem QT (stdVec 3 A) k) =
      BlockSplitting.blockElem QU (stdVec 4 A) (diagonalBlockScalar f A) h k := by
  unfold diagonalBlockClifford
  rw [T.complementCliffordMap_evenElem hδ A, T.complementCliffordMap_evenElem hδ A]
  rfl

include hT in
theorem diagonalBlock_conjCoords (h k c : Fin 4 → A) :
    BlockSplitting.conjCoords QU (stdVec 4 A) (diagonalBlockScalar f A) (algebraMap ℚ A (f 0)⁻¹)
        (algebraMap ℚ A (f 1)⁻¹) (algebraMap ℚ A (f 2)⁻¹) h k c =
      diagonalBlockConjMatrix f A h k *ᵥ c := by
  rw [BlockSplitting.conjCoords_eq_coordinates _ _ (T.diagonalBlock_hD hT hδ A)]
  simp only [stdVec, T.diagonalBlock_qU_single hT hδ A]
  rw [diagonalBlockConjMatrix, ← BlockConjugationCoordinates.conjCoords_eq_mulVec]
  rfl

theorem diagonalBlock_vector_single (i : Fin 4) :
    (Pi.single i (1 : A) : Fin 4 → A) 0 • OrthogonalQuadruple.gen QU (stdVec 4 A) 0 +
        (Pi.single i (1 : A) : Fin 4 → A) 1 • OrthogonalQuadruple.gen QU (stdVec 4 A) 1 +
        (Pi.single i (1 : A) : Fin 4 → A) 2 • OrthogonalQuadruple.gen QU (stdVec 4 A) 2 +
        (Pi.single i (1 : A) : Fin 4 → A) 3 • OrthogonalQuadruple.gen QU (stdVec 4 A) 3 =
      ι QU (Pi.single i 1) := by
  fin_cases i <;> simp [OrthogonalQuadruple.gen]

/-- `Φ(x, y)` in the fixed tensor coordinates of the intrinsic Spin carrier. -/
def diagonalBlockPointClifford (x y : CliffordAlgebra QT) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordCoordinateBaseChangeAlgebra A :=
  ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A).symm
    (T.diagonalBlockClifford hδ A x y)

@[simp]
theorem commutativeTensorCliffordEquiv_diagonalBlockPointClifford (x y : CliffordAlgebra QT) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A
        (T.diagonalBlockPointClifford hδ A x y) = T.diagonalBlockClifford hδ A x y :=
  AlgEquiv.apply_symm_apply _ _

include hT in
/-- The vector graph of `Φ(h, k)` with the explicit matrix `conjMatrix(h, k)`. -/
theorem diagonalBlock_vectorGraph (h k : Fin 4 → A) (i : Fin 4) :
    T.diagonalBlockPointClifford hδ A (OrthogonalTriple.evenElem QT (stdVec 3 A) h)
          (OrthogonalTriple.evenElem QT (stdVec 3 A) k) *
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordCoordinateBaseChangeVector A i *
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordCoordinateBaseChangeReverse A
          (T.diagonalBlockPointClifford hδ A (OrthogonalTriple.evenElem QT (stdVec 3 A) h)
            (OrthogonalTriple.evenElem QT (stdVec 3 A) k)) =
      ∑ j, diagonalBlockConjMatrix f A h k j i •
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordCoordinateBaseChangeVector A j := by
  apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A).injective
  rw [map_mul, map_mul, commutativeTensorCliffordEquiv_reverse,
    commutativeTensorCliffordEquiv_diagonalBlockPointClifford,
    commutativeTensorCliffordEquiv_baseChangeVector, map_sum]
  simp only [map_smul, commutativeTensorCliffordEquiv_baseChangeVector]
  rw [T.diagonalBlockClifford_evenElem hδ A, ← T.diagonalBlock_vector_single hδ A i,
    BlockSplitting.blockElem_conj_vector QU (stdVec 4 A) (T.diagonalBlock_orthoU hT hδ A)
      (diagonalBlock_spanU A) (T.diagonalBlock_hD hT hδ A) (T.diagonalBlock_hdinv hT hδ A)
      (u0 := algebraMap ℚ A (f 0)⁻¹) (u1 := algebraMap ℚ A (f 1)⁻¹) (u2 := algebraMap ℚ A (f 2)⁻¹)
      (by simpa [stdVec, T.diagonalBlock_qU_single hT hδ A, diagonalBlockWeights] using
        diagonalBlock_inv_mul hδ A 0)
      (by simpa [stdVec, T.diagonalBlock_qU_single hT hδ A, diagonalBlockWeights] using
        diagonalBlock_inv_mul hδ A 1)
      (by simpa [stdVec, T.diagonalBlock_qU_single hT hδ A, diagonalBlockWeights] using
        diagonalBlock_inv_mul hδ A 2),
    T.diagonalBlock_conjCoords hT hδ A, Fin.sum_univ_four]
  simp only [mulVec_single_one, Matrix.col_apply, stdVec, OrthogonalQuadruple.gen]

theorem diagonalBlockClifford_mem_even {x y : CliffordAlgebra QT} (hx : x ∈ even QT) (hy : y ∈ even QT) :
    T.diagonalBlockClifford hδ A x y ∈ even QU := by
  rw [mem_even_iff_involute_eq_of_invertible_two, T.diagonalBlockClifford_involute hδ A,
    (mem_even_iff_involute_eq_of_invertible_two).1 hx, (mem_even_iff_involute_eq_of_invertible_two).1 hy]

theorem reverse_mem_even {x : CliffordAlgebra QT} (hx : x ∈ even QT) : reverse x ∈ even QT := by
  rw [← CliffordAlgebra.mem_evenOdd_zero_iff_mem_even, reverse_mem_evenOdd_iff,
    CliffordAlgebra.mem_evenOdd_zero_iff_mem_even]
  exact hx

include hT in
theorem diagonalBlockClifford_mul_reverse {x y : CliffordAlgebra QT} (hx : x ∈ even QT)
    (hy : y ∈ even QT) :
    T.diagonalBlockClifford hδ A x y * reverse (T.diagonalBlockClifford hδ A x y) =
      T.diagonalBlockClifford hδ A (x * reverse x) (y * reverse y) := by
  rw [T.diagonalBlockClifford_reverse hT hδ A hx hy,
    ← T.diagonalBlockClifford_mul hT hδ A _ _ (T.reverse_mem_even A hx) (T.reverse_mem_even A hy)]

include hT in
/-- `Φ(x, y)` is an intrinsic Spin point for even norm-one `x, y`. -/
theorem isCliffordSpinIntrinsicPoint_diagonalBlock {x y : CliffordAlgebra QT} (hx : x ∈ even QT)
    (hy : y ∈ even QT) (hxr : x * reverse x = 1) (hyr : y * reverse y = 1) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).IsCliffordSpinIntrinsicPoint A
      (T.diagonalBlockPointClifford hδ A x y) := by
  obtain ⟨h, rfl⟩ := T.diagonalBlock_exists_coords hT A hx
  obtain ⟨k, rfl⟩ := T.diagonalBlock_exists_coords hT A hy
  have hh := T.diagonalBlockNorm_eq_one hT A hxr
  have hk := T.diagonalBlockNorm_eq_one hT A hyr
  refine ⟨?_, ?_, ⟨⟨diagonalBlockConjMatrix f A h k, T.diagonalBlockConjMatrix_mem hT hδ A hh hk⟩,
    T.diagonalBlock_vectorGraph hT hδ A h k⟩⟩
  · apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv_mem_even_iff
      A _).1
    rw [commutativeTensorCliffordEquiv_diagonalBlockPointClifford]
    exact T.diagonalBlockClifford_mem_even hδ A hx hy
  · apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A).injective
    rw [map_mul, commutativeTensorCliffordEquiv_reverse,
      commutativeTensorCliffordEquiv_diagonalBlockPointClifford, map_one,
      T.diagonalBlockClifford_mul_reverse hT hδ A hx hy, hxr, hyr, T.diagonalBlockClifford_one hδ A]

include hδ in
theorem diagonalBlockConjMatrix_fixesLastCoordinate {c : Fin 4 → A} (hc : diagonalBlockNorm f A c = 1) :
    FixesLastCoordinate (diagonalBlockConjMatrix f A c c) := by
  unfold FixesLastCoordinate
  rw [diagonalBlockConjMatrix, ← BlockConjugationCoordinates.conjCoords_eq_mulVec]
  exact BlockConjugationCoordinates.conjCoords_self_last (diagonalBlock_scalar_mul hδ A) hc

include hT hδ in
/-- In rank three, every even norm-one Clifford element is an intrinsic Spin point: its diagonal
block image `ι(a)` fixes the added vector, so the stabilizer range theorem applies. -/
theorem exists_spinPoint_of_even_of_mul_reverse {a : CliffordAlgebra QT} (ha : a ∈ even QT)
    (har : a * reverse a = 1) :
    ∃ x : T.CliffordSpinIntrinsicPoint A, T.commutativeTensorCliffordEquiv A x.1 = a := by
  obtain ⟨c, rfl⟩ := T.diagonalBlock_exists_coords hT A ha
  have hc := T.diagonalBlockNorm_eq_one hT A har
  let w : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A :=
    ⟨T.diagonalBlockPointClifford hδ A _ _, T.isCliffordSpinIntrinsicPoint_diagonalBlock hT hδ A ha ha har har⟩
  have hfix : T.IsNonisotropicLastBlockSpinFixedPoint (f 0 * f 1 * f 2) hδ A w := by
    unfold IsNonisotropicLastBlockSpinFixedPoint
    rw [CliffordSpinIntrinsicPoint.matrixPoint_eq _ A w
      (⟨diagonalBlockConjMatrix f A c c, T.diagonalBlockConjMatrix_mem hT hδ A hc hc⟩ :
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).specialOrthogonalMatrixPoint A)
      (T.diagonalBlock_vectorGraph hT hδ A c c)]
    exact diagonalBlockConjMatrix_fixesLastCoordinate hδ A hc
  obtain ⟨x, hx, -⟩ :=
    T.existsUnique_nonisotropicLastComplementSpinPreimage_of_fixes (f 0 * f 1 * f 2) hδ A w hfix
  refine ⟨x, ?_⟩
  have h1 := congrArg
    (fun z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A ↦
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A z.1) hx
  simp only [nonisotropicLastComplementSpinPoint_coe,
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap, w,
    commutativeTensorCliffordEquiv_diagonalBlockPointClifford, T.diagonalBlockClifford_self hδ A] at h1
  exact T.nonisotropicLastComplementCliffordMap_injective _ hδ A h1

include hT in
theorem diagonalBlockCliffordInv_even {g : CliffordAlgebra QU} (hg : g ∈ even QU) :
    (T.diagonalBlockCliffordInv hδ A g).1 ∈ even QT ∧ (T.diagonalBlockCliffordInv hδ A g).2 ∈ even QT := by
  have hΦ := T.diagonalBlockClifford_inv hT hδ A g
  have hinv : T.diagonalBlockClifford hδ A (involute (T.diagonalBlockCliffordInv hδ A g).1)
      (involute (T.diagonalBlockCliffordInv hδ A g).2) =
      T.diagonalBlockClifford hδ A (T.diagonalBlockCliffordInv hδ A g).1
        (T.diagonalBlockCliffordInv hδ A g).2 := by
    rw [← T.diagonalBlockClifford_involute hδ A, hΦ, (mem_even_iff_involute_eq_of_invertible_two).1 hg]
  obtain ⟨h1, h2⟩ := T.diagonalBlockClifford_injective hT hδ A hinv
  exact ⟨(mem_even_iff_involute_eq_of_invertible_two).2 h1,
    (mem_even_iff_involute_eq_of_invertible_two).2 h2⟩

include hT in
theorem diagonalBlockCliffordInv_mul_reverse {g : CliffordAlgebra QU} (hg : g ∈ even QU)
    (hgr : g * reverse g = 1) :
    (T.diagonalBlockCliffordInv hδ A g).1 * reverse (T.diagonalBlockCliffordInv hδ A g).1 = 1 ∧
      (T.diagonalBlockCliffordInv hδ A g).2 * reverse (T.diagonalBlockCliffordInv hδ A g).2 = 1 := by
  obtain ⟨he1, he2⟩ := T.diagonalBlockCliffordInv_even hT hδ A hg
  have hΦ := T.diagonalBlockClifford_inv hT hδ A g
  have key : T.diagonalBlockClifford hδ A
      ((T.diagonalBlockCliffordInv hδ A g).1 * reverse (T.diagonalBlockCliffordInv hδ A g).1)
      ((T.diagonalBlockCliffordInv hδ A g).2 * reverse (T.diagonalBlockCliffordInv hδ A g).2) =
      T.diagonalBlockClifford hδ A 1 1 := by
    rw [← T.diagonalBlockClifford_mul_reverse hT hδ A he1 he2, hΦ, hgr, T.diagonalBlockClifford_one hδ A]
  exact T.diagonalBlockClifford_injective hT hδ A key

include hT hδ in
theorem isCliffordSpinIntrinsicPoint_symm_of_even {a : CliffordAlgebra QT} (ha : a ∈ even QT)
    (har : a * reverse a = 1) :
    T.IsCliffordSpinIntrinsicPoint A ((T.commutativeTensorCliffordEquiv A).symm a) := by
  obtain ⟨x, hx⟩ := T.exists_spinPoint_of_even_of_mul_reverse hT hδ A ha har
  rw [← hx, AlgEquiv.symm_apply_apply]
  exact x.2

/-! ## The block Spin isomorphism -/

/-- The block Spin point `Φ(x, y) = ι(x) p₊ + ι(y) p₋`. -/
def diagonalBlockSpinPoint (x y : T.CliffordSpinIntrinsicPoint A) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A :=
  ⟨T.diagonalBlockPointClifford hδ A (T.commutativeTensorCliffordEquiv A x.1)
      (T.commutativeTensorCliffordEquiv A y.1),
    T.isCliffordSpinIntrinsicPoint_diagonalBlock hT hδ A x.commutativeClifford_mem_even
      y.commutativeClifford_mem_even x.commutativeClifford_mul_reverse_eq_one
      y.commutativeClifford_mul_reverse_eq_one⟩

@[simp]
theorem diagonalBlockSpinPoint_coe (x y : T.CliffordSpinIntrinsicPoint A) :
    (T.diagonalBlockSpinPoint hT hδ A x y).1 =
      T.diagonalBlockPointClifford hδ A (T.commutativeTensorCliffordEquiv A x.1)
        (T.commutativeTensorCliffordEquiv A y.1) :=
  rfl

/-- The inverse block Spin points `Ψ(z)`. -/
def diagonalBlockSpinPointInv
    (z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A) :
    T.CliffordSpinIntrinsicPoint A × T.CliffordSpinIntrinsicPoint A :=
  (⟨(T.commutativeTensorCliffordEquiv A).symm (T.diagonalBlockCliffordInv hδ A
        ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A z.1)).1,
      T.isCliffordSpinIntrinsicPoint_symm_of_even hT hδ A
        (T.diagonalBlockCliffordInv_even hT hδ A z.commutativeClifford_mem_even).1
        (T.diagonalBlockCliffordInv_mul_reverse hT hδ A z.commutativeClifford_mem_even
          z.commutativeClifford_mul_reverse_eq_one).1⟩,
    ⟨(T.commutativeTensorCliffordEquiv A).symm (T.diagonalBlockCliffordInv hδ A
        ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A z.1)).2,
      T.isCliffordSpinIntrinsicPoint_symm_of_even hT hδ A
        (T.diagonalBlockCliffordInv_even hT hδ A z.commutativeClifford_mem_even).2
        (T.diagonalBlockCliffordInv_mul_reverse hT hδ A z.commutativeClifford_mem_even
          z.commutativeClifford_mul_reverse_eq_one).2⟩)

/-- The block Spin isomorphism `Spin(T)(A) × Spin(T)(A) ≃* Spin(T ⊥ ⟨f₀f₁f₂⟩)(A)`, over every
commutative rational algebra. -/
def diagonalBlockSpinMulEquiv :
    (T.CliffordSpinIntrinsicPoint A × T.CliffordSpinIntrinsicPoint A) ≃*
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A where
  toFun p := T.diagonalBlockSpinPoint hT hδ A p.1 p.2
  invFun := T.diagonalBlockSpinPointInv hT hδ A
  left_inv p := by
    have key := T.diagonalBlockCliffordInv_clifford hT hδ A (T.commutativeTensorCliffordEquiv A p.1.1)
      (T.commutativeTensorCliffordEquiv A p.2.1)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (T.commutativeTensorCliffordEquiv A).symm (T.diagonalBlockCliffordInv hδ A
        ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A
          (T.diagonalBlockPointClifford hδ A _ _))).1 = _
      rw [commutativeTensorCliffordEquiv_diagonalBlockPointClifford, key, AlgEquiv.symm_apply_apply]
    · change (T.commutativeTensorCliffordEquiv A).symm (T.diagonalBlockCliffordInv hδ A
        ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A
          (T.diagonalBlockPointClifford hδ A _ _))).2 = _
      rw [commutativeTensorCliffordEquiv_diagonalBlockPointClifford, key, AlgEquiv.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    change T.diagonalBlockPointClifford hδ A
      (T.commutativeTensorCliffordEquiv A ((T.commutativeTensorCliffordEquiv A).symm _))
      (T.commutativeTensorCliffordEquiv A ((T.commutativeTensorCliffordEquiv A).symm _)) = z.1
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, diagonalBlockPointClifford,
      T.diagonalBlockClifford_inv hT hδ A, AlgEquiv.symm_apply_apply]
  map_mul' p q := by
    apply Subtype.ext
    rw [CliffordSpinIntrinsicPoint.mul_coe]
    change T.diagonalBlockPointClifford hδ A (T.commutativeTensorCliffordEquiv A (p.1 * q.1).1)
      (T.commutativeTensorCliffordEquiv A (p.2 * q.2).1) = T.diagonalBlockPointClifford hδ A _ _ *
        T.diagonalBlockPointClifford hδ A _ _
    rw [CliffordSpinIntrinsicPoint.mul_coe, CliffordSpinIntrinsicPoint.mul_coe, map_mul, map_mul,
      diagonalBlockPointClifford, T.diagonalBlockClifford_mul hT hδ A _ _ q.1.commutativeClifford_mem_even
        q.2.commutativeClifford_mem_even, map_mul]
    rfl

@[simp]
theorem diagonalBlockSpinMulEquiv_apply_coe (p : T.CliffordSpinIntrinsicPoint A × T.CliffordSpinIntrinsicPoint A) :
    (T.diagonalBlockSpinMulEquiv hT hδ A p).1 =
      T.diagonalBlockPointClifford hδ A (T.commutativeTensorCliffordEquiv A p.1.1)
        (T.commutativeTensorCliffordEquiv A p.2.1) :=
  rfl

end Block

/-! ## Naturality in the coefficient algebra -/

section Naturality

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) {A B : Type*} [CommRing A] [Algebra ℚ A]
  [CommRing B] [Algebra ℚ B] (φ : A →ₐ[ℚ] B)

theorem commutativeCliffordAlgebraBaseChangeHom_algebraMap (a : A) :
    V.commutativeCliffordAlgebraBaseChangeHom φ (algebraMap A _ a) = algebraMap B _ (φ a) := by
  rw [← (V.commutativeTensorCliffordEquiv A).commutes a,
    V.commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv, Algebra.TensorProduct.algebraMap_apply,
    V.cliffordCoordinateBaseChangeMap_tmul, Algebra.algebraMap_self_apply,
    ← (V.commutativeTensorCliffordEquiv B).commutes (φ a), Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self_apply]

theorem commutativeCliffordAlgebraBaseChangeHom_smul (a : A)
    (x : CliffordAlgebra (V.commutativeScalarExtensionQuadraticForm A)) :
    V.commutativeCliffordAlgebraBaseChangeHom φ (a • x) =
      φ a • V.commutativeCliffordAlgebraBaseChangeHom φ x := by
  rw [Algebra.smul_def, map_mul, V.commutativeCliffordAlgebraBaseChangeHom_algebraMap, ← Algebra.smul_def]

theorem commutativeCliffordAlgebraBaseChangeHom_ι_single (i : Fin n) :
    V.commutativeCliffordAlgebraBaseChangeHom φ
        (ι (V.commutativeScalarExtensionQuadraticForm A) (Pi.single i 1)) =
      ι (V.commutativeScalarExtensionQuadraticForm B) (Pi.single i 1) := by
  rw [V.commutativeCliffordAlgebraBaseChangeHom_ι]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem invOf_two_eq_algebraMap (R : Type*) [CommRing R] [Algebra ℚ R] [Invertible (2 : R)] :
    ⅟(2 : R) = algebraMap ℚ R 2⁻¹ :=
  invOf_eq_right_inv (by rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero,
    map_one])

theorem algHom_invOf_two : φ (⅟(2 : A)) = ⅟(2 : B) := by
  rw [invOf_two_eq_algebraMap, invOf_two_eq_algebraMap, AlgHom.commutes]

theorem commutativeCliffordAlgebraBaseChangeHom_idemPlus (V : RationalQuadraticSpaceMatrix 4) (q : ℚ) :
    V.commutativeCliffordAlgebraBaseChangeHom φ
        (OrthogonalQuadruple.idemPlus (V.commutativeScalarExtensionQuadraticForm A) (stdVec 4 A)
          (algebraMap ℚ A q)) =
      OrthogonalQuadruple.idemPlus (V.commutativeScalarExtensionQuadraticForm B) (stdVec 4 B)
        (algebraMap ℚ B q) := by
  simp only [OrthogonalQuadruple.idemPlus, OrthogonalQuadruple.normVolume, OrthogonalQuadruple.volume,
    OrthogonalQuadruple.gen, stdVec, V.commutativeCliffordAlgebraBaseChangeHom_smul, map_add, map_one,
    map_mul, V.commutativeCliffordAlgebraBaseChangeHom_ι_single, algHom_invOf_two, AlgHom.commutes]

theorem commutativeCliffordAlgebraBaseChangeHom_idemMinus (V : RationalQuadraticSpaceMatrix 4) (q : ℚ) :
    V.commutativeCliffordAlgebraBaseChangeHom φ
        (OrthogonalQuadruple.idemMinus (V.commutativeScalarExtensionQuadraticForm A) (stdVec 4 A)
          (algebraMap ℚ A q)) =
      OrthogonalQuadruple.idemMinus (V.commutativeScalarExtensionQuadraticForm B) (stdVec 4 B)
        (algebraMap ℚ B q) := by
  simp only [OrthogonalQuadruple.idemMinus, OrthogonalQuadruple.normVolume, OrthogonalQuadruple.volume,
    OrthogonalQuadruple.gen, stdVec, V.commutativeCliffordAlgebraBaseChangeHom_smul, map_sub, map_one,
    map_mul, V.commutativeCliffordAlgebraBaseChangeHom_ι_single, algHom_invOf_two, AlgHom.commutes]

end Naturality

section BlockNaturality

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
  (φ : A →ₐ[ℚ] B)

theorem diagonalBlockClifford_naturality
    (x y : CliffordAlgebra (T.commutativeScalarExtensionQuadraticForm A)) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeCliffordAlgebraBaseChangeHom φ
        (T.diagonalBlockClifford hδ A x y) =
      T.diagonalBlockClifford hδ B (T.commutativeCliffordAlgebraBaseChangeHom φ x)
        (T.commutativeCliffordAlgebraBaseChangeHom φ y) := by
  unfold diagonalBlockClifford diagonalBlockScalar
  rw [map_add, map_mul, map_mul, T.nonisotropicLastComplementCliffordMap_naturality,
    T.nonisotropicLastComplementCliffordMap_naturality,
    commutativeCliffordAlgebraBaseChangeHom_idemPlus, commutativeCliffordAlgebraBaseChangeHom_idemMinus]

include hT in
theorem diagonalBlockCliffordInv_naturality
    (g : CliffordAlgebra
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeScalarExtensionQuadraticForm A)) :
    T.diagonalBlockCliffordInv hδ B
        ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeCliffordAlgebraBaseChangeHom φ g) =
      (T.commutativeCliffordAlgebraBaseChangeHom φ (T.diagonalBlockCliffordInv hδ A g).1,
        T.commutativeCliffordAlgebraBaseChangeHom φ (T.diagonalBlockCliffordInv hδ A g).2) := by
  conv_lhs => rw [← T.diagonalBlockClifford_inv hT hδ A g, T.diagonalBlockClifford_naturality hδ φ]
  exact T.diagonalBlockCliffordInv_clifford hT hδ B _ _

include hT in
/-- The block Spin isomorphism commutes with arbitrary scalar extension. -/
theorem diagonalBlockSpinMulEquiv_naturality
    (p : T.CliffordSpinIntrinsicPoint A × T.CliffordSpinIntrinsicPoint A) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinIntrinsicPointMap φ
        (T.diagonalBlockSpinMulEquiv hT hδ A p) =
      T.diagonalBlockSpinMulEquiv hT hδ B
        (T.cliffordSpinIntrinsicPointMap φ p.1, T.cliffordSpinIntrinsicPointMap φ p.2) := by
  apply CliffordSpinIntrinsicPoint.ext
  apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv B).injective
  rw [cliffordSpinIntrinsicPointMap_coe, diagonalBlockSpinMulEquiv_apply_coe,
    diagonalBlockSpinMulEquiv_apply_coe, ← commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv,
    commutativeTensorCliffordEquiv_diagonalBlockPointClifford,
    commutativeTensorCliffordEquiv_diagonalBlockPointClifford, diagonalBlockClifford_naturality,
    cliffordSpinIntrinsicPointMap_coe, cliffordSpinIntrinsicPointMap_coe,
    commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv,
    commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv]

end BlockNaturality

end RationalQuadraticSpaceMatrix
