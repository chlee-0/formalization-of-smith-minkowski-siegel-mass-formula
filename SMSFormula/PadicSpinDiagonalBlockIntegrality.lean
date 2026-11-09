import SMSFormula.BlockConjugationIntegrality
import SMSFormula.RationalCliffordSpinDiagonalBlockCayley
import SMSFormula.AdelicSpinDiagonalBlockMeasureAssembly
import SMSFormula.RationalCliffordSpinCandidateIntegralComapVolume
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization
import SMSFormula.RationalCliffordGeneralSpinBlockIntegrality

/-!
# The block isomorphism matches integral loci at good places

Every intrinsic Spin point of the diagonal ternary space has norm-one quaternion coordinates `c`,
its special-orthogonal matrix is `M(c, c)|_T`, and the matrix of `Φ(x, y)` is `M(c_x, c_y)`.  At a
prime where `2, f₀, f₁, f₂` are units, `M(h, k)` is integral iff `h, k` are (norm one), so

`π_U(Φ(a, b))` integral  ⟺  `π_T(a)` and `π_T(b)` integral.

Off the integral-lifting bad places of `T` and `U`, integrality of a Spin point is integrality
of its special-orthogonal image (and its inverse), so `Φ_v` matches the integral loci.
Nothing is chosen.
-/

noncomputable section

open CliffordAlgebra Matrix PositiveDefiniteIntegralLattice
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

attribute [local instance] rationalAlgebraInvertibleTwo

set_option synthInstance.maxHeartbeats 400000

/-! ## Quaternion coordinates of intrinsic points -/

section Coordinates

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (A : Type*) [CommRing A] [Algebra ℚ A]

include hT in
/-- Every intrinsic ternary Spin point is the ternary point of norm-one quaternion coordinates. -/
theorem exists_eq_diagonalBlockTernaryPoint (x : T.CliffordSpinIntrinsicPoint A) :
    ∃ (c : Fin 4 → A) (hc : diagonalBlockNorm f A c = 1), x = T.diagonalBlockTernaryPoint hT hδ A hc := by
  have ha : T.commutativeTensorCliffordEquiv A x.1 ∈ even (commutativeScalarExtensionQuadraticForm T A) :=
    (T.commutativeTensorCliffordEquiv_mem_even_iff A x.1).2 x.2.1
  have har : T.commutativeTensorCliffordEquiv A x.1 * reverse (T.commutativeTensorCliffordEquiv A x.1) = 1 := by
    rw [← T.commutativeTensorCliffordEquiv_reverse, ← map_mul, x.2.2.1, map_one]
  obtain ⟨c, hceq⟩ := T.diagonalBlock_exists_coords hT A ha
  rw [hceq] at har
  have hc := T.diagonalBlockNorm_eq_one hT A har
  refine ⟨c, hc, ?_⟩
  apply CliffordSpinIntrinsicPoint.ext
  apply (T.commutativeTensorCliffordEquiv A).injective
  rw [commutativeTensorCliffordEquiv_diagonalBlockTernaryPoint, ← hceq]

end Coordinates

/-! ## Integrality of the block matrices over `ℚ_p` -/

section Integrality

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

theorem diagonalBlockConjMatrix_eq_conjMatrix (K : Type*) [Field K] [Algebra ℚ K] (h k : Fin 4 → K) :
    diagonalBlockConjMatrix f K h k =
      BlockConjugationCoordinates.conjMatrix (algebraMap ℚ K (f 0)) (algebraMap ℚ K (f 1)) (algebraMap ℚ K (f 2))
        (algebraMap ℚ K (f 0))⁻¹ (algebraMap ℚ K (f 1))⁻¹ (algebraMap ℚ K (f 2))⁻¹
        (algebraMap ℚ K (f 0) * algebraMap ℚ K (f 1) * algebraMap ℚ K (f 2))⁻¹ h k := by
  simp only [diagonalBlockConjMatrix, diagonalBlockScalar, map_inv₀, map_mul]

omit [Fact (Nat.Prime p)] in
/-- At a prime where `2, f₀, f₁, f₂` are units, `M(h, k)` is integral iff `h, k` are (norm one). -/
theorem diagonalBlockConjMatrix_integral_iff [Fact (Nat.Prime p)]
    (hf : ∀ i, ‖algebraMap ℚ ℚ_[p] (f i)‖ = 1) (h2 : ‖(2 : ℚ_[p])‖ = 1) {h k : Fin 4 → ℚ_[p]}
    (hh : diagonalBlockNorm f ℚ_[p] h = 1) (hk : diagonalBlockNorm f ℚ_[p] k = 1) :
    (∀ i j, diagonalBlockConjMatrix f ℚ_[p] h k i j ∈ PadicInt.subring p) ↔
      (∀ i, h i ∈ PadicInt.subring p) ∧ (∀ i, k i ∈ PadicInt.subring p) := by
  have hmem : ∀ i, algebraMap ℚ ℚ_[p] (f i) ∈ PadicInt.subring p :=
    fun i ↦ (PadicInt.mem_subring_iff p).2 (hf i).le
  have hinv : ∀ i, (algebraMap ℚ ℚ_[p] (f i))⁻¹ ∈ PadicInt.subring p :=
    fun i ↦ (PadicInt.mem_subring_iff p).2 (by rw [norm_inv, hf i, inv_one])
  have hne : ∀ i, algebraMap ℚ ℚ_[p] (f i) ≠ 0 := fun i h0 ↦ by
    have := hf i
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2m : (2 : ℚ_[p])⁻¹ ∈ PadicInt.subring p :=
    (PadicInt.mem_subring_iff p).2 (by rw [norm_inv, h2, inv_one])
  have hd : (algebraMap ℚ ℚ_[p] (f 0) * algebraMap ℚ ℚ_[p] (f 1) * algebraMap ℚ ℚ_[p] (f 2))⁻¹ ∈
      PadicInt.subring p := by
    rw [mul_inv, mul_inv]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hinv 0) (hinv 1)) (hinv 2)
  rw [diagonalBlockConjMatrix_eq_conjMatrix]
  constructor
  · intro hM
    have hprod := BlockConjugationCoordinates.mul_mem_of_conjMatrix_mem _ (hmem 0) (hmem 1) (hmem 2) (hinv 0)
      (hinv 1) (hinv 2) h2m two_ne_zero (hne 0) (hne 1) (hne 2) hM
    exact ⟨BlockConjugationCoordinates.mem_of_mul_mem (hmem 0) (hmem 1) (hmem 2) hk hprod,
      BlockConjugationCoordinates.mem_of_mul_mem (hmem 0) (hmem 1) (hmem 2) hh
        (fun m j ↦ by rw [mul_comm]; exact hprod j m)⟩
  · rintro ⟨hh', hk'⟩
    exact BlockConjugationCoordinates.conjMatrix_mem _ (hmem 0) (hmem 1) (hmem 2) (hinv 0) (hinv 1) (hinv 2) hd
      hh' hk'

/-- The matrix integrality of the block points: `π_U(Φ(a, b))` is integral iff `π_T(a)` and `π_T(b)`
are, at a prime where `2, f₀, f₁, f₂` are units. -/
theorem diagonalBlock_matrix_integral_iff (hf : ∀ i, ‖algebraMap ℚ ℚ_[p] (f i)‖ = 1)
    (h2 : ‖(2 : ℚ_[p])‖ = 1) (a b : T.CliffordSpinCandidateGroup ℚ_[p]) :
    (∀ i j, ((UU).cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
        (T.diagonalBlockSpinGroupMulEquiv hT hδ ℚ_[p] (a, b))).1.1.1 i j ∈ PadicInt.subring p) ↔
      (∀ i j, (T.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] a).1.1.1 i j ∈ PadicInt.subring p) ∧
        (∀ i j, (T.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] b).1.1.1 i j ∈ PadicInt.subring p) := by
  obtain ⟨c, hc, hca⟩ := T.exists_eq_diagonalBlockTernaryPoint hT hδ ℚ_[p]
    (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint ℚ_[p] a)
  obtain ⟨c', hc', hcb⟩ := T.exists_eq_diagonalBlockTernaryPoint hT hδ ℚ_[p]
    (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint ℚ_[p] b)
  rw [cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic,
    cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic,
    cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic, diagonalBlockSpinGroupMulEquiv_intrinsic, hca,
    hcb, diagonalBlockSpinMulEquiv_ternaryPoint_matrixPoint, diagonalBlockTernaryPoint_matrixPoint,
    diagonalBlockTernaryPoint_matrixPoint]
  have hT3 : ∀ {c : Fin 4 → ℚ_[p]} (hc : diagonalBlockNorm f ℚ_[p] c = 1),
      (∀ i j, upperLeftBlock (diagonalBlockConjMatrix f ℚ_[p] c c) i j ∈ PadicInt.subring p) ↔
        ∀ i j, diagonalBlockConjMatrix f ℚ_[p] c c i j ∈ PadicInt.subring p := by
    intro c hc
    conv_rhs => rw [T.diagonalBlockConjMatrix_self_eq_fixLast hT hδ ℚ_[p] hc]
    exact (fixLastBlockMatrix_entries_mem_iff _ _).symm
  rw [hT3 hc, hT3 hc', diagonalBlockConjMatrix_integral_iff p hf h2 hc hc',
    diagonalBlockConjMatrix_integral_iff p hf h2 hc hc, diagonalBlockConjMatrix_integral_iff p hf h2 hc' hc']
  tauto

end Integrality

/-! ## Matching integral loci at good places -/

section HeightOne

local instance diagonalBlockIntegralityPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

theorem heightOnePadicSpecialOrthogonal_inv_coe {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (g : V.HeightOnePadicCliffordSpinCandidateGroup v) :
    ((V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g).1.1⁻¹).1 =
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g⁻¹).1.1.1 := by
  rw [map_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Integrality of the special-orthogonal image of `g` is entrywise integrality of the images of
`g` and `g⁻¹`. -/
theorem pointMap_mem_heightOneIntegralSubgroup_iff {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (g : V.HeightOnePadicCliffordSpinCandidateGroup v) :
    V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g ∈
        V.heightOnePadicSpecialOrthogonalIntegralSubgroup v ↔
      (∀ i j, (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g).1.1.1
          i j ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
        (∀ i j, (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g⁻¹).1.1.1
          i j ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  rw [V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic, heightOnePadicSpecialOrthogonal_inv_coe]

/-- The integral loci match at every place off the lifting bad places of `T` and `U` where
`2, f₀, f₁, f₂` are units. -/
theorem diagonalBlock_heightOne_isIntegral_iff (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvT : v ∉ T.cliffordSpinCandidateIntegralLiftingBadPlaces)
    (hvU : v ∉ (UU).cliffordSpinCandidateIntegralLiftingBadPlaces)
    (hf : ∀ i, ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (f i)‖ = 1)
    (h2 : ‖(2 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖ = 1)
    (a b : T.HeightOnePadicCliffordSpinCandidateGroup v) :
    (UU).HeightOnePadicCliffordSpinCandidateIsIntegral v (T.diagonalBlockLocalEquiv hT hδ v (a, b)) ↔
      T.HeightOnePadicCliffordSpinCandidateIsIntegral v a ∧ T.HeightOnePadicCliffordSpinCandidateIsIntegral v b := by
  rw [(UU).heightOnePadicCliffordSpinCandidateIsIntegral_iff_pointMap_mem_integralSubgroup_of_not_mem_liftingBadPlaces
      v hvU,
    T.heightOnePadicCliffordSpinCandidateIsIntegral_iff_pointMap_mem_integralSubgroup_of_not_mem_liftingBadPlaces v hvT,
    T.heightOnePadicCliffordSpinCandidateIsIntegral_iff_pointMap_mem_integralSubgroup_of_not_mem_liftingBadPlaces v hvT,
    pointMap_mem_heightOneIntegralSubgroup_iff, pointMap_mem_heightOneIntegralSubgroup_iff,
    pointMap_mem_heightOneIntegralSubgroup_iff]
  have hinv : (T.diagonalBlockLocalEquiv hT hδ v (a, b))⁻¹ = T.diagonalBlockLocalEquiv hT hδ v (a⁻¹, b⁻¹) := by
    rw [← map_inv, Prod.inv_mk]
  rw [hinv]
  have h1 := T.diagonalBlock_matrix_integral_iff hT hδ (Rat.HeightOneSpectrum.primesEquiv v).1 hf h2 a b
  have h1' := T.diagonalBlock_matrix_integral_iff hT hδ (Rat.HeightOneSpectrum.primesEquiv v).1 hf h2 a⁻¹ b⁻¹
  exact (and_congr h1 h1').trans and_and_and_comm

end HeightOne

end RationalQuadraticSpaceMatrix
