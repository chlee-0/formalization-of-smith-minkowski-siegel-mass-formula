import SMSFormula.RationalCliffordSpinDiagonalBlockCayley
import SMSFormula.PadicSpinCayleyChartMass

/-!
# The local block measure identity at a finite place

At every prime `p`, the block isomorphism `Φ_p : Spin_T(ℚ_p)² ≃ₜ* Spin_U(ℚ_p)` carries
`μ_T ⊗ μ_T` to `c_p μ_U`.  Both sides are Haar; the constant is read off on the Clifford--Cayley
images of small balls, whose Spin masses are computed by the chart density, using the explicit
Cayley coordinates `X_T(u) = X(u, u)`, `X_U(u, v)`.
-/

noncomputable section

open MeasureTheory Topology PositiveDefiniteIntegralLattice Set Matrix
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

/-! ## Chart values -/

section ChartValue

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

set_option backward.isDefEq.respectTransparency false in
theorem isUnit_det_add_one_of_mem_padicSpecialOrthogonalCayleyIdentityChart_source
    {g : V.specialOrthogonalMatrixGroup ℚ_[p]} (hg : g ∈ (V.padicSpecialOrthogonalCayleyIdentityChart p).source) :
    IsUnit ((g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) + 1).det := by
  rw [V.padicSpecialOrthogonalCayleyIdentityChart_source] at hg
  have hdomain :=
    (mem_padicCayleySpecialOrthogonalTranslatedTarget_iff_inverseDomain
      V.pairingMatrix p 1 g).mp hg
  rw [← Matrix.isUnit_iff_isUnit_det]
  simpa [Matrix.padicCayleyInverseDomain] using hdomain

/-- The chart value of a Spin point whose matrix satisfies a Cayley identity. -/
theorem padicSkewAdjointIdentityChart_coe_eq_of_mul {x : V.PadicCliffordSpinCandidateGroup p}
    (hx : x ∈ (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source)
    {X : Matrix (Fin n) (Fin n) ℚ_[p]}
    (hM : (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x).1.1.1 * (1 - X) = 1 + X) :
    ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p x :
        (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
      Matrix (Fin n) (Fin n) ℚ_[p]) = X := by
  rw [padicCliffordSpinCandidateSkewAdjointIdentityChart, OpenPartialHomeomorph.trans_source] at hx
  have hxc : V.padicCliffordSpinCandidateIdentityChart p x ∈ (V.padicSpecialOrthogonalCayleyIdentityChart p).source :=
    hx.2
  have hπ : V.padicCliffordSpinCandidateIdentityChart p x = V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x :=
    (congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p) x).symm
  rw [padicCliffordSpinCandidateSkewAdjointIdentityChart, OpenPartialHomeomorph.trans_apply,
    V.padicSpecialOrthogonalCayleyIdentityChart_apply_coe p _ hxc, hπ]
  rw [hπ] at hxc
  exact cayleyInverse_eq_of_mul' ℚ_[p] hM
    (V.isUnit_det_add_one_of_mem_padicSpecialOrthogonalCayleyIdentityChart_source p hxc)

end ChartValue

/-! ## Coordinates of represented points -/

section PointCoordinates

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (A : Type*) [CommRing A] [Algebra ℚ A]

theorem cliffordSpinCandidateGroup_apply_cliffordCoordinate (F : V.CliffordSpinCandidateGroup A)
    (s : Finset (Fin n)) :
    F (V.cliffordSpinCandidateCliffordCoordinate s) =
      (V.cliffordCoordinateBaseChangeBasis A).repr (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F).1 s := by
  rw [cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_apply_coe,
    cliffordSpinCandidateElementOfCoordinateAlgHom_repr]

theorem cliffordSpinCandidateGroup_apply_matrixCoordinate (F : V.CliffordSpinCandidateGroup A) (i j : Fin n) :
    F (V.cliffordSpinCandidateMatrixCoordinate i j) =
      (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F).matrixPoint.1 i j := by
  rw [← cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply,
    ← cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic]
  change _ = (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).matrixGroup.1.1.1 i j
  rw [CliffordSpinCandidatePointData.matrixGroup_coe]

/-- Continuity at a point from continuity of all Clifford and matrix coordinates. -/
theorem continuousAt_cliffordSpinCandidateGroup_of_coordinates [TopologicalSpace A] {X : Type*}
    [TopologicalSpace X] {g : X → V.CliffordSpinCandidateGroup A} {x₀ : X}
    (hcl : ∀ s, ContinuousAt (fun x ↦ g x (V.cliffordSpinCandidateCliffordCoordinate s)) x₀)
    (hmat : ∀ i j, ContinuousAt (fun x ↦ g x (V.cliffordSpinCandidateMatrixCoordinate i j)) x₀) :
    ContinuousAt g x₀ := by
  rw [(V.cliffordSpinCandidatePointCoordinateMap_isEmbedding A).continuousAt_iff]
  exact ContinuousAt.prodMk (continuousAt_pi.2 hcl) (continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ hmat i j)

end PointCoordinates

/-! ## Cayley points on the represented groups -/

section CayleyPoints

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (K : Type*) [NormedField K] [Algebra ℚ K]

open Classical in
/-- The ternary Cayley point `κ(u) = (1 + u)(1 − u)⁻¹` (identity off the Cayley domain). -/
def ternaryCayleyPoint (u : Fin 3 → K) : T.CliffordSpinCandidateGroup K :=
  if hu : 1 + blockPureNorm f K u ≠ 0 then
    (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint K).symm
      (T.diagonalBlockTernaryPoint hT hδ K (blockCayleyCoords_norm K hu))
  else 1

theorem ternaryCayleyPoint_intrinsic {u : Fin 3 → K} (hu : 1 + blockPureNorm f K u ≠ 0) :
    T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint K (T.ternaryCayleyPoint hT hδ K u) =
      T.diagonalBlockTernaryPoint hT hδ K (blockCayleyCoords_norm K hu) := by
  rw [ternaryCayleyPoint, dif_pos hu, MulEquiv.apply_symm_apply]

theorem ternaryCayleyPoint_matrix {u : Fin 3 → K} (hu : 1 + blockPureNorm f K u ≠ 0) :
    (T.cliffordSpinCandidateGroupToSpecialOrthogonal K (T.ternaryCayleyPoint hT hδ K u)).1.1.1 =
      upperLeftBlock (diagonalBlockConjMatrix f K (blockCayleyCoords f K u) (blockCayleyCoords f K u)) := by
  rw [cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic, T.ternaryCayleyPoint_intrinsic hT hδ K hu,
    diagonalBlockTernaryPoint_matrixPoint]

/-- The block Cayley point `Φ(κ(u), κ(v))`. -/
def blockCayleyPoint (u v : Fin 3 → K) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup K :=
  T.diagonalBlockSpinGroupMulEquiv hT hδ K (T.ternaryCayleyPoint hT hδ K u, T.ternaryCayleyPoint hT hδ K v)

theorem blockCayleyPoint_matrix {u v : Fin 3 → K} (hu : 1 + blockPureNorm f K u ≠ 0)
    (hv : 1 + blockPureNorm f K v ≠ 0) :
    ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateGroupToSpecialOrthogonal K
        (T.blockCayleyPoint hT hδ K u v)).1.1.1 =
      diagonalBlockConjMatrix f K (blockCayleyCoords f K u) (blockCayleyCoords f K v) := by
  rw [cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic, blockCayleyPoint,
    diagonalBlockSpinGroupMulEquiv_intrinsic, T.ternaryCayleyPoint_intrinsic hT hδ K hu,
    T.ternaryCayleyPoint_intrinsic hT hδ K hv, diagonalBlockSpinMulEquiv_ternaryPoint_matrixPoint]

theorem blockPureNorm_zero : blockPureNorm f K 0 = 0 := by
  simp [blockPureNorm, BlockConjugationCoordinates.pureNorm]

theorem ternaryCayleyPoint_zero : T.ternaryCayleyPoint hT hδ K 0 = 1 := by
  have hu : 1 + blockPureNorm f K 0 ≠ 0 := by rw [blockPureNorm_zero]; simp
  apply (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint K).injective
  rw [T.ternaryCayleyPoint_intrinsic hT hδ K hu, map_one]
  apply CliffordSpinIntrinsicPoint.ext
  rw [CliffordSpinIntrinsicPoint.one_coe]
  apply (T.commutativeTensorCliffordEquiv K).injective
  rw [commutativeTensorCliffordEquiv_diagonalBlockTernaryPoint, map_one]
  have hc : blockCayleyCoords f K 0 = ![1, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [blockCayleyCoords, BlockConjugationCoordinates.cayleyCoords,
      BlockConjugationCoordinates.cayleyNum, BlockConjugationCoordinates.pureNorm]
  rw [hc, CliffordAlgebra.OrthogonalTriple.evenElem_single_zero, map_one]

theorem blockCayleyPoint_zero : T.blockCayleyPoint hT hδ K 0 0 = 1 := by
  rw [blockCayleyPoint, T.ternaryCayleyPoint_zero hT hδ K]
  exact map_one (T.diagonalBlockSpinGroupMulEquiv hT hδ K)

theorem ternary_evenElem_eq_sum (c : Fin 4 → K) :
    CliffordAlgebra.OrthogonalTriple.evenElem (T.commutativeScalarExtensionQuadraticForm K) (stdVec 3 K) c =
      ∑ k, c k • CliffordAlgebra.OrthogonalTriple.evenElem (T.commutativeScalarExtensionQuadraticForm K)
        (stdVec 3 K) (Pi.single k 1) := by
  simp only [CliffordAlgebra.OrthogonalTriple.evenElem, Fin.sum_univ_four, Algebra.algebraMap_eq_smul_one]
  simp

theorem continuous_pureNorm (a0 a1 a2 : K) :
    Continuous fun u : Fin 3 → K ↦ BlockConjugationCoordinates.pureNorm a0 a1 a2 u := by
  unfold BlockConjugationCoordinates.pureNorm
  fun_prop

theorem continuous_blockPureNorm : Continuous fun u : Fin 3 → K ↦ blockPureNorm f K u :=
  continuous_pureNorm K _ _ _

theorem eventually_blockPureNorm_ne : ∀ᶠ u in 𝓝 (0 : Fin 3 → K), 1 + blockPureNorm f K u ≠ 0 := by
  have h : ContinuousAt (fun u : Fin 3 → K ↦ 1 + blockPureNorm f K u) 0 :=
    (continuous_const.add (continuous_blockPureNorm (f := f) K)).continuousAt
  refine h.eventually_ne ?_
  simp [blockPureNorm_zero]

theorem continuousAt_blockCayleyCoords : ContinuousAt (blockCayleyCoords f K) 0 := by
  unfold blockCayleyCoords BlockConjugationCoordinates.cayleyCoords
  refine ContinuousAt.smul ?_ ?_
  · refine ((continuous_const.add (continuous_blockPureNorm (f := f) K)).continuousAt).inv₀ ?_
    simp [blockPureNorm_zero]
  · refine Continuous.continuousAt (continuous_pi fun i ↦ ?_)
    have hN := continuous_blockPureNorm (f := f) K
    fin_cases i <;> simp only [BlockConjugationCoordinates.cayleyNum, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    · exact continuous_const.sub hN
    all_goals fun_prop

theorem continuous_qmul_left (a0 a1 a2 : K) (k : Fin 4 → K) :
    Continuous fun h : Fin 4 → K ↦ BlockConjugationCoordinates.qmul a0 a1 a2 h k := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [BlockConjugationCoordinates.qmul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop

theorem continuous_qmul_right (a0 a1 a2 : K) (h : Fin 4 → K) :
    Continuous fun k : Fin 4 → K ↦ BlockConjugationCoordinates.qmul a0 a1 a2 h k := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [BlockConjugationCoordinates.qmul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop

theorem continuous_lmat (a0 a1 a2 : K) : Continuous fun c : Fin 4 → K ↦ BlockConjugationCoordinates.lmat a0 a1 a2 c :=
  continuous_pi fun i ↦ continuous_pi fun _j ↦ (continuous_apply i).comp (continuous_qmul_left K a0 a1 a2 _)

theorem continuous_rmat (a0 a1 a2 : K) : Continuous fun c : Fin 4 → K ↦ BlockConjugationCoordinates.rmat a0 a1 a2 c :=
  continuous_pi fun i ↦ continuous_pi fun _j ↦ (continuous_apply i).comp (continuous_qmul_right K a0 a1 a2 _)

theorem continuous_qconj : Continuous fun c : Fin 4 → K ↦ BlockConjugationCoordinates.qconj c := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [BlockConjugationCoordinates.qconj, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop

theorem continuous_diagonalBlockConjMatrix :
    Continuous fun p : (Fin 4 → K) × (Fin 4 → K) ↦ diagonalBlockConjMatrix f K p.1 p.2 := by
  unfold diagonalBlockConjMatrix BlockConjugationCoordinates.conjMatrix
  refine Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) ?_) continuous_const
  · exact (continuous_rmat K _ _ _).comp ((continuous_qconj K).comp continuous_snd)
  · exact (continuous_lmat K _ _ _).comp continuous_fst

/-- The ternary Cayley point is continuous at the origin. -/
theorem continuousAt_ternaryCayleyPoint : ContinuousAt (T.ternaryCayleyPoint hT hδ K) 0 := by
  have hκ := continuousAt_blockCayleyCoords (f := f) K
  apply T.continuousAt_cliffordSpinCandidateGroup_of_coordinates K
  · intro s
    let G : (Fin 4 → K) → K := fun c ↦ (T.cliffordCoordinateBaseChangeBasis K).repr
      ((T.commutativeTensorCliffordEquiv K).symm
        (CliffordAlgebra.OrthogonalTriple.evenElem (T.commutativeScalarExtensionQuadraticForm K) (stdVec 3 K) c)) s
    have hG : Continuous G := by
      have hsum : G = fun c ↦ ∑ k, c k * G (Pi.single k 1) := by
        funext c
        simp only [G]
        rw [T.ternary_evenElem_eq_sum K c]
        simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      rw [hsum]
      fun_prop
    refine (hG.continuousAt.comp hκ).congr ?_
    filter_upwards [eventually_blockPureNorm_ne (f := f) K] with u hu
    simp only [Function.comp_apply, G]
    rw [cliffordSpinCandidateGroup_apply_cliffordCoordinate, T.ternaryCayleyPoint_intrinsic hT hδ K hu]
    rfl
  · intro i j
    have hM : ContinuousAt (fun u : Fin 3 → K ↦
        upperLeftBlock (diagonalBlockConjMatrix f K (blockCayleyCoords f K u) (blockCayleyCoords f K u)) i j) 0 := by
      have h := (continuous_diagonalBlockConjMatrix (f := f) K).continuousAt.comp (hκ.prodMk hκ)
      exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.comp
        (ContinuousAt.comp (g := fun M : Matrix (Fin 4) (Fin 4) K ↦ upperLeftBlock M)
          (Continuous.continuousAt (continuous_pi fun a ↦ continuous_pi fun b ↦
            (continuous_apply (Fin.castSucc b)).comp (continuous_apply (Fin.castSucc a)))) h)
    refine hM.congr ?_
    filter_upwards [eventually_blockPureNorm_ne (f := f) K] with u hu
    rw [cliffordSpinCandidateGroup_apply_matrixCoordinate, T.ternaryCayleyPoint_intrinsic hT hδ K hu,
      diagonalBlockTernaryPoint_matrixPoint]

theorem continuousAt_blockCayleyPoint :
    ContinuousAt (fun w : (Fin 3 → K) × (Fin 3 → K) ↦ T.blockCayleyPoint hT hδ K w.1 w.2) 0 := by
  have h1 : ContinuousAt (fun w : (Fin 3 → K) × (Fin 3 → K) ↦ T.ternaryCayleyPoint hT hδ K w.1) 0 :=
    (T.continuousAt_ternaryCayleyPoint hT hδ K).comp_of_eq continuous_fst.continuousAt rfl
  have h2 : ContinuousAt (fun w : (Fin 3 → K) × (Fin 3 → K) ↦ T.ternaryCayleyPoint hT hδ K w.2) 0 :=
    (T.continuousAt_ternaryCayleyPoint hT hδ K).comp_of_eq continuous_snd.continuousAt rfl
  exact (T.continuous_diagonalBlockSpinGroupMulEquiv hT hδ K).continuousAt.comp (h1.prodMk h2)

end CayleyPoints

end RationalQuadraticSpaceMatrix
