import SMSFormula.RationalCliffordGeneralSpinRankOneThetaCoefficientExtraction
import SMSFormula.RationalAdeleVectorPolarThetaSpecialization
import SMSFormula.AdelicFinitePresentation

/-!
# Summability of the polar Gaussian--lattice theta family

The concrete polar Gaussian times the standard finite integral-lattice
indicator is summable on rational vectors after the actual inverse adelic
`GSpin` action.  The finite component cuts the rational vectors down to the
already constructed attached rational lattice.  Its existing integral basis
turns the real Gaussian into the positive-definite matrix Gaussian of the
attached integral lattice.

No Schwartz space, surrogate test class, quotient section, complement,
presentation family, or Weil representation is introduced.
-/

noncomputable section

open Matrix Set
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The real component of a full-adelic orthogonal action on a rational
diagonal vector is the corresponding real matrix action. -/
theorem rationalAdeleVectorRealPart_fullAdelicSpecialOrthogonal_mulVec_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n)
    (h : V.FullAdelicSpecialOrthogonalGroup) (x : Fin n → ℚ) :
    rationalAdeleVectorRealPart n
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) =
      ((V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1.1.1.1).mulVec
        (rationalRealVector n x) := by
  ext i
  rw [V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_real_matrix]
  simp only [rationalAdeleVectorRealPart, Matrix.mulVec, dotProduct,
    rationalAdeleVectorDiagonal, rationalRealVector]
  change rationalInfiniteAdeleRingEquivReal
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
        (∑ j, h.1.1.1 i j * algebraMap ℚ RationalAdele (x j))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  let φ : RationalAdele →+* ℝ :=
    rationalInfiniteAdeleRingEquivReal.toRingHom.comp
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
  change φ (h.1.1.1 i j * algebraMap ℚ RationalAdele (x j)) =
    φ (h.1.1.1 i j) * (x j : ℝ)
  rw [φ.map_mul]
  congr 1
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (φ.comp (algebraMap ℚ RationalAdele))
      (algebraMap ℚ ℝ)) (x j)

/-- The finite component of a full-adelic orthogonal action on a rational
diagonal vector is the corresponding finite matrix action. -/
theorem rationalAdeleVectorFinitePart_fullAdelicSpecialOrthogonal_mulVec_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n)
    (h : V.FullAdelicSpecialOrthogonalGroup) (x : Fin n → ℚ) :
    rationalAdeleVectorFinitePart n
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) =
      ((V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1).mulVec
        (rationalVectorFiniteAdele x) := by
  ext i v
  rw [V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_finite_matrix]
  simp only [rationalAdeleVectorFinitePart, Matrix.mulVec, dotProduct,
    rationalAdeleVectorDiagonal, rationalVectorFiniteAdele]
  change ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
      (∑ j, h.1.1.1 i j * algebraMap ℚ RationalAdele (x j))) v = _
  rw [map_sum]
  refine congrArg (fun z : RationalFiniteAdele ↦ z v) ?_
  apply Finset.sum_congr rfl
  intro j _hj
  rfl

/-- The real polar matrix is twice the real quadratic-form matrix. -/
theorem realPolarMatrix_eq_two_smul_realFormMatrix
    (V : RationalQuadraticSpaceMatrix n) :
    V.realPolarMatrix = (2 : ℝ) • V.realFormMatrix := by
  ext i j
  simp [realPolarMatrix, realFormMatrix, polarMatrix]

/-- A real special-orthogonal element preserves the polar Gaussian. -/
theorem polarRealGaussian_realSpecialOrthogonal
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (h : L.rationalQuadraticSpaceMatrix.RealSpecialOrthogonalGroup)
    (x : Fin n → ℝ) :
    polarRealGaussian L b (h.1.1.1.mulVec x) =
      polarRealGaussian L b x := by
  unfold polarRealGaussian
  rw [realCoordinateGaussian_eq_exp_dotProduct,
    realCoordinateGaussian_eq_exp_dotProduct,
    L.dotProduct_polarRealSqrtMatrix_mulVec,
    L.dotProduct_polarRealSqrtMatrix_mulVec]
  have hconj : h.1.1.1.transpose *
      L.rationalQuadraticSpaceMatrix.realPolarMatrix * h.1.1.1 =
        L.rationalQuadraticSpaceMatrix.realPolarMatrix := by
    rw [realPolarMatrix_eq_two_smul_realFormMatrix]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [h.1.2]
  rw [dotProduct_mulVec_eq_of_matrix_conj hconj x x]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Forget the determinant-one condition on the finite component of the
lattice's rational quadratic-space presentation and view the same matrix in
the concrete finite orthogonal carrier. -/
def concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.finiteAdelicOrthogonalMatrixSubgroup) :
    L.ConcreteFiniteAdelicOrthogonalGroup :=
  ⟨g.1, by
    rw [L.mem_finiteAdelicOrthogonalMatrixSubgroup_iff,
      L.finiteAdelicFormMatrix_eq_map_rationalFormMatrix]
    exact g.2⟩

@[simp]
theorem concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix_apply_matrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.finiteAdelicOrthogonalMatrixSubgroup) :
    (L.concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix g).1.1 =
      g.1.1 :=
  rfl

/-- Integral basis coordinates of the attached rational lattice, viewed in
the ambient rational coordinate space. -/
noncomputable def concreteAttachedRationalLatticeCoordinateEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (Fin n → ℤ) ≃ L.concreteAttachedRationalLatticeSubmodule g :=
  (L.concreteAttachedRationalLatticeBasis g).equivFun.symm.toEquiv

/-- The ambient value of attached-lattice basis coordinates is multiplication
by the existing rational basis matrix. -/
theorem concreteAttachedRationalLatticeCoordinateEquiv_apply_val
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) (z : Fin n → ℤ) :
    ((L.concreteAttachedRationalLatticeCoordinateEquiv g z :
        L.concreteAttachedRationalLatticeSubmodule g) : Fin n → ℚ) =
      (L.concreteAttachedRationalLatticeBasisMatrixRat g).mulVec
        (fun i ↦ (z i : ℚ)) := by
  ext i
  change (((↑((L.concreteAttachedRationalLatticeBasis g).equivFun.symm z) :
    Fin n → ℚ)) i) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _hj
  change (z j : ℚ) *
      (L.concreteAttachedRationalLatticeBasis g j).1 i =
    L.concreteAttachedRationalLatticeBasisMatrixRat g i j * (z j : ℚ)
  rw [← congr_fun (L.concreteAttachedRationalLatticeBasisMatrixRat_col g j) i]
  simp [mul_comm]

/-- Real polar matrices of an attached lattice are related to the ambient
polar matrix by the existing rational basis congruence. -/
theorem concreteAttachedIntegralLattice_realPolarMatrix_eq_conj
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedIntegralLattice g).rationalQuadraticSpaceMatrix.realPolarMatrix =
      ((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
          (Rat.castHom ℝ)).transpose *
        L.rationalQuadraticSpaceMatrix.realPolarMatrix *
          (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
            (Rat.castHom ℝ) := by
  rw [RationalQuadraticSpaceMatrix.realPolarMatrix_eq_two_smul_realFormMatrix,
    RationalQuadraticSpaceMatrix.realPolarMatrix_eq_two_smul_realFormMatrix]
  have hq := L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
  have hr' :
      (L.concreteAttachedIntegralLattice g).rationalQuadraticSpaceMatrix.realFormMatrix =
        ((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
            (Rat.castHom ℝ)).transpose *
          L.rationalQuadraticSpaceMatrix.realFormMatrix *
            (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
              (Rat.castHom ℝ) := by
    ext i j
    change ((L.concreteAttachedRationalLatticeFormMatrix g i j : ℤ) : ℝ) = _
    have hij := congr_fun (congr_fun hq i) j
    have hijR := congrArg (fun q : ℚ ↦ (q : ℝ)) hij
    simpa [Matrix.mul_apply] using hijR
  rw [hr']
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- In attached-lattice basis coordinates, the ambient polar Gaussian is the
standard positive-definite matrix Gaussian of the attached integral lattice. -/
theorem polarRealGaussian_concreteAttachedRationalLatticeCoordinateEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) (a : ℝ)
    (z : Fin n → ℤ) :
    polarRealGaussian L (a : ℂ)
        (rationalRealVector n
          (L.concreteAttachedRationalLatticeCoordinateEquiv g z).1) =
      shiftedMatrixGaussianSummand
        (L.concreteAttachedIntegralLattice g).rationalQuadraticSpaceMatrix.realPolarMatrix
        (a : ℂ) 0 z := by
  rw [polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct,
    shiftedMatrixGaussianSummand,
    L.dotProduct_polarRealSqrtMatrix_mulVec]
  rw [L.concreteAttachedIntegralLattice_realPolarMatrix_eq_conj g]
  have hx : rationalRealVector n
      (L.concreteAttachedRationalLatticeCoordinateEquiv g z).1 =
      ((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
        (Rat.castHom ℝ)).mulVec (integerVectorReal z) := by
    rw [L.concreteAttachedRationalLatticeCoordinateEquiv_apply_val]
    ext i
    simp [rationalRealVector, integerVectorReal, Matrix.mulVec, dotProduct]
  let P := (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
    (Rat.castHom ℝ)
  let C := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  let zR := integerVectorReal z
  have hquad :
      dotProduct (P.mulVec zR) (C.mulVec (P.mulVec zR)) =
        dotProduct zR ((P.transpose * C * P).mulVec zR) := by
    symm
    calc
      dotProduct zR ((P.transpose * C * P).mulVec zR) =
        (zR ᵥ* (P.transpose * C * P)) ⬝ᵥ zR := by
          rw [Matrix.dotProduct_mulVec]
      _ = (((zR ᵥ* P.transpose) ᵥ* C) ᵥ* P) ⬝ᵥ zR := by
          simp [Matrix.mul_assoc]
      _ = ((P *ᵥ zR) ᵥ* C) ⬝ᵥ (P *ᵥ zR) := by
          rw [← Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = dotProduct (P.mulVec zR) (C.mulVec (P.mulVec zR)) := by
          exact (Matrix.dotProduct_mulVec (P *ᵥ zR) C (P *ᵥ zR)).symm
  have hquad' :
      dotProduct
          (((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
            (Rat.castHom ℝ)).mulVec (integerVectorReal z))
          (L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec
            (((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
              (Rat.castHom ℝ)).mulVec (integerVectorReal z))) =
        dotProduct (integerVectorReal z)
          ((((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
            (Rat.castHom ℝ)).transpose *
              L.rationalQuadraticSpaceMatrix.realPolarMatrix *
                (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
                  (Rat.castHom ℝ)).mulVec (integerVectorReal z)) := by
    simpa [P, C, zR] using hquad
  rw [hx, hquad']
  simp

/-! ## Summability after the actual inverse `GSpin` action -/

/-- Outside the rational lattice attached to the inverse finite orthogonal
component, the concrete Gaussian--lattice summand vanishes. -/
theorem rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin_eq_zero_of_not_mem
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (x : Fin n → ℚ)
    (hx : x ∉ L.concreteAttachedRationalLatticeSubmodule
      (L.concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix
        ((L.rationalQuadraticSpaceMatrix
          |>.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
            g.matrixGroup⁻¹).2.1⁻¹))) :
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (L.rationalQuadraticSpaceMatrix
          |>.fullAdelicCliffordGeneralSpinRationalVectorAction g x) = 0 := by
  let V := L.rationalQuadraticSpaceMatrix
  let h : V.FullAdelicSpecialOrthogonalGroup := g.matrixGroup⁻¹
  let hf := (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2
  let gf : L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix hf.1⁻¹
  rw [rationalAdeleVectorPolarGaussianLatticeTest]
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem]
  · simp
  · intro hint
    apply hx
    have hfin :=
      V.rationalAdeleVectorFinitePart_fullAdelicSpecialOrthogonal_mulVec_rationalDiagonal
        h x
    change rationalAdeleVectorFinitePart n
        (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x) ∈
          integralFiniteAdeleVectors n at hint
    change rationalAdeleVectorFinitePart n
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) ∈
          integralFiniteAdeleVectors n at hint
    rw [hfin] at hint
    change x ∈ L.concreteAttachedRationalLatticeSubmodule gf
    rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff]
    have hgf : (gf.1⁻¹).1 = hf.1.1 := by
      change (((hf.1⁻¹)⁻¹).1 :
        Matrix (Fin n) (Fin n) RationalFiniteAdele) = hf.1.1
      simp
    rw [hgf]
    exact hint

/-- On its attached rational lattice, the concrete adelic summand is exactly
the ambient real polar Gaussian. -/
theorem rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin_of_mem
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (x : Fin n → ℚ)
    (hx : x ∈ L.concreteAttachedRationalLatticeSubmodule
      (L.concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix
        ((L.rationalQuadraticSpaceMatrix
          |>.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
            g.matrixGroup⁻¹).2.1⁻¹))) :
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (L.rationalQuadraticSpaceMatrix
          |>.fullAdelicCliffordGeneralSpinRationalVectorAction g x) =
      polarRealGaussian L (a : ℂ) (rationalRealVector n x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let h : V.FullAdelicSpecialOrthogonalGroup := g.matrixGroup⁻¹
  let hr := (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1
  let hf := (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2
  let gf : L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix hf.1⁻¹
  rw [rationalAdeleVectorPolarGaussianLatticeTest]
  have hreal :=
    V.rationalAdeleVectorRealPart_fullAdelicSpecialOrthogonal_mulVec_rationalDiagonal
      h x
  have hfin :=
    V.rationalAdeleVectorFinitePart_fullAdelicSpecialOrthogonal_mulVec_rationalDiagonal
      h x
  change rationalAdeleVectorRealPart n
      (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) = _ at hreal
  change rationalAdeleVectorFinitePart n
      (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) = _ at hfin
  change polarRealGaussian L (a : ℂ)
      (rationalAdeleVectorRealPart n
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x))) *
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
        (rationalAdeleVectorFinitePart n
          (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n x))) = _
  rw [hreal, hfin]
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem]
  · rw [mul_one]
    exact RationalQuadraticSpaceMatrix.polarRealGaussian_realSpecialOrthogonal
      L (a : ℂ) hr (rationalRealVector n x)
  · rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff] at hx
    have hgf : (gf.1⁻¹).1 = hf.1.1 := by
      change (((hf.1⁻¹)⁻¹).1 :
        Matrix (Fin n) (Fin n) RationalFiniteAdele) = hf.1.1
      simp
    rw [hgf] at hx
    exact hx

/-- For every positive real scale, the polar Gaussian--lattice test
is summable on all rational vectors after the inverse full-adelic
`GSpin` action. -/
theorem summable_rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Summable (fun x : Fin n → ℚ ↦
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (L.rationalQuadraticSpaceMatrix
          |>.fullAdelicCliffordGeneralSpinRationalVectorAction g x)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let h : V.FullAdelicSpecialOrthogonalGroup := g.matrixGroup⁻¹
  let hf := (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2
  let gf : L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.concreteFiniteAdelicOrthogonalOfRationalQuadraticSpaceMatrix hf.1⁻¹
  let M := L.concreteAttachedRationalLatticeSubmodule gf
  let e : (Fin n → ℤ) ≃ M :=
    L.concreteAttachedRationalLatticeCoordinateEquiv gf
  let f : (Fin n → ℚ) → ℂ := fun x ↦
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
      (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x)
  have hcoord : Summable ((fun x : M ↦ f x.1) ∘ e) := by
    have hgauss :=
      summable_shiftedMatrixGaussianSummand_zero_fintype
        (L.concreteAttachedIntegralLattice gf).rationalQuadraticSpaceMatrix.realPolarMatrix
        (L.concreteAttachedIntegralLattice gf
          |>.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef) ha
    apply hgauss.congr
    intro z
    change shiftedMatrixGaussianSummand
        (L.concreteAttachedIntegralLattice gf).rationalQuadraticSpaceMatrix.realPolarMatrix
          (a : ℂ) 0 z = f (e z).1
    symm
    rw [show f (e z).1 =
        polarRealGaussian L (a : ℂ) (rationalRealVector n (e z).1) by
      exact
        L.rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin_of_mem
          a g (e z).1 (e z).property]
    exact L.polarRealGaussian_concreteAttachedRationalLatticeCoordinateEquiv
      gf a z
  have hM : Summable (fun x : M ↦ f x.1) := by
    exact e.summable_iff.mp hcoord
  have hzero : ∀ x ∉ Set.range (fun y : M ↦ y.1), f x = 0 := by
    intro x hxrange
    have hxM : x ∉ M := by
      intro hx
      exact hxrange ⟨⟨x, hx⟩, rfl⟩
    exact
      L.rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin_eq_zero_of_not_mem
        a g x hxM
  exact (Subtype.val_injective.summable_iff hzero).mp (by
    simpa [Function.comp_def] using hM)

/-- The concrete polar Gaussian--lattice family satisfies the existing
section-free quotient summability predicate at every quotient point. -/
theorem isSummableFullAdelicCliffordGeneralSpinPolarGaussianLatticeTestAtQuotient
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (Z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    L.rationalQuadraticSpaceMatrix
      |>.IsSummableFullAdelicCliffordGeneralSpinComplexThetaAtQuotient
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) Z := by
  induction Z using Quot.inductionOn with
  | _ g =>
      exact
        L.summable_rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin
          ha g

end PositiveDefiniteIntegralLattice
