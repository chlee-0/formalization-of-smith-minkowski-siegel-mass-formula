import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionGeneration
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRangeGoodPlace
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization

/-!
# The original integral special-orthogonal matrix as a recursive form isometry

At a certified odd-unimodular place, the displayed integral Gram matrix is a
`LocalPadicIntegralUnimodularForm`.  An integral point of the original local
special-orthogonal group has a literal matrix over `Z_p`; this file packages
that matrix as an integral general-linear element, proves that it preserves
the certified Gram matrix, and applies the completed reflection-generation
theorem.

No field reflection word, spinor norm, integral Spin lifting, covering-degree
argument, or Haar comparison is used here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

/-- An invertible integral matrix preserving the displayed Gram matrix acts
as a quadratic self-isometry of the recursive unimodular-form carrier. -/
def LocalPadicIntegralUnimodularForm.isometryEquivOfGeneralLinear
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (g : GL (Fin U.rank) ℤ_[p])
    (hform : g.1ᵀ * U.pairingMatrix * g.1 = U.pairingMatrix) :
    U.quadraticForm.IsometryEquiv U.quadraticForm where
  toLinearEquiv := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  map_app' x := by
    rw [U.quadraticForm_apply, U.quadraticForm_apply]
    change
      dotProduct (g.1.mulVec x)
          (U.pairingMatrix.mulVec (g.1.mulVec x)) =
        dotProduct x (U.pairingMatrix.mulVec x)
    exact dotProduct_mulVec_eq_of_matrix_conj hform x x

@[simp]
theorem LocalPadicIntegralUnimodularForm.isometryEquivOfGeneralLinear_toMatrix'
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (g : GL (Fin U.rank) ℤ_[p])
    (hform : g.1ᵀ * U.pairingMatrix * g.1 = U.pairingMatrix) :
    LinearMap.toMatrix'
        (U.isometryEquivOfGeneralLinear g hform).toLinearEquiv.toLinearMap =
      g.1 := by
  change LinearMap.toMatrix' (Matrix.toLin' g.1) = g.1
  exact LinearMap.toMatrix'_toLin' _

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance integralOriginalMatrixCarrierPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The integral Gram matrix in the good-place certificate, packaged as the
recursive symmetric unimodular form carrier. -/
def CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unimodularForm
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v) :
    LocalPadicIntegralUnimodularForm
      (Rat.HeightOneSpectrum.primesEquiv v).1 where
  rank := n
  pairingMatrix := P.integralFormMatrix
  pairingMatrix_isSymm := P.integralFormMatrix_isSymm
  pairingMatrix_det_isUnit := P.integralFormMatrix_det_isUnit

@[simp]
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unimodularForm_rank
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v) :
    P.unimodularForm.rank = n :=
  rfl

@[simp]
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unimodularForm_pairingMatrix
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v) :
    P.unimodularForm.pairingMatrix = P.integralFormMatrix :=
  rfl

private theorem coe_padicInt_matrix_mul_apply_original
    (p : ℕ) [Fact p.Prime]
    (A B : Matrix (Fin n) (Fin n) ℤ_[p]) (i j : Fin n) :
    (((A * B) i j : ℤ_[p]) : ℚ_[p]) =
      ∑ k, (A i k : ℚ_[p]) * (B k j : ℚ_[p]) := by
  change PadicInt.Coe.ringHom (∑ k, A i k * B k j) = _
  rw [map_sum]
  rfl

/-- The literal integral matrix and inverse matrix of a point in the
height-one integral special-orthogonal subgroup. -/
def heightOnePadicSpecialOrthogonalIntegralGL
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    GL (Fin n) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1] := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  have hg :=
    (V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic
      v g.1).1 g.2
  exact
    { val := fun i j ↦ ⟨g.1.1.1.1 i j, hg.1 i j⟩
      inv := fun i j ↦ ⟨(g.1.1.1⁻¹).1 i j, hg.2 i j⟩
      val_inv := by
        apply Matrix.ext
        intro i j
        apply PadicInt.ext
        rw [coe_padicInt_matrix_mul_apply_original]
        calc
          _ = (g.1.1.1.1 * (g.1.1.1⁻¹).1) i j := rfl
          _ = (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j :=
            congr_fun (congr_fun g.1.1.1.val_inv i) j
          _ = ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) := by
            by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      inv_val := by
        apply Matrix.ext
        intro i j
        apply PadicInt.ext
        rw [coe_padicInt_matrix_mul_apply_original]
        calc
          _ = ((g.1.1.1⁻¹).1 * g.1.1.1.1) i j := rfl
          _ = (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j :=
            congr_fun (congr_fun g.1.1.1.inv_val i) j
          _ = ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) := by
            by_cases hij : i = j <;> simp [Matrix.one_apply, hij] }

@[simp]
theorem coe_heightOnePadicSpecialOrthogonalIntegralGL_apply
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v)
    (i j : Fin n) :
    ((V.heightOnePadicSpecialOrthogonalIntegralGL g i j :
        ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
        g.1.1.1.1 i j :=
  rfl

@[simp]
theorem heightOnePadicSpecialOrthogonalIntegralGL_map
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    (V.heightOnePadicSpecialOrthogonalIntegralGL g).1.map
        PadicInt.Coe.ringHom = g.1.1.1.1 := by
  ext i j
  rfl

/-- The integral matrix of an integral special-orthogonal point preserves the
certified integral Gram matrix. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralGL_preserves_form
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    (V.heightOnePadicSpecialOrthogonalIntegralGL g).1ᵀ *
        P.integralFormMatrix *
        (V.heightOnePadicSpecialOrthogonalIntegralGL g).1 =
      P.integralFormMatrix := by
  apply Matrix.ext
  intro i j
  apply PadicInt.ext
  have hmap :
      (((V.heightOnePadicSpecialOrthogonalIntegralGL g).1ᵀ *
          P.integralFormMatrix *
          (V.heightOnePadicSpecialOrthogonalIntegralGL g).1).map
            PadicInt.Coe.ringHom) =
        P.integralFormMatrix.map PadicInt.Coe.ringHom := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      V.heightOnePadicSpecialOrthogonalIntegralGL_map,
      P.integralFormMatrix_map]
    exact g.1.1.2
  exact congr_fun (congr_fun hmap i) j

/-- The integral matrix of an integral special-orthogonal point, acting as a
quadratic self-isometry of the certified recursive carrier. -/
def CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    P.unimodularForm.quadraticForm.IsometryEquiv
      P.unimodularForm.quadraticForm := by
  let U := P.unimodularForm
  let G := V.heightOnePadicSpecialOrthogonalIntegralGL g
  exact U.isometryEquivOfGeneralLinear G (by
    exact
      CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralGL_preserves_form
        V P g)

@[simp]
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry_toMatrix'
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    LinearMap.toMatrix'
        (CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry
          V P g).toLinearEquiv.toLinearMap =
      (V.heightOnePadicSpecialOrthogonalIntegralGL g).1 := by
  exact
    LocalPadicIntegralUnimodularForm.isometryEquivOfGeneralLinear_toMatrix'
      P.unimodularForm (V.heightOnePadicSpecialOrthogonalIntegralGL g)
        (CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralGL_preserves_form
          V P g)

/-- The completed integral Cartan--Dieudonne induction applied to the
original integral special-orthogonal matrix. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.exists_unitReflectionWord_eval_eq
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    ∃ xs : P.unimodularForm.UnitReflectionWord,
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
          P.unimodularForm xs =
            CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry
              V P g ∧
        xs.length ≤ 2 * n := by
  simpa using
    P.unimodularForm.exists_unitReflectionWord_eval_eq
      P.prime_ne_two
        (CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry
          V P g)

end RationalQuadraticSpaceMatrix
