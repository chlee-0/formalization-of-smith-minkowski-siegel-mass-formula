import SMSFormula.RationalCliffordSpinCandidateIntegralShellAlignment
import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSimilitude
import SMSFormula.RationalSpecialOrthogonalSpinorNorm

/-!
# Integral intrinsic GSpin lift of a local shell alignment

The determinant-corrected two-reflection word from the integral shell
alignment is packaged here as an actual intrinsic `GSpin` point.  Its
integral word evaluation first gives a general-linear matrix over `Z_p`.
After scalar extension this matrix is literally the represented `SO` matrix,
so both the matrix and its inverse are integral without a cofactor or
denominator calculation.  The existing integral reflection-pair constructor
then supplies the required integral intrinsic `GSpin` point.

This is a local theorem.  No finite-adelic assembly, cutoff, measure, or
Fourier statement occurs here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open QuadraticMap.ReflectionWord
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance integralShellLiftPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- A linear self-equivalence of a finite free module, in the standard matrix
general-linear group. -/
private def integralGeneralLinearOfLinearEquiv
    {R : Type*} [CommRing R] {m : ℕ}
    (e : (Fin m → R) ≃ₗ[R] (Fin m → R)) : GL (Fin m) R :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

private theorem integralGeneralLinearOfLinearEquiv_val
    {R : Type*} [CommRing R] {m : ℕ}
    (e : (Fin m → R) ≃ₗ[R] (Fin m → R)) :
    (integralGeneralLinearOfLinearEquiv e).1 =
      LinearMap.toMatrix' e.toLinearMap := by
  let G := integralGeneralLinearOfLinearEquiv e
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hv := congrArg Units.val h
  have hlin : Matrix.toLin' G.1 = e.toLinearMap := by
    exact hv
  calc
    G.1 = LinearMap.toMatrix' (Matrix.toLin' G.1) :=
      (LinearMap.toMatrix'_toLin' G.1).symm
    _ = LinearMap.toMatrix' e.toLinearMap := by rw [hlin]

/-- At an odd unimodular place with integral Clifford structure, an integral
unit-shell target has an integral intrinsic `GSpin` lift whose represented
action carries the supplied source vector to that target.  Positive rank of
the source orthogonal complement is the exact determinant-correction
hypothesis. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.exists_integral_padicCliffordGeneralSpin_mulVec_eq_of_unit_shell
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (hvStructure : V.CliffordGeneralSpinIntegralStructureAt v)
    (x y : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hxy : P.unimodularForm.quadraticForm y =
      P.unimodularForm.quadraticForm x)
    (hx : IsUnit (P.unimodularForm.quadraticForm x))
    [NeZero (P.unimodularForm.orthogonalUnimodularForm x hx).rank] :
    ∃ z : V.HeightOnePadicCliffordGeneralSpinGroup v,
      V.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v).1 z ∧
        z.matrixGroup.1.1.1 *ᵥ
            (fun i ↦ (x i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
          fun i ↦ (y i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let U := P.unimodularForm
  let xs := U.evenAlignmentWord P.prime_ne_two x y hxy hx
  let Q := V.commutativeScalarExtensionQuadraticForm ℚ_[p]
  let word := P.unitReflectionWordToPadic xs
  have hwordLength : word.length = 2 := by
    rw [show word.length = xs.length by
      exact P.length_unitReflectionWordToPadic xs]
    exact U.length_evenAlignmentWord P.prime_ne_two x y hxy hx
  have hdet :
      LinearMap.det (eval Q word).toLinearEquiv.toLinearMap = 1 := by
    rw [det_eval, hwordLength]
    norm_num
  let gd : DetOneIsometryGroup Q :=
    ⟨eval Q word, Units.ext (by simpa using hdet)⟩
  let g : V.specialOrthogonalMatrixGroup ℚ_[p] :=
    V.detOneIsometrySpecialOrthogonalMatrixGroup ℚ_[p] gd
  let eInt := LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U xs
  let GInt : GL (Fin n) ℤ_[p] :=
    integralGeneralLinearOfLinearEquiv eInt.toLinearEquiv
  have hGInt :
      GInt.1 = LinearMap.toMatrix' eInt.toLinearEquiv.toLinearMap :=
    integralGeneralLinearOfLinearEquiv_val eInt.toLinearEquiv
  have hmatrix :
      ((Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom) GInt).1 =
        g.1.1.1 := by
    rw [show g.1.1.1 = LinearMap.toMatrix'
        (eval Q word).toLinearEquiv.toLinearMap by
      exact V.detOneIsometrySpecialOrthogonalMatrixGroup_apply_matrix ℚ_[p] gd]
    rw [show LinearMap.toMatrix' (eval Q word).toLinearEquiv.toLinearMap =
        (LinearMap.toMatrix' eInt.toLinearEquiv.toLinearMap).map
          PadicInt.Coe.ringHom by
      exact P.eval_unitReflectionWordToPadic_toMatrix' xs]
    rw [← hGInt]
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply PadicInt.Coe.ringHom i j GInt
  have hGL :
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom) GInt = g.1.1 := by
    apply Units.ext
    exact hmatrix
  let gIntegral : V.HeightOnePadicSpecialOrthogonalIntegralGroup v :=
    ⟨g, by
      rw [V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic]
      constructor
      · intro i j
        rw [← hmatrix]
        rw [Matrix.GeneralLinearGroup.map_apply]
        exact (PadicInt.mem_subring_iff p).2 (GInt.1 i j).property
      · intro i j
        rw [← hGL]
        rw [← map_inv]
        rw [Matrix.GeneralLinearGroup.map_apply]
        exact (PadicInt.mem_subring_iff p).2 ((GInt⁻¹).1 i j).property⟩
  obtain ⟨ps, hps⟩ :=
    P.exists_reflectionPairs_flatten_eq_evenAlignmentWordToPadic
      x y hxy hx
  have hpairsEval : eval Q (flattenPairs Q ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g := by
    rw [hps]
    exact (congrArg Subtype.val
      (V.specialOrthogonalMatrixGroupDetOneIsometryHom_inverse_apply
        ℚ_[p] gd)).symm
  have hpairsIntegral : V.AreIntegralReflectionPairsAt v ps :=
    V.areIntegralReflectionPairsAt_of_unitReflectionWord P xs ps hps
  let z := CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs
    V ℚ_[p] g ps hpairsEval
  refine ⟨z, V.ofReflectionPairs_isIntegral v hvStructure gIntegral ps
    hpairsEval hpairsIntegral, ?_⟩
  have hzMatrix : z.matrixGroup = g :=
    CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs_matrixGroup
      V ℚ_[p] g ps hpairsEval
  rw [hzMatrix]
  change V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g
      (fun i ↦ (x i : ℚ_[p])) = fun i ↦ (y i : ℚ_[p])
  rw [← hpairsEval, hps]
  exact P.eval_evenAlignmentWordToPadic_apply_source x y hxy hx

end RationalQuadraticSpaceMatrix
