import SMSFormula.RationalCliffordSpinCandidateIntegralOriginalMatrixCarrier

/-!
# Scalar extension of integral unit-reflection words

At a certified odd-unimodular place, an integral unit vector for the chosen
Gram matrix becomes an anisotropic vector for the original rational form over
`Q_p`.  Integral unit reflections and their evaluated words commute with this
entrywise scalar extension.  Combining that compatibility with the original
matrix carrier identifies the cast field word with the original local
special-orthogonal isometry.

This is still presentation-level bookkeeping: no spinor norm, integral Spin
lifting, covering degree, or Haar comparison occurs here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Matrix
open QuadraticMap.ReflectionWord
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance integralReflectionFieldBridgePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The quadratic value of the certified integral form becomes the quadratic
value of the original rational form over `Q_p`. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.coe_unimodularForm_quadraticForm
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
    ((P.unimodularForm.quadraticForm x :
        ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
        V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (fun i ↦ (x i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) := by
  rw [LocalPadicIntegralUnimodularForm.quadraticForm_apply,
    V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
  simp only [
    CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unimodularForm_pairingMatrix,
    specialOrthogonalMappedFormMatrix]
  rw [← P.integralFormMatrix_map]
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct] <;> rfl

/-- An integral unit vector, regarded as an anisotropic vector of the
original scalar-extended rational form. -/
def CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitVectorToPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : P.unimodularForm.UnitVector) :
    (V.commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).AnisotropicVector := by
  refine ⟨fun i ↦ (x.1 i :
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]), ?_⟩
  rw [← P.coe_unimodularForm_quadraticForm x.1]
  exact PadicInt.coe_ne_zero.mpr x.property.ne_zero

@[simp]
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.quadraticForm_unitVectorToPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : P.unimodularForm.UnitVector) :
    V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (P.unitVectorToPadic x) =
      ((P.unimodularForm.quadraticForm x :
          ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
  (P.coe_unimodularForm_quadraticForm x.1).symm

set_option backward.isDefEq.respectTransparency false in
/-- Polarization commutes with the same pointwise scalar extension. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.polar_toPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x y : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
    QuadraticMap.polar
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (fun i ↦ (x i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
        (fun i ↦ (y i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
      ((QuadraticMap.polar P.unimodularForm.quadraticForm x y :
          ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  simp only [QuadraticMap.polar]
  rw [show
      (fun i ↦ (x i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) +
          (fun i ↦ (y i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
        fun i ↦ ((x + y) i :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) by
      ext i
      simp]
  rw [← P.coe_unimodularForm_quadraticForm (x + y),
    ← P.coe_unimodularForm_quadraticForm x,
    ← P.coe_unimodularForm_quadraticForm y]
  simp <;> rfl

/-- A single integral unit reflection commutes with pointwise scalar
extension to the p-adic field. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.quadraticReflection_toPadic_apply
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : P.unimodularForm.UnitVector)
    (y : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
    CliffordAlgebra.quadraticReflectionOfNeZero
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitVectorToPadic x) (P.unitVectorToPadic x).property
        (fun i ↦ (y i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
      fun i ↦ ((P.unimodularForm.unitReflection x y i :
        ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let U := P.unimodularForm
  let Q := V.commutativeScalarExtensionQuadraticForm ℚ_[p]
  letI : Invertible (U.quadraticForm x) := x.property.invertible
  have hinv :
      (Q (P.unitVectorToPadic x).1)⁻¹ =
        ((⅟(U.quadraticForm x) : ℤ_[p]) : ℚ_[p]) := by
    rw [show Q (P.unitVectorToPadic x).1 =
        ((U.quadraticForm x : ℤ_[p]) : ℚ_[p]) by
      exact (P.coe_unimodularForm_quadraticForm x.1).symm]
    letI hfield : Invertible
        (PadicInt.Coe.ringHom (U.quadraticForm x.1)) :=
      Invertible.map PadicInt.Coe.ringHom (U.quadraticForm x)
    calc
      (PadicInt.Coe.ringHom (U.quadraticForm x.1))⁻¹ =
          ⅟(PadicInt.Coe.ringHom (U.quadraticForm x.1)) :=
        (invOf_eq_inv _).symm
      _ = PadicInt.Coe.ringHom (⅟(U.quadraticForm x.1)) :=
        (map_invOf PadicInt.Coe.ringHom (U.quadraticForm x.1)).symm
  rw [CliffordAlgebra.quadraticReflectionOfNeZero_apply,
    LocalPadicIntegralUnimodularForm.unitReflection,
    CliffordAlgebra.quadraticReflection_apply]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hpolar :
      QuadraticMap.polar Q (P.unitVectorToPadic x).1
          (fun j ↦ (y j : ℚ_[p])) =
        ((QuadraticMap.polar U.quadraticForm x.1 y : ℤ_[p]) :
          ℚ_[p]) := by
    change
      QuadraticMap.polar Q (fun j ↦ (x.1 j : ℚ_[p]))
          (fun j ↦ (y j : ℚ_[p])) = _
    exact P.polar_toPadic x.1 y
  rw [hinv, hpolar]
  dsimp only [U]
  simp only [
    CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitVectorToPadic]
  norm_cast

/-- Pointwise scalar extension of an integral unit-reflection word. -/
def CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitReflectionWordToPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (xs : P.unimodularForm.UnitReflectionWord) :
    (V.commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).ReflectionWord :=
  xs.map P.unitVectorToPadic

@[simp]
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.length_unitReflectionWordToPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (xs : P.unimodularForm.UnitReflectionWord) :
    (P.unitReflectionWordToPadic xs).length = xs.length := by
  simp [CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitReflectionWordToPadic]

/-- Evaluation of an integral reflection word commutes pointwise with scalar
extension. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.eval_unitReflectionWordToPadic_apply
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (xs : P.unimodularForm.UnitReflectionWord)
    (y : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
    eval
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitReflectionWordToPadic xs)
        (fun i ↦ (y i : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
      fun i ↦
        ((LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
            P.unimodularForm xs y i :
          ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  induction xs generalizing y with
  | nil => rfl
  | cons x xs ih =>
      rw [CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitReflectionWordToPadic,
        List.map_cons, QuadraticMap.ReflectionWord.eval_cons_apply,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons_apply,
        P.quadraticReflection_toPadic_apply]
      exact ih (P.unimodularForm.unitReflection x y)

/-- Matrix form of word-evaluation compatibility. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.eval_unitReflectionWordToPadic_toMatrix'
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (xs : P.unimodularForm.UnitReflectionWord) :
    LinearMap.toMatrix'
        (eval
          (V.commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
          (P.unitReflectionWordToPadic xs)).toLinearEquiv.toLinearMap =
      (LinearMap.toMatrix'
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
          P.unimodularForm xs).toLinearEquiv.toLinearMap).map
            PadicInt.Coe.ringHom := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
  let ez : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    Pi.single j 1
  let eq : Fin n → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    Pi.single j 1
  change
    eval
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitReflectionWordToPadic xs) eq i =
      ((LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
          P.unimodularForm xs ez i :
        ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
  have hsingle :
      (fun k ↦ (ez k :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) = eq := by
    ext k
    by_cases hkj : k = j <;> simp [ez, eq, hkj]
  have h := congrFun
    (P.eval_unitReflectionWordToPadic_apply xs ez) i
  rw [← hsingle]
  exact h

/-- A cast integral word representing an integral `SO` point evaluates to
the original p-adic field isometry. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.eval_unitReflectionWordToPadic_eq_original
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v)
    (xs : P.unimodularForm.UnitReflectionWord)
    (hxs : LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
        P.unimodularForm xs =
      CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry
        V P g) :
    eval
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitReflectionWordToPadic xs) =
      V.specialOrthogonalMatrixGroupIsometryEquiv
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 := by
  apply DFunLike.coe_injective
  funext z
  have hlin :
      (eval
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitReflectionWordToPadic xs)).toLinearEquiv.toLinearMap =
      (V.specialOrthogonalMatrixGroupIsometryEquiv
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        g.1).toLinearEquiv.toLinearMap := by
    apply (LinearMap.toMatrix'
      (R := ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
      (m := Fin n) (n := Fin n)).injective
    rw [P.eval_unitReflectionWordToPadic_toMatrix', hxs,
      CliffordSpinCandidateIntegralSpinorRangeGoodPlace.integralIsometry_toMatrix'
        V P g]
    exact (V.heightOnePadicSpecialOrthogonalIntegralGL_map g).trans
      (V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix'
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1).symm
  exact LinearMap.congr_fun hlin z

end RationalQuadraticSpaceMatrix
