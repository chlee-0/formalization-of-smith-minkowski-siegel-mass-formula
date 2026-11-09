import SMSFormula.RationalQuadraticIsometrySpinCandidateAmbientOneShellCalibration
import SMSFormula.RationalCliffordGeneralSpinAllRationalThetaQuotient

/-!
# Section-free represented-norm theta densities on the GSpin quotient

The ordinary nonnegative theta density attached to a represented nonzero
rational norm is defined directly as the sum over its literal rational-vector
fiber.  It is rational-left invariant and descends measurably to the existing
adelic `GSpin` quotient.  For every vector in the fiber it agrees with the
previous vector-indexed rational-shell density, but no vector is selected in
its definition.

The ordinary all-rational quotient theta is then the zero summand plus the
sum of these section-free fiber densities.  Nonnegative Tonelli gives the
corresponding exact logarithmic-cutoff integral decomposition on the existing
horizontal quotient measure.  No complement witness, presentation, shell
measure, Tamagawa coefficient, or new quotient measure occurs.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

namespace RepresentedNonzeroRationalNorm

variable {V : RationalQuadraticSpaceMatrix n}

instance rationalVectorFiberCountable
    (a : V.RepresentedNonzeroRationalNorm) :
    Countable (a.rationalVectorFiber V) := by
  unfold rationalVectorFiber
  infer_instance

private theorem commutativeScalarExtensionQuadraticForm_rational_eq_native
    (V : RationalQuadraticSpaceMatrix n) (y : Fin n → ℚ) :
    V.commutativeScalarExtensionQuadraticForm ℚ y =
      V.nativeRationalQuadraticForm y := by
  simp [commutativeScalarExtensionQuadraticForm,
    commutativeScalarExtensionFormMatrix, quadraticForm]

/-- The rational inverse special-orthogonal action preserves the literal
fiber of a represented nonzero rational norm. -/
def rationalGeneralSpinInvFiberEquiv
    (a : V.RepresentedNonzeroRationalNorm)
    (d : V.RationalCliffordGeneralSpinGroup) :
    a.rationalVectorFiber V ≃ a.rationalVectorFiber V := by
  let e := V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d.matrixGroup⁻¹)
  exact
    { toFun := fun y ↦ ⟨e y.1, by
          calc
            V.commutativeScalarExtensionQuadraticForm ℚ (e y.1) =
                V.commutativeScalarExtensionQuadraticForm ℚ y.1 := e.map_app y.1
            _ = V.nativeRationalQuadraticForm y.1 :=
              commutativeScalarExtensionQuadraticForm_rational_eq_native V y.1
            _ = a.1 := y.property⟩
      invFun := fun y ↦ ⟨e.symm y.1, by
          calc
            V.commutativeScalarExtensionQuadraticForm ℚ (e.symm y.1) =
                V.commutativeScalarExtensionQuadraticForm ℚ y.1 :=
              e.symm.map_app y.1
            _ = V.nativeRationalQuadraticForm y.1 :=
              commutativeScalarExtensionQuadraticForm_rational_eq_native V y.1
            _ = a.1 := y.property⟩
      left_inv := fun y ↦ Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y.1) }

@[simp]
theorem rationalGeneralSpinInvFiberEquiv_coe
    (a : V.RepresentedNonzeroRationalNorm)
    (d : V.RationalCliffordGeneralSpinGroup)
    (y : a.rationalVectorFiber V) :
    (a.rationalGeneralSpinInvFiberEquiv d y).1 =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ
        (d.matrixGroup⁻¹) y.1 :=
  rfl

/-- A literal norm fiber is canonically the vector-indexed ambient rational
shell through any supplied member of that fiber. -/
def rationalVectorFiberEquivAmbientShell
    (a : V.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber V) :
    a.rationalVectorFiber V ≃ V.anisotropicRationalAmbientShell x.1 ℚ where
  toFun y := ⟨y.1, by
    change V.nativeRationalQuadraticForm y.1 =
      V.nativeRationalQuadraticForm x.1
    rw [y.property, x.property]⟩
  invFun y := ⟨y.1, by
    calc
      V.nativeRationalQuadraticForm y.1 =
          V.commutativeScalarExtensionQuadraticForm ℚ y.1 :=
        (commutativeScalarExtensionQuadraticForm_rational_eq_native V y.1).symm
      _ = algebraMap ℚ ℚ (V.nativeRationalQuadraticForm x.1) := y.property
      _ = V.nativeRationalQuadraticForm x.1 := Rat.cast_id _
      _ = a.1 := x.property⟩
  left_inv y := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

@[simp]
theorem rationalVectorFiberEquivAmbientShell_coe
    (a : V.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber V)
    (y : a.rationalVectorFiber V) :
    (a.rationalVectorFiberEquivAmbientShell x y).1 = y.1 :=
  rfl

end RepresentedNonzeroRationalNorm

/-- The ordinary nonnegative theta density indexed directly by a represented
nonzero rational norm. -/
def fullAdelicCliffordGeneralSpinRepresentedNormTheta
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) : ℝ≥0∞ :=
  ∑' x : a.rationalVectorFiber V,
    V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g x.1

theorem measurable_fullAdelicCliffordGeneralSpinRepresentedNormTheta
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi) := by
  unfold fullAdelicCliffordGeneralSpinRepresentedNormTheta
  exact Measurable.ennreal_tsum fun x ↦
    V.measurable_fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
      Phi hPhi x.1

/-- The section-free represented-norm density is invariant under the complete
rational adelic `GSpin` diagonal. -/
theorem fullAdelicCliffordGeneralSpinRepresentedNormTheta_rational_mul
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi
        ((delta : V.FullAdelicCliffordGeneralSpinGroup) * g) =
      V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi g := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) =
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicCliffordGeneralSpinRepresentedNormTheta
  simp_rw [fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul,
    ← a.rationalGeneralSpinInvFiberEquiv_coe d]
  exact (a.rationalGeneralSpinInvFiberEquiv d).tsum_eq
    (fun y ↦
      Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g y.1))

/-- The section-free represented-norm density on the existing rational left
quotient. -/
def fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ :=
  Quot.lift (V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi) (by
    intro g h hrel
    rcases hrel with ⟨delta, rfl⟩
    exact (V.fullAdelicCliffordGeneralSpinRepresentedNormTheta_rational_mul
      a Phi delta g).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_mk
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient a Phi
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi g :=
  rfl

theorem measurable_fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable
      (V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
        a Phi) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  intro s hs
  rcases hs with ⟨s', hs', rfl⟩
  rcases hs' with ⟨t, ht, rfl⟩
  simpa only [Set.preimage_preimage,
    fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_mk] using
      (measurable_iff_comap_le.mp
        (V.measurable_fullAdelicCliffordGeneralSpinRepresentedNormTheta
          a Phi hPhi))
        ((V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi) ⁻¹' t)
        ⟨t, ht, rfl⟩

/-- At every supplied vector of the fiber, the section-free norm density is
the previous vector-indexed rational-shell density. -/
theorem fullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_rationalShellTheta
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber V)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi g =
      V.fullAdelicCliffordGeneralSpinRationalShellTheta x.1 Phi g := by
  unfold fullAdelicCliffordGeneralSpinRepresentedNormTheta
  unfold fullAdelicCliffordGeneralSpinRationalShellTheta
  simpa only [a.rationalVectorFiberEquivAmbientShell_coe x] using
    (a.rationalVectorFiberEquivAmbientShell x).tsum_eq
      (fun y ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
          Phi g y.1)

/-- Quotient form of the agreement with every vector-indexed rational-shell
density. -/
theorem fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_eq_rationalShellTheta
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber V)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (Z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
        a Phi Z =
      V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
        x.1 Phi Z := by
  induction Z using Quot.inductionOn with
  | _ g =>
      exact V.fullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_rationalShellTheta
        a x Phi g

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Pointwise section-free partition of the ordinary all-rational theta on
the full-adelic group. -/
theorem fullAdelicCliffordGeneralSpinTheta_eq_zero_add_representedNormTheta
    (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : L.rationalQuadraticSpaceMatrix
      |>.FullAdelicCliffordGeneralSpinGroup) :
    let V := L.rationalQuadraticSpaceMatrix
    V.fullAdelicCliffordGeneralSpinTheta Phi g =
      Phi 0 + ∑' a : V.RepresentedNonzeroRationalNorm,
        V.fullAdelicCliffordGeneralSpinRepresentedNormTheta a Phi g := by
  let V := L.rationalQuadraticSpaceMatrix
  change
    (∑' x : Fin n → ℚ,
      V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g x) = _
  simpa only [fullAdelicCliffordGeneralSpinRepresentedNormTheta,
    fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    V.fullAdelicCliffordGeneralSpinRationalVectorAction_zero] using
    L.tsum_rationalVector_eq_zero_add_representedNorm_fibers
      (fun x ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g x)

/-- Pointwise section-free partition of the ordinary theta on the existing
rational left quotient. -/
theorem fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_eq_zero_add_representedNormTheta
    (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (Z : L.rationalQuadraticSpaceMatrix
      |>.FullAdelicCliffordGeneralSpinLeftQuotient) :
    let V := L.rationalQuadraticSpaceMatrix
    V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi Z =
      Phi 0 + ∑' a : V.RepresentedNonzeroRationalNorm,
        V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
          a Phi Z := by
  let V := L.rationalQuadraticSpaceMatrix
  induction Z using Quot.inductionOn with
  | _ g =>
      exact L.fullAdelicCliffordGeneralSpinTheta_eq_zero_add_representedNormTheta
        Phi g

/-- The logarithmic-cutoff integral of one section-free represented-norm
theta density against the existing horizontal quotient measure. -/
noncomputable def fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let V := L.rationalQuadraticSpaceMatrix
  ∫⁻ Z,
    f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
  ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure).withDensity
        (V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
          a Phi)

/-- The logarithmic-cutoff integral of the ordinary all-rational theta
against the existing horizontal quotient measure. -/
noncomputable def fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
    (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let V := L.rationalQuadraticSpaceMatrix
  ∫⁻ Z,
    f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
  ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure).withDensity
        (V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi)

/-- Nonnegative Tonelli reassembles the ordinary quotient-theta cutoff
integral as its zero term plus the sum of the section-free represented-norm
contributions. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_eq_zero_add_representedNorm
    (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f =
      Phi 0 *
        (∫⁻ Z,
          f (L.rationalQuadraticSpaceMatrix
            |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
        ∂(L.rationalQuadraticSpaceMatrix
          |>.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
          |>.quotientMeasure)) +
      ∑' a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        L.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
          a Phi f := by
  let V := L.rationalQuadraticSpaceMatrix
  let mu :=
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
  let cutoff : V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ :=
    fun Z ↦ f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
  let theta := V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi
  let fiberTheta := fun a : V.RepresentedNonzeroRationalNorm ↦
    V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient a Phi
  have hcutoff : Measurable cutoff :=
    hf.comp V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable
  have htheta : Measurable theta :=
    V.measurable_fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi hPhi
  have hfiberTheta : ∀ a, Measurable (fiberTheta a) := fun a ↦
    V.measurable_fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
      a Phi hPhi
  unfold fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul mu htheta hcutoff]
  calc
    (∫⁻ Z, theta Z * cutoff Z ∂mu) =
        ∫⁻ Z,
          Phi 0 * cutoff Z +
            ∑' a : V.RepresentedNonzeroRationalNorm,
              fiberTheta a Z * cutoff Z ∂mu := by
      apply lintegral_congr
      intro Z
      rw [show theta Z = Phi 0 + ∑' a, fiberTheta a Z by
        exact L.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_eq_zero_add_representedNormTheta
          Phi Z]
      rw [add_mul, ENNReal.tsum_mul_right]
    _ = Phi 0 * (∫⁻ Z, cutoff Z ∂mu) +
        ∑' a : V.RepresentedNonzeroRationalNorm,
          ∫⁻ Z, fiberTheta a Z * cutoff Z ∂mu := by
      rw [lintegral_add_left (measurable_const.mul hcutoff)]
      rw [lintegral_const_mul _ hcutoff]
      rw [lintegral_tsum]
      intro a
      exact ((hfiberTheta a).mul hcutoff).aemeasurable
    _ = Phi 0 * (∫⁻ Z, cutoff Z ∂mu) +
        ∑' a : V.RepresentedNonzeroRationalNorm,
          L.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
            a Phi f := by
      congr 1
      apply tsum_congr
      intro a
      unfold fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
      dsimp only
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul mu
          (hfiberTheta a) hcutoff).symm

end PositiveDefiniteIntegralLattice

end
