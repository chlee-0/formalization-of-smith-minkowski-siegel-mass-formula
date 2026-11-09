import SMSFormula.RationalCliffordGeneralSpinLocalCompactness
import SMSFormula.RationalCliffordGeneralSpinBlockFieldShell
import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalCliffordGeneralSpinPlacewiseTranslatedDifferentialChart
import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# The p-adic block-shell orbit map is continuous and open

Over `ℚ_p` the `GSpin` point group acts on the nonzero block shell `{Q = a}` by its
represented matrix: `g • v = g.matrixPoint *ᵥ v`.  The action is built from the shell orbit
map and its surjectivity over characteristic-zero fields (no representative enters the
result, since the translate is the literal matrix action).  It is continuous and transitive.

The group is locally compact (closed coordinate embedding) and second countable (the same
embedding into a second-countable coordinate space), hence `σ`-compact; the shell is closed in
`ℚ_p^{n+1}`, hence locally compact Hausdorff and Baire.  Mathlib's Baire open-mapping theorem
then makes the orbit map `g ↦ g • x_old` open.  Consequently the local orbit of a compact open
subset of the group is compact open in the shell: the compactness/openness hypotheses of the
orbit-image theorem reduce to the supplied local subgroups themselves.  Nothing is chosen.
-/

noncomputable section

open Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The scalar-extended quadratic form is continuous over `ℚ_p`. -/
theorem continuous_commutativeScalarExtensionQuadraticForm_padic (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact p.Prime] : Continuous (V.commutativeScalarExtensionQuadraticForm ℚ_[p]) := by
  unfold commutativeScalarExtensionQuadraticForm
  have h : ∀ v, (V.commutativeScalarExtensionFormMatrix ℚ_[p]).toQuadraticMap' v =
      v ⬝ᵥ ((V.commutativeScalarExtensionFormMatrix ℚ_[p]) *ᵥ v) := fun v ↦ by
    change Matrix.toQuadraticForm' (V.commutativeScalarExtensionFormMatrix ℚ_[p]) v = _
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  rw [show ⇑((V.commutativeScalarExtensionFormMatrix ℚ_[p]).toQuadraticMap') =
    fun v ↦ v ⬝ᵥ ((V.commutativeScalarExtensionFormMatrix ℚ_[p]) *ᵥ v) from funext h]
  unfold dotProduct Matrix.mulVec dotProduct
  fun_prop

variable (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
variable (p : ℕ) [Fact p.Prime]

theorem isClosed_nonisotropicLastQuadraticShell_padic :
    IsClosed (W.nonisotropicLastQuadraticShell a ha ℚ_[p]) :=
  isClosed_eq ((W.nonisotropicLastExtension a ha).continuous_commutativeScalarExtensionQuadraticForm_padic
    p) continuous_const

/-- The vector underlying the `ℚ_p` shell orbit of a product. -/
theorem CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul_padic
    (g h : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] (g * h)).1 =
      g.matrixPoint.1 *ᵥ
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] h).1 := by
  change (g * h).matrixPoint.1 *ᵥ lastCoordinateVector =
    g.matrixPoint.1 *ᵥ (h.matrixPoint.1 *ᵥ lastCoordinateVector)
  rw [Matrix.mulVec_mulVec]
  rfl

/-- The matrix translate of a `ℚ_p` shell point, through the orbit map. -/
def padicNonisotropicLastShellTranslate
    (g : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p])
    (v : W.nonisotropicLastQuadraticShell a ha ℚ_[p]) : W.nonisotropicLastQuadraticShell a ha ℚ_[p] :=
  CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p]
    (g * Classical.choose
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective W a ha ℚ_[p] v))

/-- The translate is the literal matrix action. -/
theorem coe_padicNonisotropicLastShellTranslate
    (g : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p])
    (v : W.nonisotropicLastQuadraticShell a ha ℚ_[p]) :
    (W.padicNonisotropicLastShellTranslate a ha p g v).1 = g.matrixPoint.1 *ᵥ v.1 := by
  unfold padicNonisotropicLastShellTranslate
  rw [CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul_padic,
    Classical.choose_spec
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective W a ha ℚ_[p] v)]

/-- The `ℚ_p` matrix action of `GSpin` on the block shell. -/
def padicNonisotropicLastShellMulAction :
    MulAction ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p])
      (W.nonisotropicLastQuadraticShell a ha ℚ_[p]) where
  smul := W.padicNonisotropicLastShellTranslate a ha p
  one_smul v := Subtype.ext (by
    change (W.padicNonisotropicLastShellTranslate a ha p 1 v).1 = v.1
    rw [coe_padicNonisotropicLastShellTranslate]
    exact Matrix.one_mulVec v.1)
  mul_smul g h v := Subtype.ext (by
    change (W.padicNonisotropicLastShellTranslate a ha p (g * h) v).1 =
      (W.padicNonisotropicLastShellTranslate a ha p g
        (W.padicNonisotropicLastShellTranslate a ha p h v)).1
    rw [coe_padicNonisotropicLastShellTranslate, coe_padicNonisotropicLastShellTranslate,
      coe_padicNonisotropicLastShellTranslate, Matrix.mulVec_mulVec]
    rfl)

/-- The orbit map is the orbit of the last-coordinate point under the matrix action. -/
theorem padicNonisotropicLastShellTranslate_orbit
    (g : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    W.padicNonisotropicLastShellTranslate a ha p g
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] 1) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] g := by
  apply Subtype.ext
  rw [coe_padicNonisotropicLastShellTranslate,
    ← CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul_padic, mul_one]

/-- The `ℚ_p` shell orbit map is continuous. -/
theorem continuous_padic_nonisotropicLastShellOrbitMap :
    Continuous (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p]) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  simpa [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap,
    Matrix.mulVec, dotProduct, lastCoordinateVector, Pi.single_apply] using
    ((W.nonisotropicLastExtension a ha).continuous_cliffordGeneralSpinMatrixCoordinate
      ℚ_[p] i (Fin.last n))

/-- The `ℚ_p` shell orbit map is open (Baire open mapping). -/
theorem isOpenMap_padic_nonisotropicLastShellOrbitMap :
    IsOpenMap (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p]) := by
  let V := W.nonisotropicLastExtension a ha
  letI := W.padicNonisotropicLastShellMulAction a ha p
  letI : LocallyCompactSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
    V.padicCliffordGeneralSpinGroupLocallyCompactSpace p
  letI : SecondCountableTopology (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
    (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding ℚ_[p]).isEmbedding
      |>.secondCountableTopology
  letI : LocallyCompactSpace (W.nonisotropicLastQuadraticShell a ha ℚ_[p]) :=
    (W.isClosed_nonisotropicLastQuadraticShell_padic a ha p).locallyCompactSpace
  letI : ContinuousSMul (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p])
      (W.nonisotropicLastQuadraticShell a ha ℚ_[p]) := ⟨by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun q : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p] ×
      W.nonisotropicLastQuadraticShell a ha ℚ_[p] ↦
        (W.padicNonisotropicLastShellTranslate a ha p q.1 q.2).val i)
    simp only [coe_padicNonisotropicLastShellTranslate, Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ (fun j _ ↦
      ((V.continuous_cliffordGeneralSpinMatrixCoordinate ℚ_[p] i j).comp continuous_fst).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))⟩
  letI : MulAction.IsPretransitive (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p])
      (W.nonisotropicLastQuadraticShell a ha ℚ_[p]) := ⟨fun x y ↦ by
    obtain ⟨h, rfl⟩ :=
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective W a ha ℚ_[p] x
    obtain ⟨k, rfl⟩ :=
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective W a ha ℚ_[p] y
    refine ⟨k * h⁻¹, Subtype.ext ?_⟩
    change (W.padicNonisotropicLastShellTranslate a ha p (k * h⁻¹) _).1 = _
    rw [coe_padicNonisotropicLastShellTranslate,
      ← CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul_padic,
      inv_mul_cancel_right]⟩
  have hopen := isOpenMap_smul_of_sigmaCompact (G := V.CliffordGeneralSpinIntrinsicPoint ℚ_[p])
    (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] 1)
  have heq : (fun g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p] ↦
      g • CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] 1) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] :=
    funext fun g ↦ W.padicNonisotropicLastShellTranslate_orbit a ha p g
  rwa [heq] at hopen

/-- The local orbit of a compact open set is compact open in the `ℚ_p` block shell. -/
theorem isCompact_isOpen_image_padic_nonisotropicLastShellOrbitMap
    {s : Set ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p])}
    (hc : IsCompact s) (ho : IsOpen s) :
    IsCompact (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] '' s) ∧
      IsOpen (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] '' s) :=
  ⟨hc.image (W.continuous_padic_nonisotropicLastShellOrbitMap a ha p),
    W.isOpenMap_padic_nonisotropicLastShellOrbitMap a ha p s ho⟩

end RationalQuadraticSpaceMatrix
