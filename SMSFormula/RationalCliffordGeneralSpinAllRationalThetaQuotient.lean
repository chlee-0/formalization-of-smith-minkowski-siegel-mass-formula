import SMSFormula.RationalCliffordGeneralSpinAllRationalWeightedTheta

/-!
# The ordinary all-rational theta function on the GSpin quotient

The ordinary nonnegative theta function is the sum of the existing ambient
summands `Phi(g⁻¹ x)` over all rational vectors.  A rational adelic `GSpin`
diagonal acts on those vectors through a rational special-orthogonal linear
equivalence.  Eliminating the diagonal subgroup's range witness only inside
the proof therefore reindexes the sum and proves rational-left invariance.

The invariant theta function descends measurably to the repository's existing
rational left quotient.  No rational representative, section, complement
presentation, Tamagawa coefficient, cutoff, or quotient measure enters its
definition.  In particular this is the ordinary theta function whose later
probability-normalized quotient integral must produce the already constructed
Spin-weighted expansion; the desired weights are not inserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Rational diagonal embedding commutes with rational matrix-vector
multiplication. -/
theorem rationalAdeleVectorDiagonal_mulVec
    (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    (M.map (algebraMap ℚ RationalAdele)).mulVec
        (rationalAdeleVectorDiagonal n x) =
      rationalAdeleVectorDiagonal n (M.mulVec x) := by
  ext i
  simp [Matrix.mulVec, dotProduct, rationalAdeleVectorDiagonal, map_sum]

private theorem specialOrthogonalMatrixGroupIsometryEquiv_inv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (d : V.RationalCliffordGeneralSpinGroup) (x : Fin n → ℚ) :
    V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d.matrixGroup⁻¹) x =
      (d.matrixGroup⁻¹).1.1.1.mulVec x := by
  change Matrix.toLin' (d.matrixGroup⁻¹).1.1.1 x = _
  rfl

/-- Left multiplication by a supplied rational diagonal transforms the
rational-vector argument by its rational inverse orthogonal equivalence. -/
theorem fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul
    (V : RationalQuadraticSpaceMatrix n)
    (d : V.RationalCliffordGeneralSpinGroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup)
    (x : Fin n → ℚ) :
    V.fullAdelicCliffordGeneralSpinRationalVectorAction
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d * g) x =
      V.fullAdelicCliffordGeneralSpinRationalVectorAction g
        (V.specialOrthogonalMatrixGroupIsometryEquiv ℚ
          (d.matrixGroup⁻¹) x) := by
  rw [fullAdelicCliffordGeneralSpinRationalVectorAction,
    fullAdelicCliffordGeneralSpinRationalVectorAction,
    CliffordGeneralSpinIntrinsicPoint.mul_matrixGroup, mul_inv_rev]
  change
    ((g.matrixGroup⁻¹).1.1.1 *
        ((V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d).matrixGroup⁻¹).1.1.1).mulVec
          (rationalAdeleVectorDiagonal n x) = _
  rw [← Matrix.mulVec_mulVec,
    specialOrthogonalMatrixGroupIsometryEquiv_inv_apply,
    ← rationalAdeleVectorDiagonal_mulVec]
  congr 1
  have hd := V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal d
  change
    (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d).matrixGroup =
      V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ RationalAdele)
        d.matrixGroup at hd
  rw [hd, ← map_inv, V.specialOrthogonalMatrixGroupMap_apply_matrix]
  rfl

/-- The ordinary nonnegative all-rational theta function on the full-adelic
intrinsic `GSpin` group.  It contains no Spin Tamagawa weight. -/
def fullAdelicCliffordGeneralSpinTheta
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) : ℝ≥0∞ :=
  ∑' x : Fin n → ℚ,
    V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g x

/-- A measurable nonnegative adelic test function gives a measurable ordinary
theta function on the full-adelic group. -/
theorem measurable_fullAdelicCliffordGeneralSpinTheta
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (V.fullAdelicCliffordGeneralSpinTheta Phi) := by
  unfold fullAdelicCliffordGeneralSpinTheta
  exact Measurable.ennreal_tsum fun x ↦
    V.measurable_fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
      Phi hPhi x

/-- The ordinary theta function is invariant under the complete rational
adelic `GSpin` diagonal.  Its range witness is eliminated locally and never
selected in the theorem interface. -/
theorem fullAdelicCliffordGeneralSpinTheta_rational_mul
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinTheta Phi
        ((delta : V.FullAdelicCliffordGeneralSpinGroup) * g) =
      V.fullAdelicCliffordGeneralSpinTheta Phi g := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) =
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicCliffordGeneralSpinTheta
  simp_rw [fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul]
  exact
    (V.specialOrthogonalMatrixGroupIsometryEquiv ℚ
      (d.matrixGroup⁻¹)).toEquiv.tsum_eq
        (fun x ↦
          Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x))

/-- The ordinary all-rational theta function descended to the existing
rational `GSpin` left quotient. -/
def fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ :=
  Quot.lift (V.fullAdelicCliffordGeneralSpinTheta Phi) (by
    intro g h hrel
    rcases hrel with ⟨delta, rfl⟩
    exact (V.fullAdelicCliffordGeneralSpinTheta_rational_mul
      Phi delta g).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_mk
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinTheta Phi g :=
  rfl

/-- The descended ordinary theta function is measurable for the existing
map-generated quotient measurable structure. -/
theorem measurable_fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  intro s hs
  rcases hs with ⟨s', hs', rfl⟩
  rcases hs' with ⟨t, ht, rfl⟩
  simpa only [Set.preimage_preimage,
    fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_mk] using
      (measurable_iff_comap_le.mp
        (V.measurable_fullAdelicCliffordGeneralSpinTheta Phi hPhi))
        ((V.fullAdelicCliffordGeneralSpinTheta Phi) ⁻¹' t)
        ⟨t, ht, rfl⟩

end RationalQuadraticSpaceMatrix

end
