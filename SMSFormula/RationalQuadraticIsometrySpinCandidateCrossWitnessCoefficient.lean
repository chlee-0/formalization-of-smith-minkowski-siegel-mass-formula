import SMSFormula.QuadraticCartanDieudonneOrthogonal
import SMSFormula.RationalQuadraticIsometrySpinCandidateOneShellCoefficient
import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRawMeasureTransport

/-!
# Cross-witness invariance of one-shell Spin coefficients

Two independently supplied complement presentations for equal nonzero
rational norms need not have the same lower coordinate matrix.  Reflection
alignment supplies an explicit ambient quadratic self-isometry carrying one
source vector to the other.  Restricting it to the two intrinsic orthogonal
complements and composing with the supplied presentation isometries gives a
rational quadratic isometry between the lower matrices.

Arbitrary-isometry raw Spin covariance then identifies their certified Spin
Tamagawa numbers and hence their normalized one-shell coefficients.  No
complement lattice, global presentation family, shell representative, chart,
or Tamagawa value is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace QuadraticMap.IsometryEquiv

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M)

/-- A quadratic self-isometry carrying `x` to `y` restricts to a quadratic
isometry from `x⊥` to `y⊥`. -/
def restrictBetweenAnisotropicOrthogonals
    (g : Q.IsometryEquiv Q) (x y : M) (hxy : g x = y) :
    (Q.orthogonalRestriction x).IsometryEquiv
      (Q.orthogonalRestriction y) where
  toLinearEquiv :=
    { toFun := fun z ↦ ⟨g z, Q.mem_anisotropicOrthogonal_iff.mpr (by
          calc
            Q.associated y (g z) = Q.associated (g x) (g z) := by rw [hxy]
            _ = Q.associated x z := g.map_associated_self Q x z
            _ = 0 := Q.mem_anisotropicOrthogonal_iff.mp z.property)⟩
      invFun := fun z ↦ ⟨g.symm z, Q.mem_anisotropicOrthogonal_iff.mpr (by
          have hinv : g.symm y = x :=
            g.toLinearEquiv.symm_apply_eq.mpr hxy.symm
          calc
            Q.associated x (g.symm z) =
                Q.associated (g.symm y) (g.symm z) := by rw [hinv]
            _ = Q.associated y z := g.symm.map_associated_self Q y z
            _ = 0 := Q.mem_anisotropicOrthogonal_iff.mp z.property)⟩
      left_inv := fun z ↦ Subtype.ext (g.symm_apply_apply z)
      right_inv := fun z ↦ Subtype.ext (g.apply_symm_apply z)
      map_add' := fun z w ↦ Subtype.ext (g.toLinearEquiv.map_add z w)
      map_smul' := fun a z ↦ Subtype.ext (g.toLinearEquiv.map_smul a z) }
  map_app' z := g.map_app z

@[simp]
theorem coe_restrictBetweenAnisotropicOrthogonals
    (g : Q.IsometryEquiv Q) (x y : M) (hxy : g x = y)
    (z : Q.anisotropicOrthogonal x) :
    ((g.restrictBetweenAnisotropicOrthogonals Q x y hxy z :
      Q.anisotropicOrthogonal y) : M) = g z :=
  rfl

/-- Equal nonzero norms give an explicit isometry between their intrinsic
orthogonal complements.  The inverse of the existing reflection alignment
is used because that alignment sends `y` to `x`. -/
def equalNormOrthogonalRestrictionIsometryEquiv
    (x y : M) (hx : Q x ≠ 0) (hxy : Q y = Q x) :
    (Q.orthogonalRestriction x).IsometryEquiv
      (Q.orthogonalRestriction y) := by
  let a := CliffordAlgebra.reflectionAlignment Q x y hx hxy
  let g := (CliffordAlgebra.ReflectionAlignment.correction Q a).symm
  have hg : g x = y := by
    exact (CliffordAlgebra.ReflectionAlignment.correction Q a).toLinearEquiv
      |>.symm_apply_eq.mpr
        (CliffordAlgebra.ReflectionAlignment.correction_map_source Q a).symm
  exact g.restrictBetweenAnisotropicOrthogonals Q x y hg

end QuadraticMap.IsometryEquiv

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-! ## Support-free arbitrary-isometry coefficient covariance -/

/-- The support-parameterized arbitrary-isometry theorem implies a direct
equality for arbitrary certified raw Spin data in every positive rank.  The
finite support is existentially enlarged only by the two already fixed native
admissible bad sets. -/
theorem spinTamagawaNumberENNReal_eq_of_rationalIsometry
    {r s : ℕ}
    (W : RationalQuadraticSpaceMatrix r)
    (Z : RationalQuadraticSpaceMatrix s)
    (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)
    (hr : 0 < r)
    (DW : W.CliffordSpinCandidateRawOnoTamagawaData)
    (DZ : Z.CliffordSpinCandidateRawOnoTamagawaData) :
    DW.spinTamagawaNumberENNReal = DZ.spinTamagawaNumberENNReal := by
  classical
  have hrs := rationalIsometry_dimension_eq W Z e
  subst s
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨S₀, hS₀⟩ :=
    exists_horizontalIntegralTailRationalIsometrySupport W Z e
  let S := S₀ ∪ W.cliffordSpinCandidateAdmissibleBadPlaces ∪
    Z.cliffordSpinCandidateAdmissibleBadPlaces
  have hS₀S : S₀ ⊆ S := by
    intro v hv
    simp only [S, Finset.mem_union]
    exact Or.inl (Or.inl hv)
  have hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S :=
    IsHorizontalIntegralTailRationalIsometrySupport.mono W Z e hS₀ hS₀S
  have hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S := by
    intro v hv
    simp only [S, Finset.mem_union]
    exact Or.inl (Or.inr hv)
  have hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S := by
    intro v hv
    simp only [S, Finset.mem_union]
    exact Or.inr hv
  exact spinTamagawaNumberENNReal_eq_of_rationalIsometry_of_horizontalIntegralTailSupport
    W Z e hS hW hZ DW DZ

namespace AnisotropicComplementPresentation

variable {n m k : ℕ}
variable {V : RationalQuadraticSpaceMatrix n}
variable {x y : Fin n → ℚ}

/-- The explicit lower-coordinate quadratic isometry determined by two
supplied complement witnesses for equal nonzero ambient norms. -/
def lowerIsometryEquivOfEqualNorm
    (P : V.AnisotropicComplementPresentation x m)
    (R : V.AnisotropicComplementPresentation y k)
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hxy : V.nativeRationalQuadraticForm y =
      V.nativeRationalQuadraticForm x) :
    P.lowerSpace.quadraticForm.IsometryEquiv
      R.lowerSpace.quadraticForm :=
  P.complementIsometry |>.trans
    (QuadraticMap.IsometryEquiv.equalNormOrthogonalRestrictionIsometryEquiv
      V.nativeRationalQuadraticForm x y hx hxy) |>.trans
    R.complementIsometry.symm

/-- The lower-space Spin Tamagawa number is independent of two independently
supplied equal-norm complement witnesses. -/
theorem lower_spinTamagawaNumberENNReal_eq_of_equalNorm
    (P : V.AnisotropicComplementPresentation x m)
    (R : V.AnisotropicComplementPresentation y k)
    (hm : 0 < m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hxy : V.nativeRationalQuadraticForm y =
      V.nativeRationalQuadraticForm x)
    (DP : P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DR : R.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData) :
    DP.spinTamagawaNumberENNReal = DR.spinTamagawaNumberENNReal := by
  exact spinTamagawaNumberENNReal_eq_of_rationalIsometry
    P.lowerSpace R.lowerSpace
      (lowerIsometryEquivOfEqualNorm P R hx hxy) hm DP DR

/-- The normalized one-shell coefficient is independent of two independently
supplied equal-norm complement witnesses.  The ambient denominator is kept
fixed and no shell representative is selected. -/
theorem oneShellSpinTamagawaCoefficient_eq_of_equalNorm
    (P : V.AnisotropicComplementPresentation x m)
    (R : V.AnisotropicComplementPresentation y k)
    (hm : 0 < m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hxy : V.nativeRationalQuadraticForm y =
      V.nativeRationalQuadraticForm x)
    (DP : P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DR : R.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) :
    P.oneShellSpinTamagawaCoefficient DP DAmbient =
      R.oneShellSpinTamagawaCoefficient DR DAmbient := by
  unfold oneShellSpinTamagawaCoefficient
  rw [lower_spinTamagawaNumberENNReal_eq_of_equalNorm
    P R hm hx hxy DP DR]

end AnisotropicComplementPresentation

/-! ## Lattice-backed witness interface -/

/-- Cross-witness invariance in the exact lattice-backed form used by the
one-shell cutoff theorem.  Both complement isometries and both raw data remain
supplied arguments. -/
theorem integralLattice_oneShellSpinTamagawaCoefficient_eq_of_equalNorm
    {n m k : ℕ}
    (L : PositiveDefiniteIntegralLattice m)
    (R : PositiveDefiniteIntegralLattice k)
    (V : RationalQuadraticSpaceMatrix n)
    (x y : Fin n → ℚ)
    (hm : 0 < m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hxy : V.nativeRationalQuadraticForm y =
      V.nativeRationalQuadraticForm x)
    (eL : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction x))
    (eR : R.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction y))
    (DL : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (DR : R.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) :
    AnisotropicComplementPresentation.oneShellSpinTamagawaCoefficient
        (integralLatticeAnisotropicComplementPresentation L V x eL)
        DL DAmbient =
      AnisotropicComplementPresentation.oneShellSpinTamagawaCoefficient
        (integralLatticeAnisotropicComplementPresentation R V y eR)
        DR DAmbient := by
  exact
    AnisotropicComplementPresentation.oneShellSpinTamagawaCoefficient_eq_of_equalNorm
      (integralLatticeAnisotropicComplementPresentation L V x eL)
      (integralLatticeAnisotropicComplementPresentation R V y eR)
      hm hx hxy DL DR DAmbient

end RationalQuadraticSpaceMatrix

end
