import SMSFormula.RationalCliffordGeneralSpinAllRationalThetaQuotient
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellHorizontalThetaCutoff

/-!
# Rational shell cosets and literal rational-vector fibers

The calibrated one-shell theta density is indexed by right cosets of the
rational `GSpin` diagonal modulo the rational complement stabilizer.  The
ordinary theta function is indexed instead by literal rational vectors.  This
file identifies those two indices on a nonisotropic block shell.

The forward map is induced directly by the rational shell orbit map.  Its
inverse is supplied only as the inverse of a proved bijection, so no rational
shell representative is selected.  Reindexing the nonnegative sum then shows
that the calibrated theta-orbit density is the literal sum over the rational
norm fiber.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

private theorem nonisotropicLastQuadraticShellMap_rationalAdele_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Function.Injective
      (W.nonisotropicLastQuadraticShellMap a ha
        (Algebra.ofId ℚ RationalAdele)) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have hi := congrFun (congrArg Subtype.val hxy) i
  exact (NumberField.AdeleRing.algebraMap_injective ℤ ℚ) hi

private theorem rationalCliffordGeneralSpinFullAdelicDiagonalHom_equiv_symm
    {m : ℕ} (V : RationalQuadraticSpaceMatrix m)
    (gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
    V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma) =
      (gamma : V.FullAdelicCliffordGeneralSpinGroup) := by
  change
    ((V.rationalCliffordGeneralSpinGroupEquivDiagonal
        (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma) :
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
        V.FullAdelicCliffordGeneralSpinGroup) = gamma
  rw [V.rationalCliffordGeneralSpinGroupEquivDiagonal.apply_symm_apply]

/-- A rational diagonal point belongs to the rational complement image exactly
when its full-adelic scalar extension belongs to the literal complement
stabilizer. -/
theorem mem_nonisotropicLastComplementGeneralSpinDiagonalImage_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (gamma : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
    gamma ∈ W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha ↔
      (gamma : (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup)) ∈
        W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          a ha RationalAdele := by
  let V := W.nonisotropicLastExtension a ha
  constructor
  · rintro ⟨delta, rfl⟩
    rw [W.nonisotropicLastComplementGeneralSpinDiagonalHom_coe a ha delta]
    exact
      (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
        a ha RationalAdele
        (delta : W.FullAdelicCliffordGeneralSpinGroup)).property
  · intro hgamma
    let q : V.RationalCliffordGeneralSpinGroup :=
      V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma
    have hqA :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q =
          (gamma : V.FullAdelicCliffordGeneralSpinGroup) := by
      change
        ((V.rationalCliffordGeneralSpinGroupEquivDiagonal q :
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
          V.FullAdelicCliffordGeneralSpinGroup) = gamma
      rw [V.rationalCliffordGeneralSpinGroupEquivDiagonal.apply_symm_apply]
    have horbitA :
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q) =
          ⟨lastCoordinateVector,
            W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
              a ha RationalAdele⟩ := by
      rw [hqA]
      exact
        (CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_eq_last_iff
          W a ha gamma).2 hgamma
    have horbitQ :
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha ℚ q =
          ⟨lastCoordinateVector,
            W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
              a ha ℚ⟩ := by
      apply
        nonisotropicLastQuadraticShellMap_rationalAdele_injective W a ha
      rw [CliffordGeneralSpinIntrinsicPoint.rationalDiagonal_nonisotropicLastShellOrbitMap]
      rw [horbitA]
      apply Subtype.ext
      funext i
      cases i using Fin.lastCases <;>
        simp [nonisotropicLastQuadraticShellMap, lastCoordinateVector]
    have hq : q ∈
        W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha ℚ :=
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_eq_last_iff
        W a ha ℚ q).1 horbitQ
    rcases hq with ⟨delta, hdelta⟩
    let deltaA := W.rationalCliffordGeneralSpinGroupEquivDiagonal delta
    refine ⟨deltaA, ?_⟩
    change
      V.rationalCliffordGeneralSpinGroupEquivDiagonal
          (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ
            (W.rationalCliffordGeneralSpinGroupEquivDiagonal.symm deltaA)) =
        gamma
    rw [W.rationalCliffordGeneralSpinGroupEquivDiagonal.symm_apply_apply]
    change
      W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ delta = q at hdelta
    rw [hdelta]
    exact V.rationalCliffordGeneralSpinGroupEquivDiagonal.apply_symm_apply gamma

/-- The rational shell point represented by a rational diagonal right coset.
The definition is a quotient lift and therefore contains no selected coset
representative. -/
def rationalNonisotropicLastShellCosetMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    ((W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) →
      W.nonisotropicLastQuadraticShell a ha ℚ :=
  Quotient.lift
    (fun gamma ↦
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha ℚ
        ((W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm gamma))
    (by
      intro gamma delta hrel
      apply nonisotropicLastQuadraticShellMap_rationalAdele_injective W a ha
      simp only
        [CliffordGeneralSpinIntrinsicPoint.rationalDiagonal_nonisotropicLastShellOrbitMap]
      apply
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_leftRel_iff
          W a ha _ _).1
      have hgamma :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalHom)
              ((W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm gamma) =
            (gamma : (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) := by
        change
          (((W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinGroupEquivDiagonal)
                ((W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm gamma) :
              (W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) = gamma
        rw [(W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinGroupEquivDiagonal).apply_symm_apply]
      have hdelta :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalHom)
              ((W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm delta) =
            (delta : (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) := by
        change
          (((W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinGroupEquivDiagonal)
                ((W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm delta) :
              (W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) = delta
        rw [(W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinGroupEquivDiagonal).apply_symm_apply]
      rw [hgamma, hdelta]
      rw [QuotientGroup.leftRel_apply]
      apply
        (W.mem_nonisotropicLastComplementGeneralSpinDiagonalImage_iff
          a ha (gamma⁻¹ * delta)).1
      change QuotientGroup.leftRel
        (W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)
          gamma delta at hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      exact hrel)

@[simp]
theorem rationalNonisotropicLastShellCosetMap_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (gamma : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
    W.rationalNonisotropicLastShellCosetMap a ha (QuotientGroup.mk gamma) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha ℚ
        ((W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm gamma) :=
  rfl

/-- The rational diagonal coset index is canonically equivalent to the
literal rational block shell.  Its forward map is the explicit quotient-lift
orbit map. -/
def rationalNonisotropicLastShellCosetEquiv
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    ((W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) ≃
      W.nonisotropicLastQuadraticShell a ha ℚ :=
  Equiv.ofBijective (W.rationalNonisotropicLastShellCosetMap a ha) (by
    constructor
    · intro xi eta hxi
      induction xi using Quotient.inductionOn with
      | _ gamma =>
          induction eta using Quotient.inductionOn with
          | _ delta =>
              apply Quotient.sound
              change QuotientGroup.leftRel
                (W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)
                  gamma delta
              rw [QuotientGroup.leftRel_apply]
              apply
                (W.mem_nonisotropicLastComplementGeneralSpinDiagonalImage_iff
                  a ha (gamma⁻¹ * delta)).2
              change
                (gamma : (W.nonisotropicLastExtension a ha
                  |>.FullAdelicCliffordGeneralSpinGroup))⁻¹ *
                    (delta : (W.nonisotropicLastExtension a ha
                      |>.FullAdelicCliffordGeneralSpinGroup)) ∈
                  W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
                    a ha RationalAdele
              rw [← QuotientGroup.leftRel_apply]
              apply
                (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_leftRel_iff
                  W a ha _ _).2
              rw [←
                rationalCliffordGeneralSpinFullAdelicDiagonalHom_equiv_symm
                  (W.nonisotropicLastExtension a ha) gamma,
                ←
                rationalCliffordGeneralSpinFullAdelicDiagonalHom_equiv_symm
                  (W.nonisotropicLastExtension a ha) delta]
              rw [←
                CliffordGeneralSpinIntrinsicPoint.rationalDiagonal_nonisotropicLastShellOrbitMap,
                ←
                CliffordGeneralSpinIntrinsicPoint.rationalDiagonal_nonisotropicLastShellOrbitMap]
              exact congrArg
                (W.nonisotropicLastQuadraticShellMap a ha
                  (Algebra.ofId ℚ RationalAdele)) hxi
    · intro y
      obtain ⟨q, hq⟩ :=
        CliffordGeneralSpinIntrinsicPoint.rational_nonisotropicLastShellOrbitMap_surjective
          W a ha y
      let gamma := (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinGroupEquivDiagonal) q
      refine ⟨QuotientGroup.mk gamma, ?_⟩
      simpa [gamma] using hq)

@[simp]
theorem rationalNonisotropicLastShellCosetEquiv_apply
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (xi : ((W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)) :
    W.rationalNonisotropicLastShellCosetEquiv a ha xi =
      W.rationalNonisotropicLastShellCosetMap a ha xi :=
  rfl

/-- Reindex a nonnegative rational shell-coset sum as the literal rational
block-shell sum. -/
theorem tsum_rationalNonisotropicLastShellCoset_eq_shell
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (F : W.nonisotropicLastQuadraticShell a ha ℚ → ℝ≥0∞) :
    (∑' xi, F (W.rationalNonisotropicLastShellCosetMap a ha xi)) =
      ∑' y, F y := by
  exact (W.rationalNonisotropicLastShellCosetEquiv a ha).tsum_eq F

/-- The existing full-adelic inverse orbit of a rational shell coset is the
ambient inverse orthogonal action on its literal rational shell vector. -/
theorem coe_fullAdelicNonisotropicLastRationalShellCosetInvOrbit_eq_action
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup))
    (xi : ((W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)) :
    (W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit
        a ha g xi).1 =
      (W.nonisotropicLastExtension a ha
        |>.fullAdelicCliffordGeneralSpinRationalVectorAction) g
          (W.rationalNonisotropicLastShellCosetMap a ha xi).1 := by
  induction xi using Quotient.inductionOn with
  | _ gamma =>
      rw [W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit_mk,
        W.rationalNonisotropicLastShellCosetMap_mk]
      rw [CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul]
      rw [←
        rationalCliffordGeneralSpinFullAdelicDiagonalHom_equiv_symm
          (W.nonisotropicLastExtension a ha) gamma]
      rw [←
        CliffordGeneralSpinIntrinsicPoint.rationalDiagonal_nonisotropicLastShellOrbitMap]
      change
        (g⁻¹).matrixPoint.1 *ᵥ
            (rationalAdeleVectorDiagonal (n + 1)
              (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
                W a ha ℚ
                ((W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm gamma)).1) =
          (g.matrixGroup⁻¹).1.1.1.mulVec
            (rationalAdeleVectorDiagonal (n + 1)
              (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
                W a ha ℚ
                ((W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinGroupEquivDiagonal).symm gamma)).1)
      rw [← CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe,
        CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup]

/-- The calibrated rational-orbit theta density is exactly the ordinary
literal sum over the rational nonisotropic block shell. -/
theorem fullAdelicNonisotropicLastShellThetaOrbitSum_eq_rationalShell
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (Phi : (Fin (n + 1) → RationalAdele) → ℝ≥0∞)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    W.fullAdelicNonisotropicLastShellThetaOrbitSum
        a ha (fun y ↦ Phi y.1) g =
      ∑' y : W.nonisotropicLastQuadraticShell a ha ℚ,
        (W.nonisotropicLastExtension a ha
          |>.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand)
            Phi g y.1 := by
  unfold fullAdelicNonisotropicLastShellThetaOrbitSum
  simp_rw [W.coe_fullAdelicNonisotropicLastRationalShellCosetInvOrbit_eq_action]
  exact W.tsum_rationalNonisotropicLastShellCoset_eq_shell a ha
    (fun y ↦
      (W.nonisotropicLastExtension a ha
        |>.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand)
          Phi g y.1)

end RationalQuadraticSpaceMatrix

end
