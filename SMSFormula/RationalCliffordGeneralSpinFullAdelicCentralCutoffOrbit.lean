import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOrbitCentralSubgroup
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicCylinderOrbit

/-!
# The full-adelic orbit of a central cutoff with full real special orthogonal group

For the central cutoff `K = {ν(g_∞)² = 1, toSO(g_∞) ∈ SO(ℝ), g_f ∈ K_f}` a full-adelic block shell
point `y` lies in `K · x_old` exactly when its finite part lies in `K_f · x_old`: there is no
condition at the real place.  Indeed, real transitivity gives a real lift of the real part, the
real/finite equivalence assembles it with a finite witness, and the central-scalar
correction `g = k · scalar(u)` (scalars fix `x_old`) moves the assembled point into `K` without
changing its orbit.  Together with the finite-adelic cylinder decomposition this describes the
orbit set of the bad-place identity as `X(ℝ) × ∏_v (local orbit)`.  Nothing is chosen beyond
existence of lifts.
-/

noncomputable section

open Set PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- Full-adelic shell points are determined by their real and finite components. -/
theorem nonisotropicLastQuadraticShell_ext_of_real_finite
    {y y' : W.nonisotropicLastQuadraticShell a ha RationalAdele}
    (hR : W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinRealAlgHom y =
      W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinRealAlgHom y')
    (hF : W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinFiniteAlgHom y =
      W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinFiniteAlgHom y') :
    y = y' := by
  apply Subtype.ext
  funext i
  apply Prod.ext
  · apply rationalInfiniteAdeleRingEquivReal.injective
    exact congrFun (congrArg Subtype.val hR) i
  · exact congrFun (congrArg Subtype.val hF) i

/-- The full-adelic orbit of the central cutoff with full real `SO`: `y ∈ K · x_old` iff the finite
part of `y` lies in `K_f · x_old`. -/
theorem mem_image_shellOrbit_centralCutoffSubgroup_top_iff [NeZero n]
    (Kf : Subgroup (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)
    (y : W.nonisotropicLastQuadraticShell a ha RationalAdele) :
    y ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
        ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤ Kf : Set _) ↔
      W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinFiniteAlgHom y ∈
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalFiniteAdele) ''
          (Kf : Set _) := by
  let V := W.nonisotropicLastExtension a ha
  have hfin : ∀ g : V.FullAdelicCliffordGeneralSpinGroup,
      W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinFiniteAlgHom
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele g) =
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalFiniteAdele
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).2 :=
    fun g ↦ CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality W a ha
      fullAdelicCliffordGeneralSpinFiniteAlgHom g
  have hreal : ∀ g : V.FullAdelicCliffordGeneralSpinGroup,
      W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinRealAlgHom
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele g) =
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℝ
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1 :=
    fun g ↦ CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality W a ha
      fullAdelicCliffordGeneralSpinRealAlgHom g
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).2,
      ((V.mem_centralCutoffSubgroup_iff ⊤ Kf g).1 hg).2.2, (hfin g).symm⟩
  · rintro ⟨kf, hkf, hkfy⟩
    obtain ⟨zR, hzR⟩ := CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective
      W a ha ℝ (W.nonisotropicLastQuadraticShellMap a ha fullAdelicCliffordGeneralSpinRealAlgHom y)
    let g : V.FullAdelicCliffordGeneralSpinGroup :=
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm (zR, kf)
    have hgc : V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g = (zR, kf) :=
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply _
    have hgset : g ∈ V.centralCutoffSet Set.univ (⊤ : Subgroup (V.specialOrthogonalMatrixGroup ℝ))
        (Kf : Set _) := by
      rw [mem_centralCutoffSet_iff, hgc]
      exact ⟨Set.mem_univ _, Subgroup.mem_top _, hkf⟩
    have hgy : CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele g =
        y := by
      refine W.nonisotropicLastQuadraticShell_ext_of_real_finite a ha ?_ ?_
      · rw [hreal g, hgc]; exact hzR
      · rw [hfin g, hgc]; exact hkfy
    rw [← hgy]
    exact W.nonisotropicLastShellOrbitMap_mem_image_centralCutoffSubgroup a ha Set.univ ⊤ Kf hgset

end RationalQuadraticSpaceMatrix
