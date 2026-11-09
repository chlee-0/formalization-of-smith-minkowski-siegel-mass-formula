import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitIdentity
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicShell

/-!
# The finite-adelic orbit of a cylinder subgroup is the product of the local orbits

For a supplied block `S` and supplied local subgroups `s_v` on `S ∪ bad`, a finite-adelic block
shell point `y` lies in the shell orbit of the cylinder subgroup (integral components off
`S ∪ bad`, components in `s_v` on `S ∪ bad`) exactly when every local component of `y` lies in the
corresponding local orbit: in `s_v · x_old` on `S ∪ bad`, and in the orbit of the integral
locus elsewhere.

The forward direction is naturality of the shell orbit map.  For the converse the local
witnesses form a principal restricted family (they are integral off the finite set `S ∪ bad`), so
the restricted-family assembly produces a finite-adelic GSpin point of the cylinder with
those components, whose shell orbit has the prescribed components, hence equals `y`.  Local
witnesses are obtained from the existence hypotheses; no section or representative is chosen
beyond that existence.
-/

noncomputable section

open Set PositiveDefiniteIntegralLattice Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance faCylOrbitDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance faCylOrbitPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The local component of a finite-adelic shell orbit point is the shell orbit of the local
component. -/
theorem shellMap_heightOne_orbit (x : (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalFiniteAdele x) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        ((W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x) :=
  CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality W a ha
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) x

/-- Finite-adelic shell points with equal local components are equal. -/
theorem nonisotropicLastQuadraticShell_ext_of_heightOne
    {y y' : W.nonisotropicLastQuadraticShell a ha RationalFiniteAdele}
    (h : ∀ v, W.nonisotropicLastQuadraticShellMap a ha
        (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y =
      W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y') :
    y = y' := by
  apply Subtype.ext
  funext i
  ext v
  apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
  exact congrFun (congrArg Subtype.val (h v)) i

/-- The finite-adelic orbit of a cylinder subgroup is the product of the local orbits. -/
theorem mem_image_shellOrbit_cylinderSubgroup_iff (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (y : W.nonisotropicLastQuadraticShell a ha RationalFiniteAdele) :
    y ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalFiniteAdele) ''
        ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S s : Set _) ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        (∀ h : v ∈ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces,
          W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y ∈
            (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)) ∧
        (v ∉ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces →
          ∃ z : (W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v,
            (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral
              (Rat.HeightOneSpectrum.primesEquiv v).1 z ∧
            CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z =
              W.nonisotropicLastQuadraticShellMap a ha
                (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y) := by
  let V := W.nonisotropicLastExtension a ha
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ V.cliffordGeneralSpinHorizontalSourceCylinder S (fun v ↦ (s v : Set _)) := hx
    have hmem := (V.mem_cliffordGeneralSpinHorizontalSourceCylinder_iff S (fun v ↦ (s v : Set _)) x).1 hx'
    intro v
    refine ⟨fun h ↦ ⟨V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x, hmem.2 ⟨v, h⟩,
      (W.shellMap_heightOne_orbit a ha x v).symm⟩, fun h ↦
      ⟨V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x, hmem.1 v h,
        (W.shellMap_heightOne_orbit a ha x v).symm⟩⟩
  · intro hy
    classical
    let localLift : V.HeightOnePadicCliffordGeneralSpinGroupProduct := fun v ↦
      if h : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then
        Classical.choose ((hy v).1 h) else Classical.choose ((hy v).2 h)
    have hlocalIn : ∀ v (h : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces),
        localLift v ∈ s ⟨v, h⟩ ∧
          CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (localLift v) =
            W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y := by
      intro v h
      simp only [localLift, dif_pos h]
      exact Classical.choose_spec ((hy v).1 h)
    have hlocalOut : ∀ v (h : v ∉ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces),
        V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v).1 (localLift v) ∧
          CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (localLift v) =
            W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y := by
      intro v h
      simp only [localLift, dif_neg h]
      exact Classical.choose_spec ((hy v).2 h)
    have horbit : ∀ v, CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (localLift v) =
          W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y := by
      intro v
      by_cases h : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      · exact (hlocalIn v h).2
      · exact (hlocalOut v h).2
    have hrestricted : V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily localLift := by
      filter_upwards [(S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces).eventually_cofinite_notMem]
        with v hv
      exact (hlocalOut v hv).1
    let fam : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily := ⟨localLift, hrestricted⟩
    let z := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly fam
    have hzLocal : ∀ v, V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z = localLift v :=
      fun v ↦ congrFun (V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly fam) v
    have hzmem : z ∈ V.cliffordGeneralSpinHorizontalSourceCylinder S (fun v ↦ (s v : Set _)) := by
      refine (V.mem_cliffordGeneralSpinHorizontalSourceCylinder_iff S (fun v ↦ (s v : Set _)) z).2
        ⟨fun v hv ↦ ?_, fun v ↦ ?_⟩
      · change V.PadicCliffordGeneralSpinIsIntegral _
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z)
        rw [hzLocal v]
        exact (hlocalOut v hv).1
      · change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 z ∈ s v
        rw [hzLocal v.1]
        exact (hlocalIn v.1 v.2).1
    refine ⟨z, hzmem, W.nonisotropicLastQuadraticShell_ext_of_heightOne a ha fun v ↦ ?_⟩
    rw [W.shellMap_heightOne_orbit a ha z v, hzLocal v, horbit v]

/-- At a good place, the integral-locus orbit is the integral shell: off the odd-unimodular
bad places and the horizontal bad places, with `a` a local unit, a local shell point of a
finite-adelic shell point is the orbit of an integral GSpin point exactly when its coordinates are
integral. -/
theorem exists_integral_orbit_eq_iff [NeZero n] (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hodd : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hbad : v ∉ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : finiteAdelicUnitHeightOneComponentHom v
        (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 a ha)) ∈
      padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1)
    (y : W.nonisotropicLastQuadraticShell a ha RationalFiniteAdele) :
    (∃ z : (W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v,
        (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v).1 z ∧
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z =
          W.nonisotropicLastQuadraticShellMap a ha
            (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y) ↔
      ∀ i, finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  constructor
  · rintro ⟨z, hz, hzy⟩ i
    have hcoord := congrFun (congrArg Subtype.val hzy) i
    change (z.matrixGroup.1.1.1 *ᵥ lastCoordinateVector) i =
      finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) at hcoord
    change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈ _
    rw [← hcoord]
    have hmat := ((W.nonisotropicLastExtension a ha).mem_padicSpecialOrthogonalIntegralSubgroup_iff
      _ z.matrixGroup).1 hz.2.2.2
    simpa [lastCoordinateVector, Matrix.mulVec_single_one] using hmat.1 i (Fin.last n)
  · intro hy
    exact W.exists_integral_heightOne_nonisotropicLastShellOrbitMap_eq a ha v hodd
      ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
        v hbad) y hy haunit

/-- The finite-adelic orbit of a cylinder subgroup in integral form: if the supplied block contains
the odd-unimodular bad places and `a` is a local unit off `S ∪ bad`, then
`y ∈ cyl(S,s)·x_old ⟺ (y_v ∈ s_v·x_old on S ∪ bad) ∧ (y_v integral off S ∪ bad)`. -/
theorem mem_image_shellOrbit_cylinderSubgroup_iff_integral [NeZero n]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hodd : (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 a ha)) ∈
        padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1)
    (y : W.nonisotropicLastQuadraticShell a ha RationalFiniteAdele) :
    y ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalFiniteAdele) ''
        ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S s : Set _) ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        (∀ h : v ∈ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces,
          W.nonisotropicLastQuadraticShellMap a ha (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y ∈
            (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)) ∧
        (v ∉ S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces →
          ∀ i, finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  rw [W.mem_image_shellOrbit_cylinderSubgroup_iff a ha S s y]
  refine forall_congr' fun v ↦ and_congr_right fun _ ↦ imp_congr_right fun hv ↦ ?_
  exact W.exists_integral_orbit_eq_iff a ha v (fun h ↦ hv (hodd h))
    (fun h ↦ hv (Finset.mem_union_right _ h)) (haunit v hv) y

end RationalQuadraticSpaceMatrix
