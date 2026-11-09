import SMSFormula.RationalCliffordGeneralSpinAdelicTopology
import SMSFormula.RationalCliffordSpinCandidateAdelicDiagonalTopology

/-!
# Topology of the rational intrinsic general-Spin diagonal

The rational diagonal in full-adelic intrinsic `GSpin` is discrete and
closed.  The same open rational-adele zero-neighborhood used for the Spin
candidate isolates the identity through the finite Clifford coordinates.
No crossed-integral or Tamagawa comparison is used.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

theorem rationalCliffordGeneralSpinFullAdelicDiagonalHom_injective :
    Function.Injective
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom := by
  intro x y hxy
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V ℚ
  apply Units.ext
  apply (V.cliffordCoordinateBaseChangeBasis ℚ).repr.injective
  ext u
  have hu := congrArg
    (fun z : V.FullAdelicCliffordGeneralSpinGroup =>
      (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
        (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u)
    hxy
  simp only [rationalCliffordGeneralSpinFullAdelicDiagonalHom,
    CliffordGeneralSpinIntrinsicPoint.mapGroupHom_apply,
    CliffordGeneralSpinIntrinsicPoint.map_cliffordUnit_coe,
    V.cliffordCoordinateBaseChangeBasis_repr_map] at hu
  exact (NumberField.AdeleRing.algebraMap_injective ℤ ℚ) hu

/-- An open identity-neighborhood requiring all Clifford coordinate
differences to lie in the standard adelic neighborhood which meets `ℚ` only
at zero. -/
def fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood :
    Set V.FullAdelicCliffordGeneralSpinGroup :=
  {g | ∀ u,
    (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
        (g.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u -
      (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
        ((1 : V.FullAdelicCliffordGeneralSpinGroup).cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u ∈
      rationalAdeleDiagonalZeroNeighborhood}

theorem isOpen_fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood :
    IsOpen V.fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood := by
  rw [show V.fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood =
      ⋂ u, {g : V.FullAdelicCliffordGeneralSpinGroup |
        (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
            (g.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u -
          (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
            ((1 : V.FullAdelicCliffordGeneralSpinGroup).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u ∈
          rationalAdeleDiagonalZeroNeighborhood} by
    ext g
    simp [fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood]]
  apply isOpen_iInter_of_finite
  intro u
  exact isOpen_rationalAdeleDiagonalZeroNeighborhood.preimage
    ((V.continuous_cliffordGeneralSpinCliffordCoordinate RationalAdele u).sub
      continuous_const)

theorem
    rationalCliffordGeneralSpinFullAdelicDiagonalHom_mem_identityNeighborhood_iff
    (q : V.RationalCliffordGeneralSpinGroup) :
    V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q ∈
        V.fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood ↔
      q = 1 := by
  constructor
  · intro hq
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V ℚ
    apply Units.ext
    apply (V.cliffordCoordinateBaseChangeBasis ℚ).repr.injective
    ext u
    have hu := hq u
    have hone :
        (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
            ((1 : V.FullAdelicCliffordGeneralSpinGroup).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u =
          algebraMap ℚ RationalAdele
            ((V.cliffordCoordinateBaseChangeBasis ℚ).repr
              ((1 : V.RationalCliffordGeneralSpinGroup).cliffordUnit :
                V.cliffordCoordinateBaseChangeAlgebra ℚ) u) := by
      have h := congrArg
        (fun z : V.FullAdelicCliffordGeneralSpinGroup =>
          (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
            (z.cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra RationalAdele) u)
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom.map_one
      simpa only [rationalCliffordGeneralSpinFullAdelicDiagonalHom,
        CliffordGeneralSpinIntrinsicPoint.mapGroupHom_apply,
        CliffordGeneralSpinIntrinsicPoint.map_cliffordUnit_coe,
        V.cliffordCoordinateBaseChangeBasis_repr_map] using h.symm
    rw [hone] at hu
    have hu' : algebraMap ℚ RationalAdele
        ((V.cliffordCoordinateBaseChangeBasis ℚ).repr
            (q.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℚ) u -
          (V.cliffordCoordinateBaseChangeBasis ℚ).repr
            ((1 : V.RationalCliffordGeneralSpinGroup).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra ℚ) u) ∈
        rationalAdeleDiagonalZeroNeighborhood := by
      simpa only [rationalCliffordGeneralSpinFullAdelicDiagonalHom,
        CliffordGeneralSpinIntrinsicPoint.mapGroupHom_apply,
        CliffordGeneralSpinIntrinsicPoint.map_cliffordUnit_coe,
        V.cliffordCoordinateBaseChangeBasis_repr_map, map_sub,
        map_one] using hu
    exact sub_eq_zero.mp
      ((algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff _).mp hu')
  · rintro rfl
    intro u
    simp only [map_one, sub_self]
    exact (algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff 0).mpr rfl

noncomputable instance
    rationalCliffordGeneralSpinFullAdelicDiagonalSubgroupDiscreteTopology :
    DiscreteTopology
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
  apply discreteTopology_of_isOpen_singleton_one
  have hopen :=
    V.isOpen_fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood
  have hpre := hopen.preimage
    (continuous_subtype_val : Continuous
      (fun g : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup =>
        (g : V.FullAdelicCliffordGeneralSpinGroup)))
  rw [show
      (fun g : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup =>
        (g : V.FullAdelicCliffordGeneralSpinGroup)) ⁻¹'
          V.fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood =
        ({1} : Set
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) by
    ext g
    constructor
    · intro hg
      rcases g.2 with ⟨q, hq⟩
      have hqmem : V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q ∈
          V.fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood := by
        rw [hq]
        exact hg
      have hqone :=
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom_mem_identityNeighborhood_iff
          q).mp hqmem
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hq, hqone, map_one]
      rfl
    · intro hg
      have hgone : g = 1 := Set.mem_singleton_iff.mp hg
      subst g
      change (1 : V.FullAdelicCliffordGeneralSpinGroup) ∈
        V.fullAdelicCliffordGeneralSpinRationalDiagonalIdentityNeighborhood
      rw [← V.rationalCliffordGeneralSpinFullAdelicDiagonalHom.map_one]
      exact
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom_mem_identityNeighborhood_iff
          1).mpr rfl] at hpre
  exact hpre

theorem isClosed_rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :
    IsClosed
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :
        Set V.FullAdelicCliffordGeneralSpinGroup) := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : T2Space V.FullAdelicCliffordGeneralSpinGroup :=
    V.cliffordGeneralSpinIntrinsicPointT2Space RationalAdele
  exact Subgroup.isClosed_of_discrete

end RationalQuadraticSpaceMatrix
