import SMSFormula.RationalCliffordSpinCandidateAdelicHaarPrecursor

/-!
# Topology of the rational Clifford--Spin diagonal

The rational diagonal in the full adelic Clifford--Spin candidate is
discrete and closed.  The proof is deliberately coordinate-level: a rational
adele which is integral at every finite place and lies in the real interval
`(-1, 1)` is zero.  Pulling this open zero-neighborhood back through all
finite Spin coordinates isolates the identity of the rational diagonal.

No rational or local point-surjectivity statement for the Spin-to-`SO` map is
used here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## An open zero-neighborhood isolating diagonal rational adeles -/

/-- Full rational adeles whose infinite component lies in `(-1, 1)` and whose
finite component is integral at every finite place. -/
def rationalAdeleDiagonalZeroNeighborhood : Set RationalAdele :=
  {a | rationalInfiniteAdeleHomeomorphReal a.1 ∈ Set.Ioo (-1 : ℝ) 1 ∧
    a.2 ∈ integralFiniteAdeleSubring}

/-- The adelic zero-neighborhood used to isolate the rational diagonal is
open. -/
theorem isOpen_rationalAdeleDiagonalZeroNeighborhood :
    IsOpen rationalAdeleDiagonalZeroNeighborhood := by
  exact
    (isOpen_Ioo.preimage
      (rationalInfiniteAdeleHomeomorphReal.continuous.comp continuous_fst)).inter
      (isOpen_integralFiniteAdeleSubring.preimage continuous_snd)

private theorem rationalAdele_algebraMap_fst (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 =
      algebraMap ℚ RationalInfiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

private theorem rationalAdele_algebraMap_snd (q : ℚ) :
    (algebraMap ℚ RationalAdele q).2 =
      algebraMap ℚ RationalFiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q

private theorem rationalInfiniteAdele_algebraMap_equivReal (q : ℚ) :
    rationalInfiniteAdeleHomeomorphReal
        (algebraMap ℚ RationalInfiniteAdele q) =
      algebraMap ℚ ℝ q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℚ RationalInfiniteAdele))
      (algebraMap ℚ ℝ)) q

/-- The chosen open neighborhood meets the diagonal copy of `ℚ` only in
zero. -/
theorem algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff (q : ℚ) :
    algebraMap ℚ RationalAdele q ∈ rationalAdeleDiagonalZeroNeighborhood ↔
      q = 0 := by
  constructor
  · rintro ⟨hinf, hfin⟩
    rw [rationalAdele_algebraMap_snd] at hfin
    rcases (rational_mem_integralFiniteAdeleSubring_iff q).mp hfin with ⟨z, rfl⟩
    rw [rationalAdele_algebraMap_fst,
      rationalInfiniteAdele_algebraMap_equivReal] at hinf
    norm_num at hinf
    have hzlow : (-1 : ℤ) < z := by
      exact_mod_cast hinf.1
    have hzhigh : z < (1 : ℤ) := by
      exact_mod_cast hinf.2
    have hz : z = 0 := by omega
    simp [hz]
  · rintro rfl
    constructor
    · rw [rationalAdele_algebraMap_fst,
        rationalInfiniteAdele_algebraMap_equivReal]
      norm_num
    · rw [rationalAdele_algebraMap_snd]
      exact (rational_mem_integralFiniteAdeleSubring_iff 0).mpr ⟨0, by simp⟩

/-! ## The rational Clifford--Spin diagonal -/

/-- Scalar extension from rational to full-adelic candidate points is
injective. -/
theorem rationalCliffordSpinCandidateFullAdelicDiagonalHom_injective :
    Function.Injective
      V.rationalCliffordSpinCandidateFullAdelicDiagonalHom := by
  intro x y hxy
  apply AlgHom.ext
  intro c
  have hc := congrArg
    (fun z : V.FullAdelicCliffordSpinCandidateGroup => z c) hxy
  change algebraMap ℚ RationalAdele (x c) =
    algebraMap ℚ RationalAdele (y c) at hc
  exact (NumberField.AdeleRing.algebraMap_injective ℤ ℚ) hc

/-- An open identity-neighborhood in the full-adelic candidate group obtained
by requiring every finite coordinate difference from the identity to lie in
the adelic zero-neighborhood above. -/
def fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood :
    Set V.FullAdelicCliffordSpinCandidateGroup :=
  {g |
    (∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) -
      (1 : V.FullAdelicCliffordSpinCandidateGroup)
        (V.cliffordSpinCandidateCliffordCoordinate s) ∈
        rationalAdeleDiagonalZeroNeighborhood) ∧
    ∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) -
      (1 : V.FullAdelicCliffordSpinCandidateGroup)
        (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
        rationalAdeleDiagonalZeroNeighborhood}

/-- The finite-coordinate identity-neighborhood is open. -/
theorem
    isOpen_fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood :
    IsOpen
      V.fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood := by
  rw [show
      V.fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood =
        (⋂ s, {g : V.FullAdelicCliffordSpinCandidateGroup |
          g (V.cliffordSpinCandidateCliffordCoordinate s) -
            (1 : V.FullAdelicCliffordSpinCandidateGroup)
              (V.cliffordSpinCandidateCliffordCoordinate s) ∈
              rationalAdeleDiagonalZeroNeighborhood}) ∩
        ⋂ i, ⋂ j, {g : V.FullAdelicCliffordSpinCandidateGroup |
          g (V.cliffordSpinCandidateMatrixCoordinate i j) -
            (1 : V.FullAdelicCliffordSpinCandidateGroup)
              (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
              rationalAdeleDiagonalZeroNeighborhood} by
    ext g
    simp [fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood]]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro s
    exact isOpen_rationalAdeleDiagonalZeroNeighborhood.preimage
      ((V.continuous_cliffordSpinCandidateCliffordCoordinate RationalAdele s).sub
        continuous_const)
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_rationalAdeleDiagonalZeroNeighborhood.preimage
      ((V.continuous_cliffordSpinCandidateMatrixCoordinate RationalAdele i j).sub
        continuous_const)

/-- A rational candidate point lies in the isolating full-adelic
identity-neighborhood exactly when it is the identity. -/
theorem rationalCliffordSpinCandidateFullAdelicDiagonalHom_mem_identityNeighborhood_iff
    (q : V.RationalCliffordSpinCandidateGroup) :
    V.rationalCliffordSpinCandidateFullAdelicDiagonalHom q ∈
        V.fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood ↔
      q = 1 := by
  constructor
  · rintro ⟨hcliff, hmatrix⟩
    apply V.cliffordSpinCandidatePointCoordinateMap_injective ℚ
    apply Prod.ext
    · funext s
      have hs := hcliff s
      rw [← V.rationalCliffordSpinCandidateFullAdelicDiagonalHom.map_one] at hs
      have hs' : algebraMap ℚ RationalAdele
        (q (V.cliffordSpinCandidateCliffordCoordinate s) -
          (1 : V.RationalCliffordSpinCandidateGroup)
            (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
          rationalAdeleDiagonalZeroNeighborhood := by
        simpa [rationalCliffordSpinCandidateFullAdelicDiagonalHom,
          cliffordSpinCandidateGroupMap_apply] using hs
      exact sub_eq_zero.mp
        ((algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff _).mp hs')
    · ext i j
      have hij := hmatrix i j
      rw [← V.rationalCliffordSpinCandidateFullAdelicDiagonalHom.map_one] at hij
      have hij' : algebraMap ℚ RationalAdele
        (q (V.cliffordSpinCandidateMatrixCoordinate i j) -
          (1 : V.RationalCliffordSpinCandidateGroup)
            (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
          rationalAdeleDiagonalZeroNeighborhood := by
        simpa [rationalCliffordSpinCandidateFullAdelicDiagonalHom,
          cliffordSpinCandidateGroupMap_apply] using hij
      exact sub_eq_zero.mp
        ((algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff _).mp hij')
  · rintro rfl
    constructor
    · intro s
      simp only [map_one, sub_self]
      exact
        (algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff 0).mpr rfl
    · intro i j
      simp only [map_one, sub_self]
      exact
        (algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff 0).mpr rfl

/-- The rational diagonal carries the discrete topology induced from the full
adelic candidate group. -/
noncomputable instance
    rationalCliffordSpinCandidateFullAdelicDiagonalSubgroupDiscreteTopology :
    DiscreteTopology
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
  apply discreteTopology_of_isOpen_singleton_one
  have hopen :=
    V.isOpen_fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood
  have hpre := hopen.preimage
    (continuous_subtype_val : Continuous
      (fun g : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup =>
        (g : V.FullAdelicCliffordSpinCandidateGroup)))
  rw [show
      (fun g : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup =>
        (g : V.FullAdelicCliffordSpinCandidateGroup)) ⁻¹'
          V.fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood =
        ({1} : Set
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup) by
    ext g
    constructor
    · intro hg
      rcases g.2 with ⟨q, hq⟩
      have hqmem : V.rationalCliffordSpinCandidateFullAdelicDiagonalHom q ∈
          V.fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood := by
        rw [hq]
        exact hg
      have hqone :=
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom_mem_identityNeighborhood_iff
          q).mp hqmem
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hq, hqone, map_one]
      rfl
    · intro hg
      have hgone : g = 1 := Set.mem_singleton_iff.mp hg
      subst g
      change (1 : V.FullAdelicCliffordSpinCandidateGroup) ∈
        V.fullAdelicCliffordSpinCandidateRationalDiagonalIdentityNeighborhood
      rw [← V.rationalCliffordSpinCandidateFullAdelicDiagonalHom.map_one]
      exact
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom_mem_identityNeighborhood_iff
          1).mpr rfl] at hpre
  exact hpre

/-- The rational diagonal is a closed subgroup of the full-adelic candidate
group. -/
theorem isClosed_rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :
    IsClosed
      (V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :
        Set V.FullAdelicCliffordSpinCandidateGroup) := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      T2Space (v.adicCompletion ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.symm.t2Space
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : T2Space V.FullAdelicCliffordSpinCandidateGroup :=
    V.cliffordSpinCandidateGroupT2Space RationalAdele
  exact Subgroup.isClosed_of_discrete

/-! ## Compatibility with the existing abstract left quotient -/

/-- The standard quotient topology on the left-coset carrier, generated by
its canonical map. -/
instance fullAdelicCliffordSpinCandidateLeftQuotientTopologicalSpace :
    TopologicalSpace V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  TopologicalSpace.coinduced
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap inferInstance

/-- The existing project-local left-coset carrier is equipped by Mathlib with
the quotient topology generated by the same `Quot.mk` used in
`fullAdelicCliffordSpinCandidateLeftQuotientMap`.  Thus its canonical map is
literally a quotient map.  The separately installed measurable structure is
the map-generated measurable structure for this same function. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap :
    Topology.IsQuotientMap
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap := by
  exact
    { isCoinducing := ⟨rfl⟩
      surjective := Quot.mk_surjective }

/-- In particular, the canonical map to the existing abstract left quotient
is continuous for the standard quotient topology. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_continuous :
    Continuous V.fullAdelicCliffordSpinCandidateLeftQuotientMap :=
  Topology.IsQuotientMap.continuous
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap

end RationalQuadraticSpaceMatrix
