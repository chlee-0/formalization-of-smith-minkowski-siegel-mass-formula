import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralCentralFactor
import SMSFormula.QuadraticPadicCayleyGoodPlaceHeightOne

/-! The good-place ledger in the GSpin horizontal masses. The integral
Cartan–Dieudonné lift (unit reflection words, `ofReflectionPairs`) is valid for
every rational form of rank at least two at every odd unimodular place with
integral Clifford structure; it does not need a lattice presentation. Hence
the GSpin central factor `v^G_{V,v} = Haar(ℤ_p^×) · vol_SO(V, v)` holds for
`V = W ⊕ ⟨a⟩` and for `W` at their common horizontal odd good places, and the
common factor `Haar(ℤ_p^×)` cancels:

`v^G_{W⊕⟨a⟩,v} / v^G_{W,v} = |r| · ν(ℤ_p) · λ(X_a(ℤ_p))`

at every such place whose residue prime is outside the explicit finite
exceptional set. These are the ledger's raw GSpin masses; the
place conditions are the finite bad sets. No chart, section or
normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open QuadraticMap.ReflectionWord
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix

local instance gpLedgerPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance gpLedgerDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

section Lift

variable {m : ℕ} (V : RationalQuadraticSpaceMatrix m)

/-- The integral Cartan–DIEUDONNÉ lift for every rational form of rank at
least two at an odd unimodular place with integral Clifford structure. -/
theorem exists_integral_padicCliffordGeneralSpin_toSpecialOrthogonal_eq_of_two_le
    (hm : 2 ≤ m) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvOdd : v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvStructure : V.CliffordGeneralSpinIntegralStructureAt v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    ∃ x : V.HeightOnePadicCliffordGeneralSpinGroup v,
      V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v).1 x ∧
        V.padicCliffordGeneralSpinToSpecialOrthogonalHom (Rat.HeightOneSpectrum.primesEquiv v).1 x =
          g.1 := by
  let P := V.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces hm v hvOdd
  obtain ⟨xs, hxs, _hlen⟩ :=
    CliffordSpinCandidateIntegralSpinorRangeGoodPlace.exists_unitReflectionWord_eval_eq V P g
  let Q := V.commutativeScalarExtensionQuadraticForm ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  let word := P.unitReflectionWordToPadic xs
  have hwordEval : eval Q word =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 :=
    P.eval_unitReflectionWordToPadic_eq_original g xs hxs
  have hdet : LinearMap.det (eval Q word).toLinearEquiv.toLinearMap = 1 := by
    rw [hwordEval]
    exact detOneIsometryGroup_det Q
      (V.specialOrthogonalMatrixGroupDetOneIsometryHom ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1)
  obtain ⟨ps, hps⟩ := exists_pairs_flatten_eq Q word (even_length_of_det_eval_eq_one Q word hdet)
  have hpairsEval : eval Q (flattenPairs Q ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 := by
    rw [hps, hwordEval]
  have hpairsIntegral : V.AreIntegralReflectionPairsAt v ps :=
    V.areIntegralReflectionPairsAt_of_unitReflectionWord P xs ps hps
  refine ⟨CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs V
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 ps hpairsEval,
    V.ofReflectionPairs_isIntegral v hvStructure g ps hpairsEval hpairsIntegral, ?_⟩
  exact CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs_matrixGroup V
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 ps hpairsEval

/-- Central factor for every rational form of rank at least two at an odd
unimodular horizontal good place. -/
theorem padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul_heightOne_of_two_le
    (hm : 2 ≤ m) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvOdd : v.1 ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≠ 2) :
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 =
      padicIntegralUnitsHaarMass (Rat.HeightOneSpectrum.primesEquiv v.1).1 *
        V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  have hlift : ∀ g : V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      g ∈ V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 →
      ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
        V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1 y ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y = g := by
    intro g hg
    have hg' : g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v.1 := by
      have := congrArg (fun T ↦ g ∈ T) (V.padicSpecialOrthogonalIntegralSubgroup_eq_heightOne v.1)
      simp only at this
      exact this.mp hg
    obtain ⟨x, hx, hxg⟩ := V.exists_integral_padicCliffordGeneralSpin_toSpecialOrthogonal_eq_of_two_le
      hm v.1 hvOdd
      (V.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
        v.1 (fun hv ↦ v.2 (Finset.mem_union_right S hv))) ⟨g, hg'⟩
    exact ⟨x, hx, hxg⟩
  rw [V.padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul S v hp2 hlift,
    heightOnePadicSpecialOrthogonalIntegralVolume,
    V.padicSpecialOrthogonalIntegralSubgroup_eq_heightOne v.1]

end Lift

/-- The common central mass `Haar(ℤ_p^×)` is positive and finite. -/
theorem padicIntegralUnitsHaarMass_pos_lt_top (p : ℕ) [Fact p.Prime] :
    0 < padicIntegralUnitsHaarMass p ∧ padicIntegralUnitsHaarMass p < ∞ := by
  letI : MeasurableSpace ℚ_[p]ˣ := borel _
  haveI : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩
  exact ⟨(isOpen_padicIntegralUnitsSubgroup p).measure_pos _ ⟨1, (padicIntegralUnitsSubgroup p).one_mem⟩,
    (isCompact_padicIntegralUnitsSubgroup p).measure_lt_top⟩

section Ledger

local instance gpLedgerPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance gpLedgerPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- GSpin ledger: at every height-one
place outside the horizontal and odd-unimodular bad sets of `W ⊕ ⟨a⟩` and
`W` whose residue prime is outside the explicit exceptional set,
`v^G_{W⊕⟨a⟩,v} / v^G_{W,v} = |r| ν(ℤ_p) λ(X_a(ℤ_p))`. -/
theorem gspinHorizontalIntegralVolume_div_eq_ledger_of_notMem (hn : 2 ≤ n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvW : v ∉ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvOddExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvOddW : v ∉ W.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (n+1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasRegion
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint i) :
    (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalIntegralVolume v /
        W.padicCliffordGeneralSpinHorizontalIntegralVolume v =
      ((‖W.lastOrbitGaugeRatio a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖₊ : ℝ≥0∞) *
          ν (closedBall 0 1)) *
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasGlue
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint tH ν
          (Padic.unitHaar (Rat.HeightOneSpectrum.primesEquiv v).1 (Fin (n+1)))
          (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] a) {y | ‖y.1‖ ≤ 1} := by
  obtain ⟨h2, -, -, -⟩ := W.goodPlace_of_notMem_exceptionalPrimes a ha _ hp
  let vExt : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinHorizontalIntegralPlace ∅ :=
    ⟨v, by simpa using hvExt⟩
  let vW : W.CliffordGeneralSpinHorizontalIntegralPlace ∅ := ⟨v, by simpa using hvW⟩
  have hExt := (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul_heightOne_of_two_le
    (by omega) ∅ vExt hvOddExt h2
  have hW := W.padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul_heightOne_of_two_le
    hn ∅ vW hvOddW h2
  obtain ⟨hpos, hfin⟩ := padicIntegralUnitsHaarMass_pos_lt_top (Rat.HeightOneSpectrum.primesEquiv v).1
  change (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalIntegralVolume vExt.1 /
    W.padicCliffordGeneralSpinHorizontalIntegralVolume vW.1 = _
  rw [hExt, hW, ENNReal.mul_div_mul_left _ _ hpos.ne' hfin.ne]
  exact W.heightOneIntegralVolume_div_eq_ledger_of_notMem a ha (by omega) v hp ν point hpoint tH hcover

end Ledger

end RationalQuadraticSpaceMatrix
