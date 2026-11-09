import SMSFormula.RationalCliffordSpinCandidateAdelicDiagonalTopology

/-!
# Topology of the rational left quotient of the adelic Spin candidate

The existing project-local left-coset carrier is a literal `Quot`.  This file
proves that its canonical map is open, that the quotient is Hausdorff,
locally compact, and second countable, and compares its quotient topology with
the already-installed map-generated measurable structure.

No fundamental domain, quotient measure, invariant-differential
normalization, condition (K), Ono comparison, or Spin Tamagawa number is
constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Hausdorffness of the full-adelic carrier -/

/-- The full-adelic Spin-candidate carrier is Hausdorff.  The required
Hausdorff instances on rational adeles are assembled locally to avoid adding
new global instances to the underlying adelic presentation. -/
noncomputable instance fullAdelicCliffordSpinCandidateGroupT2Space :
    T2Space V.FullAdelicCliffordSpinCandidateGroup := by
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
  exact V.cliffordSpinCandidateGroupT2Space RationalAdele

/-! ## Openness of the canonical quotient map -/

/-- The inverse image of the quotient image of a set is its union of rational
left translates. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_preimage_image
    (U : Set V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap ⁻¹'
        (V.fullAdelicCliffordSpinCandidateLeftQuotientMap '' U) =
      ⋃ gamma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
        (fun x : V.FullAdelicCliffordSpinCandidateGroup =>
          (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x) '' U := by
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    have hrel : IsLeftCosetRelated
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup u x := by
      exact (leftCoset_mk_eq_iff
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup u x).mp hux
    rcases hrel with ⟨gamma, rfl⟩
    exact Set.mem_iUnion.mpr ⟨gamma, ⟨u, hu, rfl⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨gamma, u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    exact (leftCosetMap_gamma_mul
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup gamma u).symm

/-- The rational left-quotient map is open. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenMap :
    IsOpenMap V.fullAdelicCliffordSpinCandidateLeftQuotientMap := by
  intro U hU
  rw [isOpen_coinduced,
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_preimage_image U]
  exact isOpen_iUnion fun gamma =>
    isOpenMap_mul_left
      (gamma : V.FullAdelicCliffordSpinCandidateGroup) U hU

/-- The canonical map is an open quotient map. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap V.fullAdelicCliffordSpinCandidateLeftQuotientMap :=
  IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenMap
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap

/-! ## Separation and local compactness -/

/-- Equality in the rational left quotient is detected by the relative
element lying in the rational diagonal subgroup. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_eq_iff
    (x y : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap x =
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap y ↔
      y * x⁻¹ ∈ V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
  change Quot.mk
      (leftCosetSetoid
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup) x =
      Quot.mk
        (leftCosetSetoid
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup) y ↔ _
  rw [leftCoset_mk_eq_iff]
  constructor
  · rintro ⟨gamma, rfl⟩
    convert gamma.property using 1
    simp [mul_assoc]
  · intro h
    refine ⟨⟨y * x⁻¹, h⟩, ?_⟩
    simp [mul_assoc]

/-- The equivalence relation defining the left quotient is closed in the
square of the full-adelic carrier. -/
theorem isClosed_fullAdelicCliffordSpinCandidateLeftQuotientRelation :
    IsClosed
      {p : V.FullAdelicCliffordSpinCandidateGroup ×
          V.FullAdelicCliffordSpinCandidateGroup |
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap p.1 =
          V.fullAdelicCliffordSpinCandidateLeftQuotientMap p.2} := by
  rw [show
      {p : V.FullAdelicCliffordSpinCandidateGroup ×
          V.FullAdelicCliffordSpinCandidateGroup |
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap p.1 =
          V.fullAdelicCliffordSpinCandidateLeftQuotientMap p.2} =
        (fun p : V.FullAdelicCliffordSpinCandidateGroup ×
            V.FullAdelicCliffordSpinCandidateGroup => p.2 * p.1⁻¹) ⁻¹'
          (V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :
            Set V.FullAdelicCliffordSpinCandidateGroup) by
    ext p
    exact V.fullAdelicCliffordSpinCandidateLeftQuotientMap_eq_iff p.1 p.2]
  exact
    V.isClosed_rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup.preimage
      (continuous_snd.mul continuous_fst.inv)

/-- The rational left quotient is Hausdorff. -/
noncomputable instance
    fullAdelicCliffordSpinCandidateLeftQuotientT2Space :
    T2Space V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  (t2Space_iff_of_isOpenQuotientMap
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenQuotientMap).mpr
      V.isClosed_fullAdelicCliffordSpinCandidateLeftQuotientRelation

/-- The rational left quotient is locally compact. -/
noncomputable instance
    fullAdelicCliffordSpinCandidateLeftQuotientLocallyCompactSpace :
    LocallyCompactSpace V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenQuotientMap
    |>.locallyCompactSpace

/-- The rational left quotient is second countable. -/
noncomputable instance
    fullAdelicCliffordSpinCandidateLeftQuotientSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap
    |>.secondCountableTopology
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenMap

/-! ## Comparison with the map-generated measurable structure -/

/-- Every open subset of the topological quotient is measurable for the
existing map-generated measurable structure. -/
noncomputable instance
    fullAdelicCliffordSpinCandidateLeftQuotientOpensMeasurableSpace :
    OpensMeasurableSpace V.FullAdelicCliffordSpinCandidateLeftQuotient where
  borel_le := by
    apply MeasurableSpace.generateFrom_le
    intro U hU
    change MeasurableSet
      (V.fullAdelicCliffordSpinCandidateLeftQuotientMap ⁻¹' U)
    exact
      (hU.preimage
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap_continuous).measurableSet

/-- The Borel measurable space of the quotient topology is contained in the
existing map-generated measurable structure.  The reverse inclusion is not
claimed: the current APIs do not supply the required standard-Borel/Polish
quotient theorem for this full-adelic carrier. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotient_borel_le_mapGenerated :
    borel V.FullAdelicCliffordSpinCandidateLeftQuotient ≤
      (inferInstance :
        MeasurableSpace V.FullAdelicCliffordSpinCandidateLeftQuotient) :=
  OpensMeasurableSpace.borel_le

end RationalQuadraticSpaceMatrix
