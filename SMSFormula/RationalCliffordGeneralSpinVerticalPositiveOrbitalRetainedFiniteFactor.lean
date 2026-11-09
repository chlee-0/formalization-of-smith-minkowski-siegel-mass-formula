import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteLocal

/-!
# Finite Spin conditions at the retained GSpin origin

Local evaluation of the intrinsic finite-adelic Spin embedding commutes with
the existing height-one evaluation maps.  Using that compatibility, the
finite Spin-orbit preimage of the retained horizontal identity carrier is
identified exactly with two conditions defined earlier: right translation
into the p-adic Spin identity source at every retained exceptional place,
and Spin integrality at every remaining place.

The retained exceptional set is also shown to be normalized for the
admissible Spin block.  Thus the measure restriction can use the block
homeomorphism and the cofinal restriction theorem directly; no
representative, chart, or scale is added here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance retainedFiniteFactorPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedFiniteFactorDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

@[simp] theorem
    finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (y : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y) =
      V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v y) := by
  exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality RationalFiniteAdele
    (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v) y

theorem cliffordSpinCandidate_finiteOrbitOrigin_mem_identityCarrier_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (y : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y *
        V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S s g ∈
          V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S ↔
      (∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v ∈
          (V.padicCliffordSpinCandidateIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).source) ∧
      (∀ v : V.CliffordGeneralSpinHorizontalIntegralPlace S,
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1
          (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)) := by
  let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  constructor
  · rintro ⟨w, hw, hwEq⟩
    refine ⟨?_, ?_⟩
    · intro v
      have hcomponent := congrArg
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1) hwEq
      have hlocal :
          V.cliffordSpinCandidateToCliffordGeneralSpinHom
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
              (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v) =
            w.1 v := by
        simpa [cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
          V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
          v.2] using hcomponent.symm
      have hwlocal : w.1 v ∈
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).source := hw.1 v (Set.mem_univ v)
      rw [← hlocal] at hwlocal
      exact Set.ext_iff.mp
        (V.preimage_cliffordSpinCandidateToCliffordGeneralSpinHom_padicCentralFiberIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1)
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v) |>.mp hwlocal
    · intro v
      have hcomponent := congrArg
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1) hwEq
      have hlocal :
          V.cliffordSpinCandidateToCliffordGeneralSpinHom
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
              (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y) *
            (g v).1 = (w.2 v).1 := by
        simpa [cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
          V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
          v.2] using hcomponent.symm
      have hprod : V.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
              (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y) *
            (g v).1) := by
        rw [hlocal]
        exact (w.2 v).2
      have hembed : V.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
            (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)) := by
        let H := V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v
        exact (H.mul_mem_cancel_right (g v).2).mp hprod
      exact
        (V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
          v.1 (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)).mp hembed
  · rintro ⟨hExceptional, hTail⟩
    let wExceptional : V.CliffordGeneralSpinHorizontalExceptionalProduct S :=
      fun v => V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v)
    let wTail : V.CliffordGeneralSpinHorizontalIntegralTail S := fun v =>
      ⟨V.cliffordSpinCandidateToCliffordGeneralSpinHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
          (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y) * (g v).1,
        (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).mul_mem
          ((V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
            v.1 (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)).mpr
              (hTail v)) (g v).2⟩
    refine ⟨(wExceptional, wTail), ?_, ?_⟩
    · exact ⟨fun v _ => Set.ext_iff.mp
          (V.preimage_cliffordSpinCandidateToCliffordGeneralSpinHom_padicCentralFiberIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v.1).1)
          (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v) |>.mpr
            (hExceptional v), Set.mem_univ wTail⟩
    · apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
      funext v
      change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
            (wExceptional, wTail)) =
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y *
            V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S s g)
      by_cases hv : v ∈ B
      · simp [wExceptional,
          V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
          cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin, B, hv]
      · simp [wTail,
          V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
          cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin, B, hv]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance retainedFiniteFactorIntegralDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedFiniteFactorIntegralPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) =
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
  ext v
  simp [RationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces,
    RationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleBadPlaces,
    cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces,
    cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces]
  aesop

/-- The finite factor occurring in the retained orbital kernel is exactly
the translated exceptional Spin identity source together with the unchanged
integral Spin tail. -/
theorem mem_cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_iff
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (y : L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    y ∈ L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x ↔
      (∀ v : {v // v ∈ B},
        V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * x.2.1 v ∈
          (V.padicCliffordSpinCandidateIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).source) ∧
      (∀ v : V.CliffordGeneralSpinHorizontalIntegralPlace E,
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1
          (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  unfold cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage
  dsimp only
  exact V.cliffordSpinCandidate_finiteOrbitOrigin_mem_identityCarrier_iff E x.2.1 g y

end PositiveDefiniteIntegralLattice

end
