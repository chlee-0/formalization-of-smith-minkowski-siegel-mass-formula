import SMSFormula.RationalCliffordSpinCandidateIntegralLocalFactorNormalization
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization
import SMSFormula.RationalCliffordSpinCandidateSpinorNormKernel

/-!
# Integral Spin images and their local Haar comparison

At a normalized admissible place, the literal integral Clifford--Spin
subgroup maps into the integral special-orthogonal subgroup. The image is
compact-open and therefore has a finite, positive index in the compact
integral SO group. It also lies in the kernel of the restricted spinor norm.

This file keeps the two remaining normalization quantities explicit: the
finite index of the actual integral Spin image in integral SO and the
positive Haar scalar comparing the pushed-forward integral Spin measure with
the differential measure comapped to that image. Haar uniqueness proves the
division-free identity

    imageIndex * SpinIntegralVolume =
      pointMapHaarScalar * SOIntegralVolume.

The full p-adic point-map kernel has cardinality two, while the restricted
integral kernel has positive cardinality at most two. Neither this kernel
bound nor local homeomorphism alone evaluates the Haar scalar. Equality of
the integral image with the integral spinor kernel, the value of its index,
and the finite-sheet evaluation of the Haar scalar remain separate inputs.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance integralImageHaarComparisonPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance integralImageHaarComparisonSpecialOrthogonalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance integralImageHaarComparisonSpecialOrthogonalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance integralImageHaarComparisonSpinMeasurableMul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableMul (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ContinuousMul.measurableMul

local instance integralImageHaarComparisonSpecialOrthogonalMeasurableMul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableMul (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ContinuousMul.measurableMul

/-! ## The integral point map -/

/-- Literal Clifford--Spin integrality implies integrality of the matrix and
inverse-matrix coordinates of its special-orthogonal image. -/
theorem heightOnePadicCliffordSpinCandidateIsIntegral_pointMap
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicCliffordSpinCandidateGroup v)
    (hg : V.HeightOnePadicCliffordSpinCandidateIsIntegral v g) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g) := by
  unfold HeightOnePadicSpecialOrthogonalIsIntegral
  constructor
  · intro i j
    simpa [cliffordSpinCandidateGroupToSpecialOrthogonal,
      cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
      cliffordSpinCandidateMatrixOfCoordinateAlgHom,
      CliffordSpinCandidatePointData.matrixGroup_coe] using hg.2.1 i j
  · intro i j
    have h := hg.2.2.2 i j
    have hint :
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((V.cliffordSpinCandidateGroupToSpecialOrthogonal
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (g⁻¹)).1.1.1 i j) ∈
          v.adicCompletionIntegers ℚ := by
      simpa [cliffordSpinCandidateGroupToSpecialOrthogonal,
        cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
        cliffordSpinCandidateMatrixOfCoordinateAlgHom,
        CliffordSpinCandidatePointData.matrixGroup_coe] using h
    rw [map_inv] at hint
    exact hint

/-- The point map restricted from a good integral Clifford--Spin local factor
to the carrier-independent integral special-orthogonal group. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v →*
      V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 :=
  ((V.cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
      S v)).codRestrict
    (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v.1)
    (fun g =>
      V.heightOnePadicCliffordSpinCandidateIsIntegral_pointMap
        v.1 g.1 (g.2 v.2))

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v g :
      V.HeightOnePadicSpecialOrthogonalGroup v.1) =
      V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] g.1 :=
  rfl

/-- The restricted integral point map is continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v) := by
  exact continuous_induced_rng.mpr
    ((V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp
      (V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
        S v))

/-! ## Integral image and restricted spinor norm -/

/-- The p-adic spinor norm restricted to the integral special-orthogonal
subgroup. -/
def heightOnePadicSpecialOrthogonalIntegralSpinorNormHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicSpecialOrthogonalIntegralGroup v →*
      Rat.SquareClass ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
  (V.padicSpecialOrthogonalSpinorNormHom
      (Rat.HeightOneSpectrum.primesEquiv v).1).comp
    (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v).subtype

@[simp]
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormHom_apply
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v g =
      V.padicSpecialOrthogonalSpinorNormHom
        (Rat.HeightOneSpectrum.primesEquiv v).1 g.1 :=
  rfl

/-- The integral Clifford--Spin image lies in the restricted spinor-norm
kernel. The reverse inclusion is the missing integral lifting theorem. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range_le_spinorNorm_ker
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range ≤
      (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).ker := by
  rintro g ⟨x, rfl⟩
  change V.padicSpecialOrthogonalSpinorNormHom
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x.1) = 1
  exact V.specialOrthogonalSpinorNorm_candidateToSpecialOrthogonal_eq_one
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x.1

/-- The actual integral Clifford--Spin image is open inside integral SO. -/
theorem
    isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    IsOpen
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range :
        Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let K :=
    V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
      S v.1
  have himage : IsOpen
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] ''
        (K : Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1))) :=
    (V.padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap p)
      (K : Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1))
      (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v.1 v.2)
  have hpre := himage.preimage
    (continuous_subtype_val : Continuous
      (fun g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 ↦
        (g : V.HeightOnePadicSpecialOrthogonalGroup v.1)))
  convert hpre using 1
  ext g
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  · rintro ⟨x, hxK, hx⟩
    refine ⟨⟨x, hxK⟩, ?_⟩
    exact Subtype.ext hx

/-- The actual integral Clifford--Spin image is compact inside integral
SO. -/
theorem
    isCompact_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    IsCompact
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range :
        Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)) := by
  letI : CompactSpace
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    isCompact_iff_compactSpace.mp
      (V.isCompact_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1)
  exact
    ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range
      |>.isClosed_of_isOpen
        (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
          S v)).isCompact

/-- The exact missing integral lifting statement at an admissible place. It
asserts that a target-integral point of trivial spinor norm admits an integral
lift, including all Clifford and inverse-Clifford coordinates rather than only
its matrix coordinates. -/
def CliffordSpinCandidateIntegralLiftingAt
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) : Prop :=
  (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range =
    (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).ker

/-- Elementwise form of the integral lifting condition. -/
theorem cliffordSpinCandidateIntegralLiftingAt_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.CliffordSpinCandidateIntegralLiftingAt S v ↔
      ∀ g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1,
        V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1 g = 1 →
          ∃ x :
              V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
                S v,
            V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
              S v x = g := by
  constructor
  · intro h g hg
    have hgker :
        g ∈ (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).ker :=
      hg
    rw [← h] at hgker
    exact hgker
  · intro h
    apply le_antisymm
    · exact
        V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range_le_spinorNorm_ker
          S v
    · intro g hg
      exact h g hg

/-! ## The finite integral-image index -/

noncomputable instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapRangeQuotientFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Finite
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 ⧸
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).range) := by
  letI : CompactSpace
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    isCompact_iff_compactSpace.mp
      (V.isCompact_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1)
  exact Subgroup.quotient_finite_of_isOpen _
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
      S v)

/-- The index of the actual integral Clifford--Spin image in the full
integral special-orthogonal group. -/
def heightOnePadicCliffordSpinCandidateIntegralImageIndex
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) : ℕ :=
  (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range.index

/-- The integral-image index is positive. -/
theorem heightOnePadicCliffordSpinCandidateIntegralImageIndex_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    0 < V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v := by
  rw [heightOnePadicCliffordSpinCandidateIntegralImageIndex,
    Subgroup.index_eq_card]
  exact Nat.card_pos

/-! ## Full and restricted kernel cardinalities -/

/-- The full p-adic Clifford--Spin point-map kernel has cardinality two. -/
theorem natCard_padicCliffordSpinCandidatePointMap_ker_eq_two
    (p : ℕ) [Fact p.Prime] :
    Nat.card
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker = 2 := by
  calc
    Nat.card
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker =
        Nat.card (rootsOfUnity 2 ℚ_[p]) :=
      Nat.card_congr
        (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
          ℚ_[p]).symm.toEquiv
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact
        (IsPrimitiveRoot.neg_one 0 (R := ℚ_[p]) (by norm_num)).card_rootsOfUnity

/-- Forgetting integrality embeds the restricted point-map kernel into the
full p-adic kernel. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).ker →*
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).ker where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The kernel-forgetting homomorphism is injective. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel_injective
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Function.Injective
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel
        S v) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z :
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).ker =>
      (z : V.HeightOnePadicCliffordSpinCandidateGroup v.1))
    hxy

noncomputable instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapKerFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Finite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).ker :=
  Finite.of_injective
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel
      S v)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel_injective
      S v)

/-- The number of kernel points which remain in the chosen integral
coordinate subgroup. -/
def heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) : ℕ :=
  Nat.card
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).ker

theorem heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    0 <
      V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree S v :=
  Nat.card_pos

/-- The integral point-map kernel has at most the two points of the full
p-adic kernel. Equality still requires proving that the nontrivial scalar
kernel point is integral in the chosen coordinate model. -/
theorem heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree_le_two
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree S v ≤ 2 := by
  calc
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree S v ≤
        Nat.card
          (V.cliffordSpinCandidateGroupToSpecialOrthogonal
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).ker :=
      Nat.card_le_card_of_injective
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel
          S v)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralKernelToPadicKernel_injective
          S v)
    _ = 2 := V.natCard_padicCliffordSpinCandidatePointMap_ker_eq_two
      (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-! ## Haar measures on the source and its actual image -/

/-- The unnormalized integral Clifford--Spin local-factor measure is Haar on
the compact-open subgroup. -/
noncomputable instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_isHaar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI : MeasurableMul
      (V.HeightOnePadicCliffordSpinCandidateGroup v.1) :=
    ContinuousMul.measurableMul
  unfold finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.padicCliffordSpinCandidateChartGluedMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1)
    (f :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
        S v)
    (mH := ContinuousMul.measurableMul)
      (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v.1 v.2).isOpenEmbedding_subtypeVal

/-- The unnormalized integral special-orthogonal differential measure is
Haar on its compact-open subgroup. -/
noncomputable instance heightOnePadicSpecialOrthogonalIntegralMeasure_isHaar
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure
      (V.heightOnePadicSpecialOrthogonalIntegralMeasure v) := by
  letI : Measure.IsHaarMeasure
      (V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : MeasurableMul (V.HeightOnePadicSpecialOrthogonalGroup v) :=
    ContinuousMul.measurableMul
  unfold heightOnePadicSpecialOrthogonalIntegralMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.padicInvariantDifferentialGroupMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1)
    (f := (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v).subtype)
    (mH := ContinuousMul.measurableMul)
      (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v
        ).isOpenEmbedding_subtypeVal

/-- The integral SO differential measure comapped to the actual integral
Clifford--Spin image. -/
def heightOnePadicCliffordSpinCandidateIntegralImageMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).range :=
  Measure.comap
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
      S v).range.subtype
    (V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1)

noncomputable instance
    heightOnePadicCliffordSpinCandidateIntegralImageMeasure_isHaar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsHaarMeasure
      (V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v) := by
  unfold heightOnePadicCliffordSpinCandidateIntegralImageMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1)
    (f :=
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).range.subtype)
    (mH := ContinuousMul.measurableMul)
      (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
        S v).isOpenEmbedding_subtypeVal

/-- Pushing the source Haar measure through the surjection onto its actual
image again gives Haar measure. -/
noncomputable instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToImageMeasure_isHaar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsHaarMeasure
      (Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).rangeRestrict
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S v)) := by
  apply Measure.isHaarMeasure_map_of_isFiniteMeasure
  · exact continuous_induced_rng.mpr
      (V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v)
  · exact
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).rangeRestrict_surjective

/-- The positive finite Haar scalar comparing the point-map pushforward with
the differential measure on the actual integral image. This scalar is not
evaluated from the kernel cardinality. -/
noncomputable def
    heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) : NNReal :=
  Measure.haarScalarFactor
    (Measure.map
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).rangeRestrict
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v))
    (V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v)

theorem heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    0 <
      V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v := by
  unfold heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Haar uniqueness gives the exact measure comparison on the actual
integral image. -/
theorem
    map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_haarScalar_smul_imageMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).rangeRestrict
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S v) =
      V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v •
        V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v := by
  letI : CompactSpace
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    isCompact_iff_compactSpace.mp
      (V.isCompact_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1)
  letI : CompactSpace
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).range :=
    isCompact_iff_compactSpace.mp
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range
        |>.isClosed_of_isOpen
          (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
            S v)).isCompact
  exact Measure.isMulInvariant_eq_smul_of_compactSpace _ _

@[simp]
theorem heightOnePadicCliffordSpinCandidateIntegralImageMeasure_univ
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v Set.univ =
      V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).range :
            Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)) := by
  unfold heightOnePadicCliffordSpinCandidateIntegralImageMeasure
  exact subgroup_comap_measure_univ_eq_of_subtype_mspace
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
      S v).range
    rfl
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
      S v).measurableSet

/-! ## Division-free volume comparison -/

/-- Taking total masses in a measure comparison by a finite NNReal scalar. -/
theorem measure_univ_eq_nnreal_mul_of_map_eq_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) (ν : Measure β) (c : NNReal)
    (hf : AEMeasurable f μ) (h : Measure.map f μ = c • ν) :
    μ Set.univ = (c : ℝ≥0∞) * ν Set.univ := by
  have huniv := congrArg (fun m : Measure β => m Set.univ) h
  change (Measure.map f μ) Set.univ = (c • ν) Set.univ at huniv
  rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply] at huniv
  exact huniv

/-- The Spin integral volume is the point-map Haar scalar times the
differential mass of the actual integral image. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_eq_haarScalar_mul_imageVolume
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
      (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
        S v : ℝ≥0∞) *
        V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
            S v).range :
              Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)) := by
  have hmap : Measurable
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).rangeRestrict :=
    Measurable.subtype_mk
      (V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).measurable
  have hvolume := measure_univ_eq_nnreal_mul_of_map_eq_smul
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
      S v).rangeRestrict
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
      S v)
    (V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v)
    (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v)
    hmap.aemeasurable
    (V.map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_haarScalar_smul_imageMeasure
      S v)
  rw [
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_univ
      S v,
    V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure_univ S v]
    at hvolume
  exact hvolume

/-- Finite-index Haar algebra compares the actual image mass with the full
integral special-orthogonal volume. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralImageIndex_mul_imageVolume_eq_soIntegralVolume
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v : ℝ≥0∞) *
        V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
            S v).range :
              Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)) =
      V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  letI :
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).range.FiniteIndex := ⟨by
      exact Nat.ne_of_gt
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_pos S v)⟩
  have h := Subgroup.index_mul_measure
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
      S v).measurableSet
    (V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1)
  rw [V.heightOnePadicSpecialOrthogonalIntegralMeasure_univ v.1] at h
  exact h

/-- Local volume comparison supplied by the coordinate model. The image
index and the point-map Haar scalar are kept separate. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_index_mul_eq_haarScalar_mul_soIntegralVolume
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v : ℝ≥0∞) *
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
      (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
        S v : ℝ≥0∞) *
        V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  rw [
    V.heightOnePadicCliffordSpinCandidateIntegralVolume_eq_haarScalar_mul_imageVolume
      S v]
  calc
    (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v : ℝ≥0∞) *
          ((V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
              S v : ℝ≥0∞) *
            V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1
              ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
                S v).range :
                  Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1))) =
        (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
            S v : ℝ≥0∞) *
          ((V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v :
              ℝ≥0∞) *
            V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1
              ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
                S v).range :
                  Set (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1))) := by
      ac_rfl
    _ = (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar
            S v : ℝ≥0∞) *
          V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
      rw [
        V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_mul_imageVolume_eq_soIntegralVolume
          S v]

/-- If the finite image index equals the point-map Haar scalar, the two
literal integral volumes agree. Establishing this scalar equality is exactly
the remaining finite-sheet plus arithmetic-index input. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_index_eq_haarScalar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hscale :
      (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v : NNReal) =
        V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
      V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  let c : ℝ≥0∞ :=
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast
      (ne_of_gt
        (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar_pos
          S v))
  have hctop : c ≠ ⊤ := by simp [c]
  have hcomparison :=
    V.heightOnePadicCliffordSpinCandidateIntegralVolume_index_mul_eq_haarScalar_mul_soIntegralVolume
      S v
  have hscale' :
      (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v : ℝ≥0∞) =
        c := by
    dsimp [c]
    exact_mod_cast hscale
  rw [hscale'] at hcomparison
  calc
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
        1 *
          V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 :=
      (one_mul _).symm
    _ = (c⁻¹ * c) *
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 := by
      rw [ENNReal.inv_mul_cancel hc0 hctop]
    _ = c⁻¹ *
        (c *
          V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
            v.1) := by
      rw [mul_assoc]
    _ = c⁻¹ *
        (c * V.heightOnePadicSpecialOrthogonalIntegralVolume v.1) := by
      rw [hcomparison]
    _ = (c⁻¹ * c) *
        V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
      rw [mul_assoc]
    _ = V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
      rw [ENNReal.inv_mul_cancel hc0 hctop, one_mul]

end RationalQuadraticSpaceMatrix
