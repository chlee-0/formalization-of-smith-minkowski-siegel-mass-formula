import SMSFormula.RationalCliffordSpinCandidateIntegralImageHaarComparison
import SMSFormula.RationalCliffordSpinCandidateRankTwoInvolution

/-!
# The integral two-point kernel of the local Spin map

The nontrivial scalar root `-1` already gives a point of the full p-adic
Clifford--Spin kernel.  This file proves that its Clifford, matrix,
inverse-Clifford, and inverse-matrix coordinates are integral at every
normalized admissible place.  It therefore lies in the good integral local
factor and sharpens the restricted-kernel bound to

    `Nat.card ker = 2`.

The construction is valid at the dyadic place as well: it uses only that
`-1` and the identity coordinates are integral, not that `2` is a unit.
The finite-sheet Haar scalar is treated after this algebraic kernel layer;
kernel cardinality alone is not used as a measure normalization theorem.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000

local instance integralKernelFiniteSheetPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## The scalar `-1` point -/

/-- The full p-adic Clifford--Spin point supplied by the nontrivial scalar
root of unity. -/
def heightOnePadicCliffordSpinCandidateNegOnePoint
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicCliffordSpinCandidateGroup v :=
  (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
    (negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])).1

/-- The scalar `-1` point maps to the identity special-orthogonal matrix. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_mem_ker
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (V.heightOnePadicCliffordSpinCandidateNegOnePoint v) = 1 := by
  exact
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])).2

/-- The scalar `-1` point has order two. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_mul_self
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicCliffordSpinCandidateNegOnePoint v *
        V.heightOnePadicCliffordSpinCandidateNegOnePoint v = 1 := by
  change
    ((V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
      (negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *
      (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
      (negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])).1 = 1
  rw [← map_mul, negOneRootOfUnity_mul_self, map_one]
  rfl

/-- The scalar `-1` point is its own inverse. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_inv
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.heightOnePadicCliffordSpinCandidateNegOnePoint v)⁻¹ =
      V.heightOnePadicCliffordSpinCandidateNegOnePoint v := by
  exact inv_eq_of_mul_eq_one_left
    (V.heightOnePadicCliffordSpinCandidateNegOnePoint_mul_self v)

/-- Point-data form of the scalar `-1` affine coordinate point. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_pointData
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (V.heightOnePadicCliffordSpinCandidateNegOnePoint v) =
      V.cliffordSpinCandidatePointDataOfRootOfUnity
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  exact
    (V.cliffordSpinCandidateCoordinateAlgHomEquivPointData
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).apply_symm_apply _

/-- Every Clifford coordinate of the scalar `-1` point is the negative of
the corresponding identity coordinate. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_cliffordCoordinate
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (s : Finset (Fin n)) :
    V.heightOnePadicCliffordSpinCandidateNegOnePoint v
        (V.cliffordSpinCandidateCliffordCoordinate s) =
      -(1 : V.HeightOnePadicCliffordSpinCandidateGroup v)
        (V.cliffordSpinCandidateCliffordCoordinate s) := by
  rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr,
    ← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr,
    V.heightOnePadicCliffordSpinCandidateNegOnePoint_pointData]
  have hone :
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (1 : V.HeightOnePadicCliffordSpinCandidateGroup v) = 1 :=
    map_one
      (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
  rw [hone, CliffordSpinCandidatePointData.one_clifford]
  change
    (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr (-1) s =
      -((V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr 1 s)
  rw [map_neg]
  rfl

/-- Every matrix coordinate of the scalar `-1` point equals the
corresponding identity coordinate. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_matrixCoordinate
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (i j : Fin n) :
    V.heightOnePadicCliffordSpinCandidateNegOnePoint v
        (V.cliffordSpinCandidateMatrixCoordinate i j) =
      (1 : V.HeightOnePadicCliffordSpinCandidateGroup v)
        (V.cliffordSpinCandidateMatrixCoordinate i j) := by
  have h := congrArg
    (fun M : V.HeightOnePadicSpecialOrthogonalGroup v => M.1.1.1 i j)
    (V.heightOnePadicCliffordSpinCandidateNegOnePoint_mem_ker v)
  change
    (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (V.heightOnePadicCliffordSpinCandidateNegOnePoint v)).1.1.1 i j =
      (1 : V.HeightOnePadicSpecialOrthogonalGroup v).1.1.1 i j at h
  rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix]
    at h
  have hone := congrArg
    (fun M : V.HeightOnePadicSpecialOrthogonalGroup v => M.1.1.1 i j)
    (map_one (V.cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
  change
    (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (1 : V.HeightOnePadicCliffordSpinCandidateGroup v)).1.1.1 i j =
      (1 : V.HeightOnePadicSpecialOrthogonalGroup v).1.1.1 i j at hone
  rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix]
    at hone
  exact h.trans hone.symm

/-! ## Integrality and restricted kernel cardinality -/

/-- All four coordinate families of the scalar `-1` point are integral at
every normalized admissible place. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_isIntegral
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1
      (V.heightOnePadicCliffordSpinCandidateNegOnePoint v.1) := by
  have hone :
      V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1
        (1 : V.HeightOnePadicCliffordSpinCandidateGroup v.1) := by
    exact
      (1 : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
        S v).2 v.2
  unfold HeightOnePadicCliffordSpinCandidateIsIntegral at hone ⊢
  have hcliff : ∀ s,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1).symm
          (V.heightOnePadicCliffordSpinCandidateNegOnePoint v.1
            (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
        v.1.adicCompletionIntegers ℚ := by
    intro s
    rw [V.heightOnePadicCliffordSpinCandidateNegOnePoint_cliffordCoordinate]
    simpa only [map_neg] using
      (v.1.adicCompletionIntegers ℚ).neg_mem _ (hone.1 s)
  have hmatrix : ∀ i j,
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1).symm
          (V.heightOnePadicCliffordSpinCandidateNegOnePoint v.1
            (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
        v.1.adicCompletionIntegers ℚ := by
    intro i j
    rw [V.heightOnePadicCliffordSpinCandidateNegOnePoint_matrixCoordinate]
    exact hone.2.1 i j
  refine ⟨hcliff, hmatrix, ?_, ?_⟩
  · intro s
    rw [V.heightOnePadicCliffordSpinCandidateNegOnePoint_inv]
    exact hcliff s
  · intro i j
    rw [V.heightOnePadicCliffordSpinCandidateNegOnePoint_inv]
    exact hmatrix i j

/-- The scalar `-1` point as a point of the normalized integral local
factor. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v :=
  ⟨V.heightOnePadicCliffordSpinCandidateNegOnePoint v.1,
    fun _ =>
      V.heightOnePadicCliffordSpinCandidateNegOnePoint_isIntegral S v⟩

/-- The integral scalar `-1` point in the restricted point-map kernel. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOneKernelPoint
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).ker :=
  ⟨V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint S v, by
    show V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint
          S v) = 1
    apply Subtype.ext
    simpa only [
      V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_apply]
      using V.heightOnePadicCliffordSpinCandidateNegOnePoint_mem_ker v.1⟩

/-- The scalar `-1` point is nontrivial over every standard p-adic field. -/
theorem heightOnePadicCliffordSpinCandidateNegOnePoint_ne_one
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicCliffordSpinCandidateNegOnePoint v ≠ 1 := by
  intro hk
  let E :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  have hE :
      E (negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
        E 1 := by
    apply Subtype.ext
    simpa [heightOnePadicCliffordSpinCandidateNegOnePoint, E] using hk
  have hz :
      negOneRootOfUnity ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] = 1 :=
    E.injective hE
  have hval := congrArg
    (fun z : rootsOfUnity 2 ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] =>
      ((z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) hz
  norm_num [negOneRootOfUnity] at hval

/-- Every point of the full p-adic point-map kernel is either the identity
or the scalar `-1` point. -/
theorem eq_one_or_heightOnePadicCliffordSpinCandidateNegOnePoint_of_pointMap_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicCliffordSpinCandidateGroup v)
    (hg : V.cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g = 1) :
    g = 1 ∨ g = V.heightOnePadicCliffordSpinCandidateNegOnePoint v := by
  let E :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  let x :
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).ker := ⟨g, hg⟩
  let z : rootsOfUnity 2 ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    E.symm x
  have hzpow :
      (((z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) ^ 2 = 1 := by
    exact congrArg Units.val z.property
  rcases sq_eq_one_iff.mp hzpow with hz | hz
  · left
    have hz' : z = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact hz
    have hx : x = 1 := by
      calc
        x = E z := (E.apply_symm_apply x).symm
        _ = E 1 := congrArg E hz'
        _ = 1 := map_one E
    exact congrArg (fun y :
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).ker => y.1) hx
  · right
    have hz' :
        z = negOneRootOfUnity
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] := by
      apply Subtype.ext
      apply Units.ext
      simpa [negOneRootOfUnity] using hz
    have hx :
        x = E (negOneRootOfUnity
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
      calc
        x = E z := (E.apply_symm_apply x).symm
        _ = E (negOneRootOfUnity
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := congrArg E hz'
    exact congrArg (fun y :
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).ker => y.1) hx

/-- The integral scalar `-1` kernel point is distinct from the identity. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOneKernelPoint_ne_one
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOneKernelPoint
        S v ≠ 1 := by
  intro h
  apply V.heightOnePadicCliffordSpinCandidateNegOnePoint_ne_one v.1
  have hval := congrArg
    (fun x :
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).ker =>
      (x.1.1 : V.HeightOnePadicCliffordSpinCandidateGroup v.1)) h
  change V.heightOnePadicCliffordSpinCandidateNegOnePoint v.1 = 1 at hval
  exact hval

/-- The restricted integral point-map kernel has exactly the two scalar
points `1` and `-1`. -/
theorem heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree_eq_two
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree S v = 2 := by
  have hpos :=
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree_pos S v
  have hle :=
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree_le_two
      S v
  have hne :
      V.heightOnePadicCliffordSpinCandidateIntegralPointMapKernelDegree
        S v ≠ 1 := by
    intro hcard
    have hsub : Subsingleton
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).ker :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    exact
      V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOneKernelPoint_ne_one
        S v (Subsingleton.elim _ _)
  omega

end RationalQuadraticSpaceMatrix
