import SMSFormula.RationalCliffordGeneralSpinAdelicTopology
import SMSFormula.RationalCliffordSpinCandidatePlacewiseImageOpennessPrecursor

/-!
# Local compactness of intrinsic general-Spin points

The intrinsic `GSpin` carrier is embedded into the finite coordinates of its
Clifford unit, inverse Clifford unit, similitude, and special-orthogonal
action.  Its image is the common zero locus of the literal intrinsic point
equations.  This gives a closed embedding over every Hausdorff topological
rational ring and hence local compactness over the real and p-adic fields.
-/

noncomputable section

open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

abbrev CliffordGeneralSpinClosedCoordinateSpace
    (A : Type*) [CommRing A] [Algebra ℚ A] :=
  (((Finset (Fin n) → A) × (Finset (Fin n) → A)) × Aˣ) ×
    V.specialOrthogonalMatrixGroup A

/-- The finite closed-realization coordinates: a Clifford unit and its
inverse, the similitude, and the existing special-orthogonal group point. -/
def cliffordGeneralSpinClosedCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    V.CliffordGeneralSpinIntrinsicPoint A →
      V.CliffordGeneralSpinClosedCoordinateSpace A :=
  fun x =>
    (((
      (fun u => (V.cliffordCoordinateBaseChangeBasis A).repr
        (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) u),
      fun u => (V.cliffordCoordinateBaseChangeBasis A).repr
        ((x.cliffordUnit⁻¹ :
          (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          V.cliffordCoordinateBaseChangeAlgebra A) u),
      x.similitude),
    x.matrixGroup)

/-- Reconstruct a Clifford element from its complete finite coefficient
family. -/
def cliffordGeneralSpinCliffordOfCoordinates
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (c : Finset (Fin n) → A) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  (V.cliffordCoordinateBaseChangeBasis A).equivFun.symm c

@[simp]
theorem cliffordGeneralSpinCliffordOfCoordinates_repr
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (c : Finset (Fin n) → A) (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (V.cliffordGeneralSpinCliffordOfCoordinates A c) u = c u := by
  exact congrFun
    ((V.cliffordCoordinateBaseChangeBasis A).equivFun.apply_symm_apply c) u

theorem cliffordGeneralSpinCliffordOfCoordinates_repr_self
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordGeneralSpinCliffordOfCoordinates A
        (fun u => (V.cliffordCoordinateBaseChangeBasis A).repr x u) = x := by
  apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
  ext u
  simp

def cliffordGeneralSpinClosedCoordinateClifford
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : V.CliffordGeneralSpinClosedCoordinateSpace A) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  V.cliffordGeneralSpinCliffordOfCoordinates A z.1.1.1

def cliffordGeneralSpinClosedCoordinateCliffordInv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : V.CliffordGeneralSpinClosedCoordinateSpace A) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  V.cliffordGeneralSpinCliffordOfCoordinates A z.1.1.2

/-- The exact intrinsic equations cutting out general Spin inside the finite
closed-coordinate space. -/
def IsCliffordGeneralSpinClosedCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : V.CliffordGeneralSpinClosedCoordinateSpace A) : Prop :=
  let x := V.cliffordGeneralSpinClosedCoordinateClifford A z
  let y := V.cliffordGeneralSpinClosedCoordinateCliffordInv A z
  x * y = 1 ∧ y * x = 1 ∧
  V.cliffordCoordinateBaseChangeInvolute A x = x ∧
  x * V.cliffordCoordinateBaseChangeReverse A x =
    algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) z.1.2 ∧
  ∀ i, x * V.cliffordCoordinateBaseChangeVector A i * y =
    ∑ j, z.2.1.1.1 j i • V.cliffordCoordinateBaseChangeVector A j

theorem range_cliffordGeneralSpinClosedCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Set.range (V.cliffordGeneralSpinClosedCoordinateMap A) =
      {z | V.IsCliffordGeneralSpinClosedCoordinate A z} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change V.IsCliffordGeneralSpinClosedCoordinate A
      (V.cliffordGeneralSpinClosedCoordinateMap A x)
    simp only [IsCliffordGeneralSpinClosedCoordinate,
      cliffordGeneralSpinClosedCoordinateClifford,
      cliffordGeneralSpinClosedCoordinateCliffordInv,
      cliffordGeneralSpinClosedCoordinateMap]
    rw [V.cliffordGeneralSpinCliffordOfCoordinates_repr_self,
      V.cliffordGeneralSpinCliffordOfCoordinates_repr_self]
    refine ⟨congrArg Units.val (mul_inv_cancel x.cliffordUnit),
      congrArg Units.val (inv_mul_cancel x.cliffordUnit), x.involute_eq,
      x.mul_reverse_eq, ?_⟩
    intro i
    simpa only [CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe] using
      x.vectorGraph i
  · intro hz
    let x := V.cliffordGeneralSpinClosedCoordinateClifford A z
    let y := V.cliffordGeneralSpinClosedCoordinateCliffordInv A z
    let u : (V.cliffordCoordinateBaseChangeAlgebra A)ˣ :=
      ⟨x, y, hz.1, hz.2.1⟩
    let g : V.CliffordGeneralSpinIntrinsicPoint A :=
      { cliffordUnit := u
        similitude := z.1.2
        matrixPoint := V.specialOrthogonalMatrixPointOfGroup A z.2
        involute_eq := hz.2.2.1
        mul_reverse_eq := hz.2.2.2.1
        vectorGraph := by
          intro i
          simpa [u, x, y] using hz.2.2.2.2 i }
    refine ⟨g, ?_⟩
    change V.cliffordGeneralSpinClosedCoordinateMap A g = z
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · funext s
          change (V.cliffordCoordinateBaseChangeBasis A).repr x s = _
          exact V.cliffordGeneralSpinCliffordOfCoordinates_repr A z.1.1.1 s
        · funext s
          change (V.cliffordCoordinateBaseChangeBasis A).repr y s = _
          exact V.cliffordGeneralSpinCliffordOfCoordinates_repr A z.1.1.2 s
      · change z.1.2 = z.1.2
        rfl
    · change (V.specialOrthogonalMatrixPointEquivGroup A)
        ((V.specialOrthogonalMatrixPointEquivGroup A).symm z.2) = z.2
      exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply z.2

/-! ## Coordinatewise continuity of Clifford expressions -/

def CliffordCoordinatewiseContinuous
    {X : Type*} [TopologicalSpace X]
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (f : X → V.cliffordCoordinateBaseChangeAlgebra A) : Prop :=
  ∀ u, Continuous (fun x =>
    (V.cliffordCoordinateBaseChangeBasis A).repr (f x) u)

theorem cliffordCoordinatewiseContinuous_const
    {X : Type*} [TopologicalSpace X]
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (c : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.CliffordCoordinatewiseContinuous A (fun _ : X => c) :=
  fun _ => continuous_const

theorem CliffordCoordinatewiseContinuous.mul
    {X : Type*} [TopologicalSpace X]
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {f g : X → V.cliffordCoordinateBaseChangeAlgebra A}
    (hf : V.CliffordCoordinatewiseContinuous A f)
    (hg : V.CliffordCoordinatewiseContinuous A g) :
    V.CliffordCoordinatewiseContinuous A (fun x => f x * g x) := by
  intro u
  simp_rw [V.cliffordCoordinateBaseChangeBasis_repr_mul]
  apply continuous_finset_sum
  intro s _
  apply continuous_finset_sum
  intro t _
  exact ((hf s).mul (hg t)).mul continuous_const

theorem CliffordCoordinatewiseContinuous.involute
    {X : Type*} [TopologicalSpace X]
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {f : X → V.cliffordCoordinateBaseChangeAlgebra A}
    (hf : V.CliffordCoordinatewiseContinuous A f) :
    V.CliffordCoordinatewiseContinuous A
      (fun x => V.cliffordCoordinateBaseChangeInvolute A (f x)) := by
  intro u
  simp_rw [V.cliffordCoordinateBaseChangeBasis_repr_involute]
  apply continuous_finset_sum
  intro s _
  exact (hf s).mul continuous_const

theorem CliffordCoordinatewiseContinuous.reverse
    {X : Type*} [TopologicalSpace X]
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {f : X → V.cliffordCoordinateBaseChangeAlgebra A}
    (hf : V.CliffordCoordinatewiseContinuous A f) :
    V.CliffordCoordinatewiseContinuous A
      (fun x => V.cliffordCoordinateBaseChangeReverse A (f x)) := by
  intro u
  simp_rw [V.cliffordCoordinateBaseChangeBasis_repr_reverse]
  apply continuous_finset_sum
  intro s _
  exact (hf s).mul continuous_const

theorem isClosed_eq_of_cliffordCoordinatewiseContinuous
    {X : Type*} [TopologicalSpace X]
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [T2Space A]
    {f g : X → V.cliffordCoordinateBaseChangeAlgebra A}
    (hf : V.CliffordCoordinatewiseContinuous A f)
    (hg : V.CliffordCoordinatewiseContinuous A g) :
    IsClosed {x | f x = g x} := by
  rw [show {x | f x = g x} =
      ⋂ u, {x | (V.cliffordCoordinateBaseChangeBasis A).repr (f x) u =
        (V.cliffordCoordinateBaseChangeBasis A).repr (g x) u} by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h u
      rw [h]
    · intro h
      apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
      ext u
      exact h u]
  apply isClosed_iInter
  intro u
  exact isClosed_eq (hf u) (hg u)

theorem cliffordCoordinatewiseContinuous_closedCoordinateClifford
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] :
    V.CliffordCoordinatewiseContinuous A
      (V.cliffordGeneralSpinClosedCoordinateClifford A) := by
  intro u
  simp only [cliffordGeneralSpinClosedCoordinateClifford,
    V.cliffordGeneralSpinCliffordOfCoordinates_repr]
  exact (continuous_apply u).comp
    (continuous_fst.comp (continuous_fst.comp continuous_fst))

theorem cliffordCoordinatewiseContinuous_closedCoordinateCliffordInv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] :
    V.CliffordCoordinatewiseContinuous A
      (V.cliffordGeneralSpinClosedCoordinateCliffordInv A) := by
  intro u
  simp only [cliffordGeneralSpinClosedCoordinateCliffordInv,
    V.cliffordGeneralSpinCliffordOfCoordinates_repr]
  exact (continuous_apply u).comp
    (continuous_snd.comp (continuous_fst.comp continuous_fst))

theorem cliffordCoordinatewiseContinuous_closedCoordinateAlgebraMapSimilitude
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    V.CliffordCoordinatewiseContinuous A
      (fun z : V.CliffordGeneralSpinClosedCoordinateSpace A =>
        algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) z.1.2) := by
  intro u
  simp_rw [V.cliffordCoordinateBaseChangeBasis_repr_algebraMap A]
  exact (Units.continuous_val.comp
    (continuous_snd.comp continuous_fst)).mul continuous_const

theorem cliffordCoordinatewiseContinuous_closedCoordinateVectorGraph
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (i : Fin n) :
    V.CliffordCoordinatewiseContinuous A
      (fun z : V.CliffordGeneralSpinClosedCoordinateSpace A =>
        ∑ j, z.2.1.1.1 j i • V.cliffordCoordinateBaseChangeVector A j) := by
  intro u
  simp_rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply continuous_finset_sum
  intro j _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hm : Continuous (fun z : V.CliffordGeneralSpinClosedCoordinateSpace A =>
      z.2.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))
  exact (((continuous_apply i).comp ((continuous_apply j).comp hm)).mul
    continuous_const)

theorem isClosed_isCliffordGeneralSpinClosedCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed {z | V.IsCliffordGeneralSpinClosedCoordinate A z} := by
  let hx := V.cliffordCoordinatewiseContinuous_closedCoordinateClifford A
  let hy := V.cliffordCoordinatewiseContinuous_closedCoordinateCliffordInv A
  let hone : V.CliffordCoordinatewiseContinuous A
      (fun _ : V.CliffordGeneralSpinClosedCoordinateSpace A => 1) :=
    V.cliffordCoordinatewiseContinuous_const A 1
  let hvector (i : Fin n) : V.CliffordCoordinatewiseContinuous A
      (fun _ : V.CliffordGeneralSpinClosedCoordinateSpace A =>
        V.cliffordCoordinateBaseChangeVector A i) :=
    V.cliffordCoordinatewiseContinuous_const A _
  rw [show {z | V.IsCliffordGeneralSpinClosedCoordinate A z} =
      {z | V.cliffordGeneralSpinClosedCoordinateClifford A z *
          V.cliffordGeneralSpinClosedCoordinateCliffordInv A z = 1} ∩
      {z | V.cliffordGeneralSpinClosedCoordinateCliffordInv A z *
          V.cliffordGeneralSpinClosedCoordinateClifford A z = 1} ∩
      {z | V.cliffordCoordinateBaseChangeInvolute A
          (V.cliffordGeneralSpinClosedCoordinateClifford A z) =
        V.cliffordGeneralSpinClosedCoordinateClifford A z} ∩
      {z | V.cliffordGeneralSpinClosedCoordinateClifford A z *
          V.cliffordCoordinateBaseChangeReverse A
            (V.cliffordGeneralSpinClosedCoordinateClifford A z) =
        algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) z.1.2} ∩
      ⋂ i, {z | V.cliffordGeneralSpinClosedCoordinateClifford A z *
          V.cliffordCoordinateBaseChangeVector A i *
            V.cliffordGeneralSpinClosedCoordinateCliffordInv A z =
        ∑ j, z.2.1.1.1 j i • V.cliffordCoordinateBaseChangeVector A j} by
    ext z
    simp [IsCliffordGeneralSpinClosedCoordinate, and_assoc]]
  repeat' apply IsClosed.inter
  · exact V.isClosed_eq_of_cliffordCoordinatewiseContinuous A
      (CliffordCoordinatewiseContinuous.mul V A hx hy) hone
  · exact V.isClosed_eq_of_cliffordCoordinatewiseContinuous A
      (CliffordCoordinatewiseContinuous.mul V A hy hx) hone
  · exact V.isClosed_eq_of_cliffordCoordinatewiseContinuous A
      (CliffordCoordinatewiseContinuous.involute V A hx) hx
  · exact V.isClosed_eq_of_cliffordCoordinatewiseContinuous A
      (CliffordCoordinatewiseContinuous.mul V A hx
        (CliffordCoordinatewiseContinuous.reverse V A hx))
      (V.cliffordCoordinatewiseContinuous_closedCoordinateAlgebraMapSimilitude A)
  · apply isClosed_iInter
    intro i
    exact V.isClosed_eq_of_cliffordCoordinatewiseContinuous A
      (CliffordCoordinatewiseContinuous.mul V A
        (CliffordCoordinatewiseContinuous.mul V A hx (hvector i)) hy)
      (V.cliffordCoordinatewiseContinuous_closedCoordinateVectorGraph A i)

/-! ## Closed embedding and local compactness -/

theorem continuous_cliffordGeneralSpinClosedCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (V.cliffordGeneralSpinClosedCoordinateMap A) := by
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply Continuous.prodMk
      · apply continuous_pi
        intro u
        exact V.continuous_cliffordGeneralSpinCliffordCoordinate A u
      · apply continuous_pi
        intro u
        change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
          (V.cliffordCoordinateBaseChangeBasis A).repr
            ((x⁻¹).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra A) u)
        exact (V.continuous_cliffordGeneralSpinCliffordCoordinate A u).comp
          continuous_inv
    · exact V.continuous_cliffordGeneralSpinSimilitude A
  · exact V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom A

theorem cliffordGeneralSpinClosedCoordinateMap_isEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Topology.IsEmbedding (V.cliffordGeneralSpinClosedCoordinateMap A) := by
  let f : V.CliffordGeneralSpinClosedCoordinateSpace A →
      ((Finset (Fin n) → A) × Aˣ) ×
        (Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) A) :=
    fun z => ((z.1.1.1, z.1.2), (z.2.1.1.1, z.2⁻¹.1.1.1))
  have hf : Continuous f := by
    apply Continuous.prodMk
    · exact (continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_fst)
    · apply Continuous.prodMk
      · exact Units.continuous_val.comp
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_snd))
      · exact Units.continuous_val.comp
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp (continuous_inv.comp continuous_snd)))
  have hcomp : f ∘ V.cliffordGeneralSpinClosedCoordinateMap A =
      V.cliffordGeneralSpinPointCoordinateMap A := by
    funext x
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · rfl
    · rfl
  apply Topology.IsEmbedding.of_comp
    (V.continuous_cliffordGeneralSpinClosedCoordinateMap A) hf
  rw [hcomp]
  exact V.cliffordGeneralSpinPointCoordinateMap_isEmbedding A

theorem cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    Topology.IsClosedEmbedding
      (V.cliffordGeneralSpinClosedCoordinateMap A) :=
  ⟨V.cliffordGeneralSpinClosedCoordinateMap_isEmbedding A, by
    rw [V.range_cliffordGeneralSpinClosedCoordinateMap A]
    exact V.isClosed_isCliffordGeneralSpinClosedCoordinate A⟩

noncomputable instance realCliffordGeneralSpinGroupLocallyCompactSpace :
    LocallyCompactSpace V.RealCliffordGeneralSpinGroup := by
  letI : LocallyCompactSpace (V.specialOrthogonalMatrixGroup ℝ) := by
    change LocallyCompactSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup V.realFormMatrix)
    exact V.realSpecialOrthogonalGroupLocallyCompactSpace
  exact (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding ℝ)
    |>.locallyCompactSpace

noncomputable instance padicCliffordGeneralSpinGroupLocallyCompactSpace
    (p : ℕ) [Fact p.Prime] :
    LocallyCompactSpace (V.PadicCliffordGeneralSpinGroup p) := by
  letI : LocallyCompactSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_locallyCompact
      p n V.pairingMatrix V.form_det_ne_zero
  exact (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding ℚ_[p])
    |>.locallyCompactSpace

end RationalQuadraticSpaceMatrix
