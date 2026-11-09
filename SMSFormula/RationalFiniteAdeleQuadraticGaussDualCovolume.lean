import SMSFormula.RationalFiniteAdeleQuadraticGaussDualPeriodicity
import SMSFormula.RationalAdeleRationalMatrixHaar

/-!
# The exact polar-dual covolume and denominator index

This file computes the raw mass of the intrinsic finite polar-dual lattice.
The full rational-adelic polar matrix preserves the fixed adelic coordinate
Haar.  After the canonical real--finite split, its real component has
Jacobian `polarDeterminant(L)⁻¹`; evaluation on a real unit cube times `Zhat^n` therefore
forces the finite preimage `C⁻¹ Zhat^n` to have mass `|polarDeterminant(L)|`.

For a nonzero natural denominator `m`, an adjugate containment supplies a
finite-index subgroup inside the literal embedded `m Zhat^n`.  The exact
index then follows from invariant Haar and the already proved mass
`m⁻ⁿ` of that subgroup:

`[C⁻¹ Zhat^n : m Zhat^n] = |polarDeterminant(L)| * m^n`.

The argument uses neither primewise coordinates nor residue representatives.
It does not average the polar-dual quadratic phase or assert a Gauss
reciprocity value.
-/

open PositiveDefiniteIntegralLattice MeasureTheory Matrix Set
open scoped ENNReal

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The real and finite components of the exact polar-matrix action after the
canonical adelic split. -/
def realFinitePolarMatrixMap (L : PositiveDefiniteIntegralLattice n) :
    ((Fin n → ℝ) × (Fin n → RationalFiniteAdele)) →
      ((Fin n → ℝ) × (Fin n → RationalFiniteAdele)) :=
  fun p ↦
    (Matrix.toLin' L.rationalQuadraticSpaceMatrix.realPolarMatrix p.1,
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec p.2)

/-- The split real--finite polar action preserves the product Haar exactly.
Its reciprocal real and finite determinant moduli have already cancelled in
the full rational-adelic matrix theorem. -/
theorem measurePreserving_realFinitePolarMatrixMap
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurePreserving (realFinitePolarMatrixMap L)
      ((volume : Measure (Fin n → ℝ)).prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n))
      ((volume : Measure (Fin n → ℝ)).prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
  let e := PositiveDefiniteIntegralLattice.rationalAdeleVectorRealFiniteEquiv n
  have hs := PositiveDefiniteIntegralLattice.measurePreserving_rationalAdeleVectorRealFiniteSplit n
  have hs_inv := hs.symm e
  have hc := PositiveDefiniteIntegralLattice.measurePreserving_fullAdelicPolarMatrix_mulVec
    L.rationalQuadraticSpaceMatrix
  have hcomp := hs.comp (hc.comp hs_inv)
  convert hcomp using 1
  funext p
  change realFinitePolarMatrixMap L p =
    (PositiveDefiniteIntegralLattice.rationalAdeleVectorRealPart n
      (L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec (e.symm p)),
     PositiveDefiniteIntegralLattice.rationalAdeleVectorFinitePart n
      (L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec (e.symm p)))
  unfold realFinitePolarMatrixMap
  rw [PositiveDefiniteIntegralLattice.rationalAdeleVectorRealPart_fullAdelicPolarMatrix_mulVec,
    PositiveDefiniteIntegralLattice.rationalAdeleVectorFinitePart_fullAdelicPolarMatrix_mulVec]
  have he := e.apply_symm_apply p
  apply Prod.ext
  · exact congrArg
      (fun z ↦ Matrix.toLin'
        L.rationalQuadraticSpaceMatrix.realPolarMatrix z)
      (congrArg Prod.fst he).symm
  · exact congrArg
      (fun z ↦
        L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec z)
      (congrArg Prod.snd he).symm

private def realUnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun _ ↦ Set.Icc 0 1)

private theorem measurableSet_realUnitCube (n : ℕ) :
    MeasurableSet (realUnitCube n) := by
  exact MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc

@[simp]
private theorem volume_realUnitCube (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) (realUnitCube n) = 1 := by
  rw [realUnitCube, volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc]

@[simp]
private theorem rationalFiniteAdeleCoordinateAddHaarMeasure_integralVectors
    (n : ℕ) :
    rationalFiniteAdeleCoordinateAddHaarMeasure n
        (integralFiniteAdeleVectors n) = 1 := by
  rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
  rw [show integralFiniteAdeleVectors n =
      Set.univ.pi fun _ : Fin n ↦
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) by
    ext x
    simp [integralFiniteAdeleVectors]]
  change (Measure.pi fun _ : Fin n ↦ rationalFiniteAdeleAddHaarMeasure)
    (Set.univ.pi fun _ : Fin n ↦
      (integralFiniteAdeleSubring : Set RationalFiniteAdele)) = 1
  rw [Measure.pi_pi]
  simp

private theorem realPolarMap_preimage_cube_volume
    (L : PositiveDefiniteIntegralLattice n) :
    (volume : Measure (Fin n → ℝ))
        ((Matrix.toLin' L.rationalQuadraticSpaceMatrix.realPolarMatrix) ⁻¹'
          realUnitCube n) =
      ENNReal.ofReal
        L.rationalQuadraticSpaceMatrix.realPolarMatrix.det⁻¹ := by
  have h := congrArg (fun mu : Measure (Fin n → ℝ) ↦ mu (realUnitCube n))
    L.map_rationalQuadraticSpaceMatrix_realPolarMatrix_volume
  change
    (Measure.map
      (Matrix.toLin' L.rationalQuadraticSpaceMatrix.realPolarMatrix) volume)
        (realUnitCube n) = _ at h
  rw [Measure.map_apply (by fun_prop) (measurableSet_realUnitCube n)] at h
  change
    volume
        ((Matrix.toLin' L.rationalQuadraticSpaceMatrix.realPolarMatrix) ⁻¹'
          realUnitCube n) =
      (ENNReal.ofReal
        L.rationalQuadraticSpaceMatrix.realPolarMatrix.det⁻¹ •
        (volume : Measure (Fin n → ℝ))) (realUnitCube n) at h
  rw [Measure.smul_apply, volume_realUnitCube, smul_eq_mul, mul_one] at h
  exact h

private theorem realFinitePolarMatrixMap_preimage_rectangle
    (L : PositiveDefiniteIntegralLattice n) :
    realFinitePolarMatrixMap L ⁻¹'
        (realUnitCube n ×ˢ integralFiniteAdeleVectors n) =
      ((Matrix.toLin' L.rationalQuadraticSpaceMatrix.realPolarMatrix) ⁻¹'
          realUnitCube n) ×ˢ
        L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by
  ext p
  rfl

/-- The intrinsic finite polar-dual lattice has the exact determinant mass
forced by full adelic matrix invariance and the real Jacobian. -/
theorem rationalFiniteAdeleCoordinateAddHaarMeasure_finitePolarDualLattice
    (L : PositiveDefiniteIntegralLattice n) :
    rationalFiniteAdeleCoordinateAddHaarMeasure n
        L.rationalQuadraticSpaceMatrix.finitePolarDualLattice =
      ENNReal.ofReal L.rationalQuadraticSpaceMatrix.realPolarMatrix.det := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  have hrect := (measurePreserving_realFinitePolarMatrixMap L).measure_preimage
    ((measurableSet_realUnitCube n).prod
      (measurableSet_integralFiniteAdeleVectors n)).nullMeasurableSet
  rw [realFinitePolarMatrixMap_preimage_rectangle L] at hrect
  rw [Measure.prod_prod, Measure.prod_prod,
    realPolarMap_preimage_cube_volume, volume_realUnitCube,
    rationalFiniteAdeleCoordinateAddHaarMeasure_integralVectors,
    one_mul] at hrect
  let D : ENNReal :=
    ENNReal.ofReal L.rationalQuadraticSpaceMatrix.realPolarMatrix.det
  have hD0 : D ≠ 0 := by
    exact ne_of_gt <| ENNReal.ofReal_pos.mpr
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
  have hDtop : D ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv :
      ENNReal.ofReal L.rationalQuadraticSpaceMatrix.realPolarMatrix.det⁻¹ =
        D⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos]
  rw [hinv] at hrect
  calc
    rationalFiniteAdeleCoordinateAddHaarMeasure n
        L.rationalQuadraticSpaceMatrix.finitePolarDualLattice =
        1 * rationalFiniteAdeleCoordinateAddHaarMeasure n
          L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by simp
    _ = (D * D⁻¹) * rationalFiniteAdeleCoordinateAddHaarMeasure n
          L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by
        rw [ENNReal.mul_inv_cancel hD0 hDtop]
    _ = D * (D⁻¹ * rationalFiniteAdeleCoordinateAddHaarMeasure n
          L.rationalQuadraticSpaceMatrix.finitePolarDualLattice) := by
        rw [mul_assoc]
    _ = D * 1 := by rw [hrect]
    _ = D := mul_one D

/-- The raw restricted Haar on the polar-dual subtype has total mass equal to
the real polar determinant. -/
@[simp]
theorem finitePolarDualAddHaarMeasure_univ (L : PositiveDefiniteIntegralLattice n) :
    finitePolarDualAddHaarMeasure L Set.univ =
      ENNReal.ofReal L.rationalQuadraticSpaceMatrix.realPolarMatrix.det := by
  have h := congrArg
    (fun mu : Measure (Fin n → RationalFiniteAdele) ↦ mu Set.univ)
    (measurePreserving_finitePolarDualCoe L).map_eq
  change
    (Measure.map Subtype.val (finitePolarDualAddHaarMeasure L)) Set.univ =
      ((rationalFiniteAdeleCoordinateAddHaarMeasure n).restrict
        L.rationalQuadraticSpaceMatrix.finitePolarDualLattice) Set.univ at h
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ] at h
  exact h.trans
    (rationalFiniteAdeleCoordinateAddHaarMeasure_finitePolarDualLattice L)

/-- Integral positivity rewrites the raw polar-dual mass as the natural
absolute discriminant. -/
theorem finitePolarDualAddHaarMeasure_univ_eq_natAbs_polarDeterminant
    (L : PositiveDefiniteIntegralLattice n) :
    finitePolarDualAddHaarMeasure L Set.univ =
      (L.polarDeterminant.natAbs : ENNReal) := by
  rw [finitePolarDualAddHaarMeasure_univ,
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_det]
  have hdisc : (L.polarDeterminant.natAbs : ℝ) = (L.polarDeterminant : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_pos]
    exact_mod_cast L.polarDeterminant_pos
  rw [← hdisc]
  exact ENNReal.ofReal_natCast L.polarDeterminant.natAbs

private def finitePolarDualDiscDenDilationAddSubgroup
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    AddSubgroup (FinitePolarDualAdeleVector L) :=
  (integralFiniteAdeleCoordinateNatDilation n (m * L.polarDeterminant.natAbs)).range.comap
    (finitePolarDualEquivIntegralCoordinates L).toAddMonoidHom

private theorem finitePolarDualDiscDenDilationAddSubgroup_index
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (hm : m ≠ 0) :
    (finitePolarDualDiscDenDilationAddSubgroup L m).index =
      (m * L.polarDeterminant.natAbs) ^ n := by
  rw [finitePolarDualDiscDenDilationAddSubgroup,
    AddSubgroup.index_comap_of_surjective _
      (finitePolarDualEquivIntegralCoordinates L).surjective]
  exact integralFiniteAdeleCoordinateNatDilation_range_index n
    (m * L.polarDeterminant.natAbs) <| mul_ne_zero hm <|
      Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos)

private noncomputable instance
    finitePolarDualDiscDenDilationAddSubgroupFiniteIndex
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    (finitePolarDualDiscDenDilationAddSubgroup L m).FiniteIndex :=
  ⟨by
    rw [finitePolarDualDiscDenDilationAddSubgroup_index L m (NeZero.ne m)]
    exact pow_ne_zero n <| mul_ne_zero (NeZero.ne m) <|
      Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos)⟩

private theorem integralFiniteAdeleVectors_mulVec_intMatrix
    (C : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → RationalFiniteAdele)
    (hz : z ∈ integralFiniteAdeleVectors n) :
    (C.map (algebraMap ℤ RationalFiniteAdele)).mulVec z ∈
      integralFiniteAdeleVectors n := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem integralFiniteAdeleSubring fun j _ ↦
    integralFiniteAdeleSubring.mul_mem
      (integer_mem_integralFiniteAdeleSubring (C i j)) (hz j)

private theorem finitePolarDualDiscDenDilationAddSubgroup_le_denDilation
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    finitePolarDualDiscDenDilationAddSubgroup L m ≤
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range := by
  intro x hx
  change finitePolarDualEquivIntegralCoordinates L x ∈
      (integralFiniteAdeleCoordinateNatDilation n
        (m * L.polarDeterminant.natAbs)).range at hx
  rcases hx with ⟨z, hz⟩
  let za : Fin n → RationalFiniteAdele := fun i ↦ (z i : RationalFiniteAdele)
  let Afa : Matrix (Fin n) (Fin n) RationalFiniteAdele :=
    L.polarGramMatrix.adjugate.map (algebraMap ℤ RationalFiniteAdele)
  have hza : za ∈ integralFiniteAdeleVectors n := fun i ↦ (z i).property
  have hwa : Afa.mulVec za ∈ integralFiniteAdeleVectors n :=
    integralFiniteAdeleVectors_mulVec_intMatrix L.polarGramMatrix.adjugate za hza
  let w : Fin n → IntegralFiniteAdele := fun i ↦
    ⟨(Afa.mulVec za) i, hwa i⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixLinearEquiv.injective
  rw [finiteAdelicPolarMatrixLinearEquiv_apply]
  let Cfa := L.polarGramMatrix.map (algebraMap ℤ RationalFiniteAdele)
  have hC :
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix = Cfa :=
    L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix
  have hmapAdjugate :
      Cfa * Afa = L.polarDeterminant •
          (1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) := by
    dsimp [Cfa, Afa]
    rw [← Matrix.map_mul, Matrix.mul_adjugate]
    rw [show L.polarGramMatrix.det = L.polarDeterminant by rfl]
    simpa using Matrix.map_smul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant
      (fun a ↦ map_zsmul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant a)
      (1 : Matrix (Fin n) (Fin n) ℤ)
  have hzval := congrArg
    (fun y : Fin n → IntegralFiniteAdele ↦
      fun i ↦ (y i : RationalFiniteAdele)) hz
  have hCx :
      (m * L.polarDeterminant.natAbs) • za =
        L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x.1 := by
    simpa [za, integralFiniteAdeleCoordinateNatDilation, nsmul_eq_mul] using hzval
  rw [hC] at hCx
  change
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
        (m • (fun i ↦ (w i : RationalFiniteAdele))) =
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x.1
  rw [hC]
  calc
    Cfa.mulVec (m • (fun i ↦ (w i : RationalFiniteAdele))) =
        (m : RationalFiniteAdele) • Cfa.mulVec (Afa.mulVec za) := by
          change Cfa.mulVec (m • Afa.mulVec za) = _
          rw [show m • Afa.mulVec za =
            (m : RationalFiniteAdele) • Afa.mulVec za by
              ext i
              simp [nsmul_eq_mul]]
          rw [Matrix.mulVec_smul]
    _ = (m : RationalFiniteAdele) • (L.polarDeterminant : RationalFiniteAdele) • za := by
          rw [Matrix.mulVec_mulVec, hmapAdjugate,
            Matrix.smul_mulVec, Matrix.one_mulVec]
          ext i
          simp [zsmul_eq_mul]
    _ = (m * L.polarDeterminant.natAbs) • za := by
          have hdiscInt : (L.polarDeterminant.natAbs : ℤ) = L.polarDeterminant :=
            Int.natAbs_of_nonneg (le_of_lt L.polarDeterminant_pos)
          have hdisc : (L.polarDeterminant : RationalFiniteAdele) =
              (L.polarDeterminant.natAbs : RationalFiniteAdele) := by
            calc
              (L.polarDeterminant : RationalFiniteAdele) =
                  algebraMap ℤ RationalFiniteAdele L.polarDeterminant := by norm_num
              _ = algebraMap ℤ RationalFiniteAdele
                  (L.polarDeterminant.natAbs : ℤ) := by rw [hdiscInt]
              _ = (L.polarDeterminant.natAbs : RationalFiniteAdele) := by norm_num
          ext i
          simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
          rw [hdisc]
          norm_num
          ring_nf
    _ = Cfa.mulVec x.1 := hCx

/-- In integral coordinates, the scalar lattice dilated by
`m * |polarDeterminant L|` is contained in the literal `m * C` polar denominator
lattice.  This is the section-free adjugate containment used to pass from a
rectangular residue quotient to the intrinsic polar-matrix quotient. -/
theorem integralFiniteAdeleCoordinateNatDiscDilation_range_le_polarDenDilation
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    (integralFiniteAdeleCoordinateNatDilation n
        (m * L.polarDeterminant.natAbs)).range ≤
      ((integralFiniteAdelePolarMatrixEnd L).comp
        (integralFiniteAdeleCoordinateNatDilation n m)).range := by
  intro x hx
  let y : FinitePolarDualAdeleVector L :=
    (finitePolarDualEquivIntegralCoordinates L).symm x
  have hyDisc : y ∈ finitePolarDualDiscDenDilationAddSubgroup L m := by
    change finitePolarDualEquivIntegralCoordinates L y ∈
      (integralFiniteAdeleCoordinateNatDilation n
        (m * L.polarDeterminant.natAbs)).range
    simpa [y] using hx
  have hyDen :=
    finitePolarDualDiscDenDilationAddSubgroup_le_denDilation L m hyDisc
  have hmap : finitePolarDualEquivIntegralCoordinates L y ∈
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range.map
        (finitePolarDualEquivIntegralCoordinates L).toAddMonoidHom :=
    ⟨y, hyDen, rfl⟩
  rw [finitePolarDualEquivIntegralCoordinates_map_denDilation_range] at hmap
  simpa [y] using hmap

/-- The literal embedded denominator lattice has finite index in the
polar-dual additive carrier.  The construction uses the adjugate lower
subgroup and stores no quotient representatives. -/
noncomputable instance finitePolarDualDenDilationRangeFiniteIndex
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range.FiniteIndex :=
  AddSubgroup.finiteIndex_of_le
    (finitePolarDualDiscDenDilationAddSubgroup_le_denDilation L m)

local instance rationalFiniteAdeleCoordinateAddHaarMeasure_isAddLeftInvariant_dualCovolume
    (d : ℕ) :
    Measure.IsAddLeftInvariant
      (rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  refine ⟨fun z ↦ ?_⟩
  change Measure.map (fun x ↦ z + x)
      (Measure.pi fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure) =
    Measure.pi fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure
  exact (measurePreserving_pi
    (fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure)
    (fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure)
    (fun i ↦ measurePreserving_add_left
      rationalFiniteAdeleAddHaarMeasure (z i))).map_eq

noncomputable instance finitePolarDualAddHaarMeasure_isAddLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsAddLeftInvariant (finitePolarDualAddHaarMeasure L) := by
  exact Measure.IsAddLeftInvariant.comap
    (G := FinitePolarDualAdeleVector L)
    (rationalFiniteAdeleCoordinateAddHaarMeasure n)
    (f := (finitePolarDualAddSubgroup L).subtype)
    (MeasurableEmbedding.subtype_coe
      (measurableSet_finitePolarDualLattice L))

/-- Exact finite index of the embedded denominator lattice in the raw
polar-dual carrier.  The factor `|polarDeterminant(L)|` appears explicitly. -/
theorem finitePolarDualDenDilationRange_index
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range.index =
      L.polarDeterminant.natAbs * m ^ n := by
  let H :=
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range
  have hindex := AddSubgroup.index_mul_measure H
    (measurableSet_integralFiniteAdeleCoordinateNatDilationToPolarDual_range
      L m (NeZero.ne m))
    (finitePolarDualAddHaarMeasure L)
  rw [finitePolarDualAddHaarMeasure_denDilation_range L m (NeZero.ne m),
    finitePolarDualAddHaarMeasure_univ_eq_natAbs_polarDeterminant] at hindex
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hmtop : (m : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top m
  have hcancel : ((m : ENNReal)⁻¹) ^ n * (m : ENNReal) ^ n = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel hm0 hmtop, one_pow]
  have hcast : (H.index : ENNReal) =
      ((L.polarDeterminant.natAbs * m ^ n : ℕ) : ENNReal) := by
    calc
      (H.index : ENNReal) = (H.index : ENNReal) * 1 := by simp
      _ = (H.index : ENNReal) *
          (((m : ENNReal)⁻¹) ^ n * (m : ENNReal) ^ n) := by rw [hcancel]
      _ = ((H.index : ENNReal) * ((m : ENNReal)⁻¹) ^ n) *
          (m : ENNReal) ^ n := by rw [mul_assoc]
      _ = (L.polarDeterminant.natAbs : ENNReal) * (m : ENNReal) ^ n := by rw [hindex]
      _ = ((L.polarDeterminant.natAbs * m ^ n : ℕ) : ENNReal) := by norm_num
  exact_mod_cast hcast

end RationalQuadraticSpaceMatrix
