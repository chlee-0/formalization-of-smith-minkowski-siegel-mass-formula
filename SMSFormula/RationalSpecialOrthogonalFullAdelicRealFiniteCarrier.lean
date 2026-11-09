import SMSFormula.RationalSpecialOrthogonalInvariantDifferentialPlacewiseGroupMeasure
import SMSFormula.AdelicProperFullPresentation

/-!
# General rational special-orthogonal real/finite adelic splitting

For an arbitrary rational quadratic-space matrix `V`, this module defines its
real, infinite-adelic, and finite-adelic special-orthogonal matrix groups.  It
then restricts the standard topological ring decompositions

```text
𝔸_ℚ ≃ 𝔸_{ℚ,∞} × 𝔸_{ℚ,f},    𝔸_{ℚ,∞} ≃ ℝ
```

to a continuous multiplicative equivalence

```text
V.FullAdelicSpecialOrthogonalGroup ≃ₜ*
  V.RealSpecialOrthogonalGroup × V.FiniteAdelicSpecialOrthogonalGroup.
```

This is a carrier theorem only.  It constructs no restricted-product measure
and makes no differential-normalization or Tamagawa assertion.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Real and finite carriers -/

/-- The rational form matrix extended to the reals. -/
def realFormMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) ℝ :=
  V.pairingMatrix.map (algebraMap ℚ ℝ)

/-- The real orthogonal matrix group of `V`. -/
def realOrthogonalMatrixSubgroup (V : RationalQuadraticSpaceMatrix n) :
    Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  formPreservingMatrixSubgroup V.realFormMatrix

/-- The real special-orthogonal matrix group of `V`. -/
def realSpecialOrthogonalMatrixSubgroup (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.realOrthogonalMatrixSubgroup :=
  specialFormPreservingMatrixSubgroup V.realFormMatrix

/-- The concrete carrier of `SO(V)(ℝ)`. -/
abbrev RealSpecialOrthogonalGroup (V : RationalQuadraticSpaceMatrix n) :=
  V.realSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_realOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : (Matrix (Fin n) (Fin n) ℝ)ˣ) :
    g ∈ V.realOrthogonalMatrixSubgroup ↔
      g.1ᵀ * V.realFormMatrix * g.1 = V.realFormMatrix :=
  Iff.rfl

@[simp]
theorem mem_realSpecialOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.realOrthogonalMatrixSubgroup) :
    g ∈ V.realSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff V.realFormMatrix g

/-- The rational form matrix extended to the finite adeles. -/
def finiteAdelicFormMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  V.pairingMatrix.map (algebraMap ℚ RationalFiniteAdele)

/-- The finite-adelic orthogonal matrix group of `V`. -/
def finiteAdelicOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
  formPreservingMatrixSubgroup V.finiteAdelicFormMatrix

/-- The finite-adelic special-orthogonal matrix group of `V`. -/
def finiteAdelicSpecialOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.finiteAdelicOrthogonalMatrixSubgroup :=
  specialFormPreservingMatrixSubgroup V.finiteAdelicFormMatrix

/-- The concrete carrier of `SO(V)(𝔸_f)`. -/
abbrev FiniteAdelicSpecialOrthogonalGroup
    (V : RationalQuadraticSpaceMatrix n) :=
  V.finiteAdelicSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_finiteAdelicOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) :
    g ∈ V.finiteAdelicOrthogonalMatrixSubgroup ↔
      g.1ᵀ * V.finiteAdelicFormMatrix * g.1 =
        V.finiteAdelicFormMatrix :=
  Iff.rfl

@[simp]
theorem mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.finiteAdelicOrthogonalMatrixSubgroup) :
    g ∈ V.finiteAdelicSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff V.finiteAdelicFormMatrix g

/-! ## Infinite-to-real carrier equivalence -/

/-- The rational form matrix extended to the infinite adeles. -/
def infiniteAdelicFormMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) RationalInfiniteAdele :=
  V.pairingMatrix.map (algebraMap ℚ RationalInfiniteAdele)

/-- The infinite-adelic orthogonal matrix group of `V`. -/
def infiniteAdelicOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup (Matrix (Fin n) (Fin n) RationalInfiniteAdele)ˣ :=
  formPreservingMatrixSubgroup V.infiniteAdelicFormMatrix

/-- The infinite-adelic special-orthogonal matrix group of `V`. -/
def infiniteAdelicSpecialOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.infiniteAdelicOrthogonalMatrixSubgroup :=
  specialFormPreservingMatrixSubgroup V.infiniteAdelicFormMatrix

/-- The concrete carrier of `SO(V)(𝔸_∞)`. -/
abbrev InfiniteAdelicSpecialOrthogonalGroup
    (V : RationalQuadraticSpaceMatrix n) :=
  V.infiniteAdelicSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_infiniteAdelicOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : (Matrix (Fin n) (Fin n) RationalInfiniteAdele)ˣ) :
    g ∈ V.infiniteAdelicOrthogonalMatrixSubgroup ↔
      g.1ᵀ * V.infiniteAdelicFormMatrix * g.1 =
        V.infiniteAdelicFormMatrix :=
  Iff.rfl

@[simp]
theorem mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.infiniteAdelicOrthogonalMatrixSubgroup) :
    g ∈ V.infiniteAdelicSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff V.infiniteAdelicFormMatrix g

/-- The infinite form becomes the real form under the unique rational
infinite-place equivalence. -/
theorem infiniteAdelicFormMatrix_map_equivReal
    (V : RationalQuadraticSpaceMatrix n) :
    V.infiniteAdelicFormMatrix.map rationalInfiniteAdeleRingEquivReal =
      V.realFormMatrix := by
  ext i j
  change
    rationalInfiniteAdeleRingEquivReal
        (algebraMap ℚ RationalInfiniteAdele (V.pairingMatrix i j)) =
      algebraMap ℚ ℝ (V.pairingMatrix i j)
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℚ RationalInfiniteAdele))
      (algebraMap ℚ ℝ))
    (V.pairingMatrix i j)

/-- Mapping entries through `𝔸_{ℚ,∞} ≃ ℝ` gives a homomorphism of the
special-orthogonal carriers. -/
def infiniteAdelicSpecialOrthogonalToRealHom
    (V : RationalQuadraticSpaceMatrix n) :
    V.InfiniteAdelicSpecialOrthogonalGroup →*
      V.RealSpecialOrthogonalGroup where
  toFun g := by
    let mapped : GL (Fin n) ℝ :=
      Units.mapEquiv
        (rationalInfiniteAdeleRingEquivReal.mapMatrix
          (m := Fin n)).toMulEquiv g.1.1
    have hForm : mapped ∈ V.realOrthogonalMatrixSubgroup := by
      rw [V.mem_realOrthogonalMatrixSubgroup_iff]
      have hmapped := congrArg
        rationalInfiniteAdeleRingEquivReal.mapMatrix g.1.2
      simp only [map_mul, RingEquiv.mapMatrix_apply, Matrix.transpose_map,
        V.infiniteAdelicFormMatrix_map_equivReal] at hmapped
      simpa [mapped] using hmapped
    have hgdet : g.1.1.1.det = 1 :=
      (V.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
    have hDet : mapped.1.det = 1 := by
      have hmap := congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det
          (f := rationalInfiniteAdeleRingEquivReal.toRingHom) g.1.1)
      simpa [mapped, hgdet] using hmap
    exact
      ⟨⟨mapped, hForm⟩,
        (V.mem_realSpecialOrthogonalMatrixSubgroup_iff
          ⟨mapped, hForm⟩).2 hDet⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (Units.mapEquiv
        (rationalInfiniteAdeleRingEquivReal.mapMatrix
          (m := Fin n)).toMulEquiv).map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (Units.mapEquiv
        (rationalInfiniteAdeleRingEquivReal.mapMatrix
          (m := Fin n)).toMulEquiv).map_mul g.1.1 h.1.1

/-- The infinite-to-real special-orthogonal homomorphism is bijective. -/
theorem infiniteAdelicSpecialOrthogonalToRealHom_bijective
    (V : RationalQuadraticSpaceMatrix n) :
    Function.Bijective V.infiniteAdelicSpecialOrthogonalToRealHom := by
  let E : GL (Fin n) RationalInfiniteAdele ≃* GL (Fin n) ℝ :=
    Units.mapEquiv
      (rationalInfiniteAdeleRingEquivReal.mapMatrix
        (m := Fin n)).toMulEquiv
  constructor
  · intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    apply E.injective
    exact congrArg (fun z ↦ z.1.1) heq
  · intro y
    let G : GL (Fin n) RationalInfiniteAdele := E.symm y.1.1
    have hGL : E G = y.1.1 := E.apply_symm_apply _
    have hMatrix :
        G.1.map rationalInfiniteAdeleRingEquivReal = y.1.1.1 :=
      congrArg Units.val hGL
    have hForm :
        G.1ᵀ * V.infiniteAdelicFormMatrix * G.1 =
          V.infiniteAdelicFormMatrix := by
      apply rationalInfiniteAdeleRingEquivReal.mapMatrix.injective
      simp only [map_mul, RingEquiv.mapMatrix_apply, Matrix.transpose_map,
        V.infiniteAdelicFormMatrix_map_equivReal]
      rw [hMatrix]
      exact y.1.2
    have hDet : G.1.det = 1 := by
      apply rationalInfiniteAdeleRingEquivReal.injective
      calc
        rationalInfiniteAdeleRingEquivReal G.1.det =
            (G.1.map rationalInfiniteAdeleRingEquivReal).det :=
          RingHom.map_det rationalInfiniteAdeleRingEquivReal.toRingHom G.1
        _ = y.1.1.1.det := congrArg Matrix.det hMatrix
        _ = 1 :=
          (V.mem_realSpecialOrthogonalMatrixSubgroup_iff y.1).mp y.2
        _ = rationalInfiniteAdeleRingEquivReal 1 := by simp
    let gOrth : V.infiniteAdelicOrthogonalMatrixSubgroup := ⟨G, hForm⟩
    let gSpecial : V.InfiniteAdelicSpecialOrthogonalGroup :=
      ⟨gOrth,
        (V.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff
          gOrth).2 hDet⟩
    refine ⟨gSpecial, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hGL

/-- The infinite-adelic and real special-orthogonal carriers are
multiplicatively equivalent. -/
def infiniteAdelicSpecialOrthogonalGroupEquivReal
    (V : RationalQuadraticSpaceMatrix n) :
    V.InfiniteAdelicSpecialOrthogonalGroup ≃*
      V.RealSpecialOrthogonalGroup :=
  MulEquiv.ofBijective V.infiniteAdelicSpecialOrthogonalToRealHom
    V.infiniteAdelicSpecialOrthogonalToRealHom_bijective

/-- The infinite-adelic and real special-orthogonal carriers are continuously
multiplicatively equivalent. -/
def infiniteAdelicSpecialOrthogonalGroupContinuousEquivReal
    (V : RationalQuadraticSpaceMatrix n) :
    V.InfiniteAdelicSpecialOrthogonalGroup ≃ₜ*
      V.RealSpecialOrthogonalGroup where
  toMulEquiv := V.infiniteAdelicSpecialOrthogonalGroupEquivReal
  continuous_toFun := by
    exact
      ((Units.mapContinuousMulEquiv
        (rationalInfiniteAdeleMatrixContinuousMulEquivReal
          (n := n))).continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
            _ |>.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    let E :=
      Units.mapContinuousMulEquiv
        (rationalInfiniteAdeleMatrixContinuousMulEquivReal
          (n := n))
    refine
      (E.symm.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)).congr ?_
    intro y
    symm
    apply E.injective
    change
      E
          (V.infiniteAdelicSpecialOrthogonalGroupEquivReal.symm
            y).1.1 =
        E (E.symm y.1.1)
    calc
      _ = y.1.1 := congrArg (fun z => z.1.1)
        (V.infiniteAdelicSpecialOrthogonalGroupEquivReal.apply_symm_apply y)
      _ = _ := (E.apply_symm_apply y.1.1).symm

/-! ## Full-adelic product carrier -/

/-- The full form projects to the infinite form. -/
theorem fullAdelicFormMatrix_map_fst
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicFormMatrix.map
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) =
      V.infiniteAdelicFormMatrix := by
  apply Matrix.ext
  intro i j
  change
    (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
        (algebraMap ℚ RationalAdele (V.pairingMatrix i j)) =
      algebraMap ℚ RationalInfiniteAdele (V.pairingMatrix i j)
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele))
    (V.pairingMatrix i j)

/-- The full form projects to the finite form. -/
theorem fullAdelicFormMatrix_map_snd
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicFormMatrix.map
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
      V.finiteAdelicFormMatrix := by
  apply Matrix.ext
  intro i j
  change
    (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
        (algebraMap ℚ RationalAdele (V.pairingMatrix i j)) =
      algebraMap ℚ RationalFiniteAdele (V.pairingMatrix i j)
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele))
    (V.pairingMatrix i j)

set_option backward.isDefEq.respectTransparency false in
/-- Projection of a full-adelic special-orthogonal matrix to its infinite and
finite components. -/
def fullAdelicSpecialOrthogonalToProdHom
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSpecialOrthogonalGroup →*
      V.InfiniteAdelicSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup where
  toFun g := by
    let gInf := Matrix.GeneralLinearGroup.map
      (n := Fin n)
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) g.1.1
    let gFin := Matrix.GeneralLinearGroup.map
      (n := Fin n)
      (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) g.1.1
    have hInfForm : gInf ∈ V.infiniteAdelicOrthogonalMatrixSubgroup := by
      rw [V.mem_infiniteAdelicOrthogonalMatrixSubgroup_iff]
      have hmapped := congrArg
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix
          g.1.2
      rw [(RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix.map_mul
        (g.1.1.1ᵀ * V.fullAdelicFormMatrix) g.1.1.1,
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix.map_mul
          g.1.1.1ᵀ V.fullAdelicFormMatrix] at hmapped
      simp only [RingHom.mapMatrix_apply, Matrix.transpose_map,
        V.fullAdelicFormMatrix_map_fst] at hmapped
      simpa [gInf] using hmapped
    have hFinForm : gFin ∈ V.finiteAdelicOrthogonalMatrixSubgroup := by
      rw [V.mem_finiteAdelicOrthogonalMatrixSubgroup_iff]
      have hmapped := congrArg
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix
          g.1.2
      rw [(RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix.map_mul
        (g.1.1.1ᵀ * V.fullAdelicFormMatrix) g.1.1.1,
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix.map_mul
          g.1.1.1ᵀ V.fullAdelicFormMatrix] at hmapped
      simp only [RingHom.mapMatrix_apply, Matrix.transpose_map,
        V.fullAdelicFormMatrix_map_snd] at hmapped
      simpa [gFin] using hmapped
    have hgdet : g.1.1.1.det = 1 :=
      (V.mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
    have hInfDet : gInf.1.det = 1 := by
      have hmap := congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det
          (f := RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
          g.1.1)
      exact hmap.trans (congrArg
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) hgdet)
    have hFinDet : gFin.1.det = 1 := by
      have hmap := congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det
          (f := RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
          g.1.1)
      exact hmap.trans (congrArg
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) hgdet)
    exact
      (⟨⟨gInf, hInfForm⟩,
          (V.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff
            ⟨gInf, hInfForm⟩).2 hInfDet⟩,
        ⟨⟨gFin, hFinForm⟩,
          (V.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff
            ⟨gFin, hFinForm⟩).2 hFinDet⟩)
  map_one' := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact Matrix.GeneralLinearGroup.map_one
        (n := Fin n)
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
    · exact Matrix.GeneralLinearGroup.map_one
        (n := Fin n)
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
  map_mul' g h := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact Matrix.GeneralLinearGroup.map_mul
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) g.1.1 h.1.1
    · exact Matrix.GeneralLinearGroup.map_mul
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) g.1.1 h.1.1

set_option backward.isDefEq.respectTransparency false in
/-- The infinite/finite component projection is bijective. -/
theorem fullAdelicSpecialOrthogonalToProdHom_bijective
    (V : RationalQuadraticSpaceMatrix n) :
    Function.Bijective V.fullAdelicSpecialOrthogonalToProdHom := by
  let E :
      GL (Fin n) RationalAdele ≃*
        GL (Fin n) RationalInfiniteAdele ×
          GL (Fin n) RationalFiniteAdele :=
    generalLinearGroupProdEquiv
  constructor
  · intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    apply E.injective
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1.1) heq
    · exact congrArg (fun z ↦ z.2.1.1) heq
  · intro y
    let G : GL (Fin n) RationalAdele := E.symm (y.1.1.1, y.2.1.1)
    have hcomponents : E G = (y.1.1.1, y.2.1.1) :=
      E.apply_symm_apply _
    have hInfGL :
        Matrix.GeneralLinearGroup.map
            (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) G =
          y.1.1.1 :=
      congrArg Prod.fst hcomponents
    have hFinGL :
        Matrix.GeneralLinearGroup.map
            (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) G =
          y.2.1.1 :=
      congrArg Prod.snd hcomponents
    have hInfMatrix :
        G.1.map (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) =
          y.1.1.1.1 :=
      congrArg Units.val hInfGL
    have hFinMatrix :
        G.1.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
          y.2.1.1.1 :=
      congrArg Units.val hFinGL
    have hFullForm :
        G.1ᵀ * V.fullAdelicFormMatrix * G.1 =
          V.fullAdelicFormMatrix := by
      apply (matrixProdRingEquiv
        (ι := Fin n) (R := RationalInfiniteAdele)
        (S := RationalFiniteAdele)).injective
      rw [(matrixProdRingEquiv (ι := Fin n) (R := RationalInfiniteAdele)
        (S := RationalFiniteAdele)).map_mul
          (G.1ᵀ * V.fullAdelicFormMatrix) G.1,
        (matrixProdRingEquiv (ι := Fin n) (R := RationalInfiniteAdele)
          (S := RationalFiniteAdele)).map_mul G.1ᵀ V.fullAdelicFormMatrix]
      change
        ((G.1ᵀ).map (RingHom.fst RationalInfiniteAdele RationalFiniteAdele),
            (G.1ᵀ).map
              (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)) *
            (V.fullAdelicFormMatrix.map
                (RingHom.fst RationalInfiniteAdele RationalFiniteAdele),
              V.fullAdelicFormMatrix.map
                (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)) *
            (G.1.map
                (RingHom.fst RationalInfiniteAdele RationalFiniteAdele),
              G.1.map
                (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)) =
          (V.fullAdelicFormMatrix.map
              (RingHom.fst RationalInfiniteAdele RationalFiniteAdele),
            V.fullAdelicFormMatrix.map
              (RingHom.snd RationalInfiniteAdele RationalFiniteAdele))
      rw [Matrix.transpose_map, Matrix.transpose_map,
        V.fullAdelicFormMatrix_map_fst, V.fullAdelicFormMatrix_map_snd,
        hInfMatrix, hFinMatrix]
      exact Prod.ext y.1.1.2 y.2.1.2
    have hFullDet : G.1.det = 1 := by
      apply Prod.ext
      · calc
          G.1.det.1 =
              (G.1.map
                (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)).det :=
            RingHom.map_det
              (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) G.1
          _ = y.1.1.1.1.det := congrArg Matrix.det hInfMatrix
          _ = 1 :=
            (V.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff
              y.1.1).mp y.1.2
      · calc
          G.1.det.2 =
              (G.1.map
                (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)).det :=
            RingHom.map_det
              (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) G.1
          _ = y.2.1.1.1.det := congrArg Matrix.det hFinMatrix
          _ = 1 :=
            (V.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff
              y.2.1).mp y.2.2
    let gOrth : V.fullAdelicOrthogonalMatrixSubgroup := ⟨G, hFullForm⟩
    let gSpecial : V.FullAdelicSpecialOrthogonalGroup :=
      ⟨gOrth,
        (V.mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff
          gOrth).2 hFullDet⟩
    refine ⟨gSpecial, ?_⟩
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact hInfGL
    · exact hFinGL

/-- The full-adelic group is multiplicatively equivalent to its infinite and
finite factors. -/
def fullAdelicSpecialOrthogonalGroupProdEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSpecialOrthogonalGroup ≃*
      V.InfiniteAdelicSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup :=
  MulEquiv.ofBijective V.fullAdelicSpecialOrthogonalToProdHom
    V.fullAdelicSpecialOrthogonalToProdHom_bijective

/-- The full-adelic group is continuously multiplicatively equivalent to its
infinite and finite factors. -/
def fullAdelicSpecialOrthogonalGroupProdContinuousEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSpecialOrthogonalGroup ≃ₜ*
      V.InfiniteAdelicSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup where
  toMulEquiv := V.fullAdelicSpecialOrthogonalGroupProdEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · exact
        (((generalLinearGroupProdContinuousEquiv.continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val)).fst).subtype_mk
            _).subtype_mk _
    · exact
        (((generalLinearGroupProdContinuousEquiv.continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val)).snd).subtype_mk
            _).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    let E :
        GL (Fin n) RationalAdele ≃ₜ*
          GL (Fin n) RationalInfiniteAdele ×
            GL (Fin n) RationalFiniteAdele :=
      generalLinearGroupProdContinuousEquiv
    let componentVals := fun y :
        V.InfiniteAdelicSpecialOrthogonalGroup ×
          V.FiniteAdelicSpecialOrthogonalGroup =>
      (y.1.1.1, y.2.1.1)
    have hcomponentVals : Continuous componentVals := by
      apply Continuous.prodMk
      · exact
          (continuous_subtype_val.comp continuous_subtype_val).comp
            continuous_fst
      · exact
          (continuous_subtype_val.comp continuous_subtype_val).comp
            continuous_snd
    refine (E.symm.continuous.comp hcomponentVals).congr ?_
    intro y
    symm
    apply E.injective
    change
      E (V.fullAdelicSpecialOrthogonalGroupProdEquiv.symm y).1.1 =
        E (E.symm (componentVals y))
    calc
      _ = componentVals y := congrArg
        (fun z => (z.1.1.1, z.2.1.1))
        (V.fullAdelicSpecialOrthogonalGroupProdEquiv.apply_symm_apply y)
      _ = _ := (E.apply_symm_apply (componentVals y)).symm

/-- The general full-adelic special-orthogonal group splits topologically
into its real and finite-adelic factors. -/
def fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSpecialOrthogonalGroup ≃ₜ*
      V.RealSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup :=
  V.fullAdelicSpecialOrthogonalGroupProdContinuousEquiv.trans
    (prodContinuousMulEquiv
      V.infiniteAdelicSpecialOrthogonalGroupContinuousEquivReal
      (ContinuousMulEquiv.refl _))

/-! ## Literal component and inverse formulas -/

@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_real_matrix
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    ((V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).1 :
        V.realOrthogonalMatrixSubgroup).1.1 =
      (g.1.1.1.map
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)).map
          rationalInfiniteAdeleRingEquivReal := by
  rfl

@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_finite_matrix
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    ((V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 :
        V.finiteAdelicOrthogonalMatrixSubgroup).1.1 =
      g.1.1.1.map
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) := by
  rfl

@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_symm_apply_apply
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
        (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g) =
      g :=
  V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm_apply_apply g

@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_symm_apply
    (V : RationalQuadraticSpaceMatrix n)
    (x :
      V.RealSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup) :
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm x) =
      x :=
  V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply x

end RationalQuadraticSpaceMatrix
