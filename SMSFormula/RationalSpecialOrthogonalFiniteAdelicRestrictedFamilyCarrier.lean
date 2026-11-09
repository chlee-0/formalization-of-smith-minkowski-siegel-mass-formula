import SMSFormula.RationalSpecialOrthogonalFiniteAdelicLocalEvaluationCarrier

/-!
# Restricted-family presentation of the finite-adelic special-orthogonal group

For an arbitrary rational quadratic-space matrix `V`, this module reverses
the simultaneous height-one evaluation constructed in
`RationalSpecialOrthogonalFiniteAdelicLocalEvaluationCarrier`.  A family of
local p-adic special-orthogonal matrices whose matrix and inverse matrix are
integral at all but finitely many places is assembled entrywise into a
finite-adelic matrix unit.  Local extensionality proves the form and
determinant-one equations.

The resulting presentation is a multiplicative equivalence.  No topology or
measure is transported through it: the restricted-family subtype carries the
subspace topology from the unrestricted product, whereas the finite adeles
carry the restricted-product topology, and no reverse-continuity theorem
identifying these structures is presently available.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicRestrictedFamilyPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## The restricted-family subgroup -/

private theorem heightOnePadicSpecialOrthogonalIsIntegral_one
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v 1 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro i j
    change e.symm ((1 : Matrix (Fin n) (Fin n)
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) i j) ∈
        v.adicCompletionIntegers ℚ
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  · intro i j
    change e.symm ((1 : Matrix (Fin n) (Fin n)
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) i j) ∈
        v.adicCompletionIntegers ℚ
    by_cases h : i = j
    · subst j
      simp
    · simp [h]

private theorem heightOnePadicSpecialOrthogonalIsIntegral_mul
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g h : V.HeightOnePadicSpecialOrthogonalGroup v}
    (hg : V.HeightOnePadicSpecialOrthogonalIsIntegral v g)
    (hh : V.HeightOnePadicSpecialOrthogonalIsIntegral v h) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v (g * h) := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro i j
    change e.symm ((g.1.1.1 * h.1.1.1) i j) ∈
      v.adicCompletionIntegers ℚ
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hg.1 i k) (hh.1 k j)
  · intro i j
    change e.symm (((h.1.1⁻¹).1 * (g.1.1⁻¹).1) i j) ∈
      v.adicCompletionIntegers ℚ
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hh.2 i k) (hg.2 k j)

private theorem heightOnePadicSpecialOrthogonalIsIntegral_inv
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g : V.HeightOnePadicSpecialOrthogonalGroup v}
    (hg : V.HeightOnePadicSpecialOrthogonalIsIntegral v g) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v g⁻¹ := by
  constructor
  · exact hg.2
  · simpa using hg.1

/-- The local special-orthogonal families satisfying the actual cofinite
matrix-and-inverse integrality condition form a subgroup of the unrestricted
dependent product. -/
def finiteAdelicSpecialOrthogonalRestrictedFamilySubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.HeightOnePadicSpecialOrthogonalGroupProduct where
  carrier := {g | V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g}
  one_mem' := by
    show V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily 1
    exact Filter.Eventually.of_forall fun v =>
      heightOnePadicSpecialOrthogonalIsIntegral_one V v
  mul_mem' := by
    intro g h hg hh
    change V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g at hg
    change V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily h at hh
    show V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily (g * h)
    filter_upwards [hg, hh] with v hgv hhv
    exact heightOnePadicSpecialOrthogonalIsIntegral_mul V v hgv hhv
  inv_mem' := by
    intro g hg
    change V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g at hg
    show V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g⁻¹
    filter_upwards [hg] with v hgv
    exact heightOnePadicSpecialOrthogonalIsIntegral_inv V v hgv

@[simp]
theorem mem_finiteAdelicSpecialOrthogonalRestrictedFamilySubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.HeightOnePadicSpecialOrthogonalGroupProduct) :
    g ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilySubgroup ↔
      V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g :=
  Iff.rfl

/-- The carrier of restricted p-adic special-orthogonal families. -/
abbrev FiniteAdelicSpecialOrthogonalRestrictedFamily
    (V : RationalQuadraticSpaceMatrix n) :=
  V.finiteAdelicSpecialOrthogonalRestrictedFamilySubgroup

/-! ## Entrywise finite-adele assembly -/

/-- Assemble one entry of a restricted local matrix family as a rational
finite adele. -/
noncomputable def finiteAdelicSpecialOrthogonalRestrictedFamilyMatrixEntry
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily)
    (i j : Fin n) : RationalFiniteAdele :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1 v).1.1.1 i j),
    (show V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g.1 from g.2).mono
      fun _v hv => hv.1 i j⟩

@[simp]
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyMatrixEntry_apply
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily)
    (i j : Fin n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrixEntry g i j v =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g.1 v).1.1.1 i j) :=
  rfl

/-- Assemble one inverse-matrix entry of a restricted local family as a
rational finite adele. -/
noncomputable def
    finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrixEntry
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily)
    (i j : Fin n) : RationalFiniteAdele :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        (((g.1 v).1.1⁻¹).1 i j),
    (show V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily g.1 from g.2).mono
      fun _v hv => hv.2 i j⟩

@[simp]
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrixEntry_apply
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily)
    (i j : Fin n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrixEntry g i j v =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        (((g.1 v).1.1⁻¹).1 i j) :=
  rfl

/-- The finite-adelic matrix assembled from a restricted local family. -/
noncomputable def finiteAdelicSpecialOrthogonalRestrictedFamilyMatrix
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  fun i j =>
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrixEntry g i j

/-- The finite-adelic inverse matrix assembled from a restricted local
family. -/
noncomputable def finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrix
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  fun i j =>
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrixEntry g i j

/-- The assembled matrix and inverse matrix form a finite-adelic matrix
unit. -/
noncomputable def finiteAdelicSpecialOrthogonalRestrictedFamilyGL
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    GL (Fin n) RationalFiniteAdele := by
  let A :=
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrix g
  let B :=
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrix g
  refine ⟨A, B, ?_, ?_⟩
  · ext i j v
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    let φ : RationalFiniteAdele →+*
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
      e.toRingEquiv.toRingHom.comp ev
    apply e.injective
    change φ ((A * B) i j) =
      φ ((1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j)
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul]
    have hA (a b : Fin n) :
        φ (A a b) = (g.1 v).1.1.1 a b :=
      e.apply_symm_apply _
    have hB (a b : Fin n) :
        φ (B a b) = ((g.1 v).1.1⁻¹).1 a b :=
      e.apply_symm_apply _
    simp_rw [hA, hB]
    have hij := congr_fun (congr_fun (g.1 v).1.1.val_inv i) j
    change
      (∑ k, (g.1 v).1.1.1 i k * ((g.1 v).1.1⁻¹).1 k j) =
        (1 : Matrix (Fin n) (Fin n)
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) i j at hij
    by_cases h : i = j
    · subst j
      simpa [Matrix.one_apply] using hij
    · simpa [Matrix.one_apply, h] using hij
  · ext i j v
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    let φ : RationalFiniteAdele →+*
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
      e.toRingEquiv.toRingHom.comp ev
    apply e.injective
    change φ ((B * A) i j) =
      φ ((1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j)
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul]
    have hA (a b : Fin n) :
        φ (A a b) = (g.1 v).1.1.1 a b :=
      e.apply_symm_apply _
    have hB (a b : Fin n) :
        φ (B a b) = ((g.1 v).1.1⁻¹).1 a b :=
      e.apply_symm_apply _
    simp_rw [hA, hB]
    have hij := congr_fun (congr_fun (g.1 v).1.1.inv_val i) j
    change
      (∑ k, ((g.1 v).1.1⁻¹).1 i k * (g.1 v).1.1.1 k j) =
        (1 : Matrix (Fin n) (Fin n)
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) i j at hij
    by_cases h : i = j
    · subst j
      simpa [Matrix.one_apply] using hij
    · simpa [Matrix.one_apply, h] using hij

/-! ## Local recovery and special-orthogonal assembly -/

/-- Evaluating the assembled finite-adelic matrix unit recovers the local
matrix unit at every height-one place. -/
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyGL_map_eval
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    Matrix.GeneralLinearGroup.map
        ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
          ev)
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyGL g) =
      (g.1 v).1.1 := by
  dsimp only
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply
      ((g.1 v).1.1.1 i j)

/-- Assemble a restricted local special-orthogonal family into the
finite-adelic special-orthogonal group. -/
noncomputable def finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    V.FiniteAdelicSpecialOrthogonalGroup := by
  let U := V.finiteAdelicSpecialOrthogonalRestrictedFamilyGL g
  have hform :
      U.1ᵀ * V.finiteAdelicFormMatrix * U.1 =
        V.finiteAdelicFormMatrix := by
    ext i j v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
    let φ : RationalFiniteAdele →+*
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
      e.toRingEquiv.toRingHom.comp ev
    apply e.injective
    have hU :
        U.1.map φ = (g.1 v).1.1.1 := by
      exact congrArg Units.val
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyGL_map_eval g v)
    have hF :
        V.finiteAdelicFormMatrix.map φ =
          V.pairingMatrix.map
            (algebraMap ℚ
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
      ext a b
      exact φ.toRatAlgHom.commutes (V.pairingMatrix a b)
    have hmatrix :
        (U.1ᵀ * V.finiteAdelicFormMatrix * U.1).map φ =
          V.finiteAdelicFormMatrix.map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hU, hF]
      exact (g.1 v).1.2
    exact congr_fun (congr_fun hmatrix i) j
  let go : V.finiteAdelicOrthogonalMatrixSubgroup :=
    ⟨U, hform⟩
  have hdet : U.1.det = 1 := by
    ext v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
    let φ : RationalFiniteAdele →+*
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
      e.toRingEquiv.toRingHom.comp ev
    apply e.injective
    change φ U.1.det = φ 1
    rw [map_one, RingHom.map_det]
    have hU :
        U.1.map φ = (g.1 v).1.1.1 := by
      exact congrArg Units.val
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyGL_map_eval g v)
    change (U.1.map φ).det = 1
    rw [hU]
    exact
      (mem_specialFormPreservingMatrixSubgroup_iff
        (V.pairingMatrix.map
          (algebraMap ℚ
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
        (g.1 v).1).mp (g.1 v).2
  exact
    ⟨go,
      (V.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff go).2 hdet⟩

/-- Simultaneous evaluation of the assembled finite adele recovers the
original restricted local family. -/
theorem
    finiteAdelicSpecialOrthogonalHeightOneComponents_assembly
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly g) =
      g.1 := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  calc
    (V.finiteAdelicSpecialOrthogonalHeightOneComponent
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly g) v).1.1.1 =
        Matrix.GeneralLinearGroup.map
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
            (RestrictedProduct.evalRingHom
              (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
                w.adicCompletion ℚ) v))
          (V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly g).1.1 :=
      V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly g) v
    _ = (g.1 v).1.1.1 :=
      congrArg Units.val
        (V.finiteAdelicSpecialOrthogonalRestrictedFamilyGL_map_eval g v)

/-- Reverse assembly of the evaluated restricted family recovers the
original finite-adelic special-orthogonal element. -/
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly_components
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly
        ⟨V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom a,
          V.finiteAdelicSpecialOrthogonalHeightOneComponents_isRestrictedFamily
            a⟩ =
      a := by
  apply V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom_injective
  exact
    V.finiteAdelicSpecialOrthogonalHeightOneComponents_assembly
      ⟨V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom a,
        V.finiteAdelicSpecialOrthogonalHeightOneComponents_isRestrictedFamily
          a⟩

/-! ## Multiplicative equivalence -/

/-- The finite-adelic special-orthogonal group is multiplicatively
equivalent to the subtype of p-adic special-orthogonal families satisfying
the actual cofinite matrix-and-inverse integrality condition. -/
noncomputable def
    finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.FiniteAdelicSpecialOrthogonalGroup ≃*
      V.FiniteAdelicSpecialOrthogonalRestrictedFamily where
  toFun a :=
    ⟨V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom a,
      V.finiteAdelicSpecialOrthogonalHeightOneComponents_isRestrictedFamily a⟩
  invFun g :=
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly g
  left_inv :=
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly_components
  right_inv := by
    intro g
    apply Subtype.ext
    exact V.finiteAdelicSpecialOrthogonalHeightOneComponents_assembly g
  map_mul' := by
    intro a b
    apply Subtype.ext
    exact
      V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom.map_mul a b

@[simp]
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    (V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv a).1 =
      V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom a :=
  rfl

@[simp]
theorem finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_symm_apply
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv.symm g =
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly g :=
  rfl

end RationalQuadraticSpaceMatrix
