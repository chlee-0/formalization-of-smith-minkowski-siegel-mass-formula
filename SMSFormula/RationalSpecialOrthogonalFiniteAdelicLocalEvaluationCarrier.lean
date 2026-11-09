import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier

/-!
# General finite-adelic special-orthogonal local evaluation

This module evaluates the finite-adelic special-orthogonal group of an
arbitrary rational quadratic-space matrix at every height-one prime of
`ℤ`.  Evaluation is bundled as a continuous multiplicative homomorphism into
the corresponding p-adic special-orthogonal group.  Simultaneous evaluation
is injective and its image satisfies the literal almost-everywhere integral
matrix-and-inverse condition inherited from the restricted-product
definition of the finite adeles.

No measure or reverse restricted-family assembly is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicLocalEvaluationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The p-adic special-orthogonal carrier indexed by a height-one prime of
`ℤ`. -/
abbrev HeightOnePadicSpecialOrthogonalGroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  specialFormPreservingMatrixSubgroup
    (V.pairingMatrix.map
      (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))

/-- Evaluate a finite-adelic special-orthogonal matrix at a height-one prime
and identify that completion with the corresponding standard p-adic field. -/
def finiteAdelicSpecialOrthogonalHeightOneComponent
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicSpecialOrthogonalGroup v := by
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let φ : RationalFiniteAdele →+* ℚ_[q.1] :=
    e.toRingEquiv.toRingHom.comp ev
  let U : GL (Fin n) ℚ_[q.1] :=
    Matrix.GeneralLinearGroup.map φ a.1.1
  have hform :
      U.1ᵀ * V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1]) * U.1 =
        V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1]) := by
    have hmap := congrArg
      (fun M : Matrix (Fin n) (Fin n) RationalFiniteAdele =>
        M.map φ) a.1.2
    change
      (a.1.1.1ᵀ * V.finiteAdelicFormMatrix * a.1.1.1).map φ =
        V.finiteAdelicFormMatrix.map φ at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    have hF :
        V.finiteAdelicFormMatrix.map φ =
          V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1]) := by
      ext i j
      exact φ.toRatAlgHom.commutes (V.pairingMatrix i j)
    rw [hF] at hmap
    exact hmap
  let gf :
      formPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1])) :=
    ⟨U, hform⟩
  have hdet : U.1.det = 1 := by
    have ha : a.1.1.1.det = 1 :=
      (V.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff a.1).mp a.2
    change (a.1.1.1.map φ).det = 1
    calc
      (a.1.1.1.map φ).det = φ a.1.1.1.det :=
        (RingHom.map_det φ a.1.1.1).symm
      _ = 1 := by rw [ha, map_one]
  exact
    ⟨gf,
      (mem_specialFormPreservingMatrixSubgroup_iff
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1])) gf).2 hdet⟩

/-- The height-one component has the literal evaluated ambient matrix. -/
theorem finiteAdelicSpecialOrthogonalHeightOneComponent_matrix
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    (V.finiteAdelicSpecialOrthogonalHeightOneComponent a v).1.1.1 =
      Matrix.GeneralLinearGroup.map
        ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
          ev) a.1.1 := by
  rfl

/-- Height-one evaluation is multiplicative. -/
theorem finiteAdelicSpecialOrthogonalHeightOneComponent_mul
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (a b : V.FiniteAdelicSpecialOrthogonalGroup) :
    V.finiteAdelicSpecialOrthogonalHeightOneComponent (a * b) v =
      V.finiteAdelicSpecialOrthogonalHeightOneComponent a v *
        V.finiteAdelicSpecialOrthogonalHeightOneComponent b v := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  let φ : RationalFiniteAdele →+*
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
      (RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v)
  calc
    (V.finiteAdelicSpecialOrthogonalHeightOneComponent (a * b) v).1.1.1 =
        (Matrix.GeneralLinearGroup.map φ (a * b).1.1).1 :=
      V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix (a * b) v
    _ =
        (Matrix.GeneralLinearGroup.map φ a.1.1).1 *
          (Matrix.GeneralLinearGroup.map φ b.1.1).1 :=
      congrArg Units.val
        (Matrix.GeneralLinearGroup.map_mul φ a.1.1 b.1.1)
    _ =
        (V.finiteAdelicSpecialOrthogonalHeightOneComponent a v).1.1.1 *
          (V.finiteAdelicSpecialOrthogonalHeightOneComponent b v).1.1.1 :=
      congrArg₂ (· * ·)
        (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix a v).symm
        (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix b v).symm
    _ = _ := rfl

/-- Evaluation at one height-one place as a multiplicative homomorphism. -/
def finiteAdelicSpecialOrthogonalHeightOneComponentHom
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.FiniteAdelicSpecialOrthogonalGroup →*
      V.HeightOnePadicSpecialOrthogonalGroup v where
  toFun a := V.finiteAdelicSpecialOrthogonalHeightOneComponent a v
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    let φ : RationalFiniteAdele →+*
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
        (RestrictedProduct.evalRingHom
          (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
            w.adicCompletion ℚ) v)
    calc
      (V.finiteAdelicSpecialOrthogonalHeightOneComponent 1 v).1.1.1 =
          (Matrix.GeneralLinearGroup.map φ
            (1 : V.FiniteAdelicSpecialOrthogonalGroup).1.1).1 :=
        V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix 1 v
      _ = (1 : GL (Fin n)
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).1 :=
        congrArg Units.val (Matrix.GeneralLinearGroup.map_one φ)
      _ = _ := rfl
  map_mul' := V.finiteAdelicSpecialOrthogonalHeightOneComponent_mul v

/-- Evaluation at one height-one place is continuous. -/
theorem continuous_finiteAdelicSpecialOrthogonalHeightOneComponent
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  let φ : RationalFiniteAdele →+*
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
      ev
  have hev : Continuous (ev : RationalFiniteAdele → v.adicCompletion ℚ) := by
    change Continuous (fun x : RationalFiniteAdele => x v)
    exact RestrictedProduct.continuous_eval v
  have hφ : Continuous φ :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous.comp hev
  have hmatrix :
      Continuous
        (φ.mapMatrix :
          Matrix (Fin n) (Fin n) RationalFiniteAdele →
            Matrix (Fin n) (Fin n)
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact hφ.comp ((continuous_apply j).comp (continuous_apply i))
  let fm :
      Matrix (Fin n) (Fin n) RationalFiniteAdele →*
        Matrix (Fin n) (Fin n)
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    φ.mapMatrix.toMonoidHom
  have hfm : Continuous fm := hmatrix
  have hunits : Continuous (Units.map fm) :=
    hfm.units_map fm
  refine (hunits.comp
    (continuous_subtype_val.comp continuous_subtype_val)).congr ?_
  intro a
  apply Units.ext
  exact (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix a v).symm

/-! ## Simultaneous evaluation -/

/-- The dependent family of all p-adic special-orthogonal groups, indexed in
the height-one convention of the rational finite adeles. -/
abbrev HeightOnePadicSpecialOrthogonalGroupProduct
    (V : RationalQuadraticSpaceMatrix n) :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    V.HeightOnePadicSpecialOrthogonalGroup v

/-- Simultaneous height-one evaluation as a multiplicative homomorphism. -/
def finiteAdelicSpecialOrthogonalHeightOneComponentsHom
    (V : RationalQuadraticSpaceMatrix n) :
    V.FiniteAdelicSpecialOrthogonalGroup →*
      V.HeightOnePadicSpecialOrthogonalGroupProduct where
  toFun a v := V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a
  map_one' := by
    funext v
    exact (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v).map_one
  map_mul' a b := by
    funext v
    exact (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v).map_mul a b

/-- Simultaneous evaluation is continuous. -/
theorem continuous_finiteAdelicSpecialOrthogonalHeightOneComponents
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom :=
  continuous_pi fun v => by
    change Continuous
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v)
    exact V.continuous_finiteAdelicSpecialOrthogonalHeightOneComponent v

/-- A finite-adelic special-orthogonal matrix is determined by all of its
height-one p-adic components. -/
theorem finiteAdelicSpecialOrthogonalHeightOneComponentsHom_injective
    (V : RationalQuadraticSpaceMatrix n) :
    Function.Injective
      V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply e.injective
  have hv := congrFun hab v
  have hij := congrArg (fun z => z.1.1.1 i j) hv
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  have ha :=
    congr_fun (congr_fun
      (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix a v)
      i) j
  have hb :=
    congr_fun (congr_fun
      (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix b v)
      i) j
  exact ha.symm.trans (hij.trans hb)

/-! ## The actual restricted-family image condition -/

/-- A local p-adic special-orthogonal matrix is integral at the height-one
place when both it and its inverse have integral entries after transport back
to the completion field used by the finite adeles. -/
def HeightOnePadicSpecialOrthogonalIsIntegral
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicSpecialOrthogonalGroup v) : Prop :=
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  (∀ i j, e.symm (g.1.1.1 i j) ∈ v.adicCompletionIntegers ℚ) ∧
    (∀ i j, e.symm ((g.1.1⁻¹).1 i j) ∈
      v.adicCompletionIntegers ℚ)

/-- The precise restricted-family predicate: matrix and inverse entries are
integral at all but finitely many height-one places. -/
def IsFiniteAdelicSpecialOrthogonalRestrictedFamily
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.HeightOnePadicSpecialOrthogonalGroupProduct) : Prop :=
  ∀ᶠ v in Filter.cofinite,
    V.HeightOnePadicSpecialOrthogonalIsIntegral v (g v)

/-- Simultaneous evaluation of a finite-adelic special-orthogonal matrix
satisfies the actual almost-everywhere matrix-and-inverse integrality
condition. -/
theorem finiteAdelicSpecialOrthogonalHeightOneComponents_isRestrictedFamily
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom a) := by
  have hval :
      ∀ᶠ v in Filter.cofinite,
        ∀ i j, a.1.1.1 i j v ∈ v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (a.1.1.1 i j).2
  have hinv :
      ∀ᶠ v in Filter.cofinite,
        ∀ i j, (a.1.1⁻¹).1 i j v ∈ v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact ((a.1.1⁻¹).1 i j).2
  filter_upwards [hval, hinv] with v hv hvi
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro i j
    have hmatrix :=
      congr_fun (congr_fun
        (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix a v)
        i) j
    change
      e.symm
          ((V.finiteAdelicSpecialOrthogonalHeightOneComponent a v).1.1.1 i j) ∈
        v.adicCompletionIntegers ℚ
    rw [hmatrix]
    change e.symm (e (a.1.1.1 i j v)) ∈ v.adicCompletionIntegers ℚ
    simpa using hv i j
  · intro i j
    have hmapinv :=
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v).map_inv a
    change
      e.symm
          (((V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1⁻¹).1
            i j) ∈
        v.adicCompletionIntegers ℚ
    rw [← show
      (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v (a⁻¹)).1.1 =
          (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a).1.1⁻¹ by
        exact congrArg (fun z => z.1.1) hmapinv]
    change
      e.symm
          ((V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (a⁻¹) v).1.1.1 i j) ∈
        v.adicCompletionIntegers ℚ
    have hmatrix :=
      congr_fun (congr_fun
        (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix
          (a⁻¹) v) i) j
    rw [hmatrix]
    change e.symm (e ((a.1.1⁻¹).1 i j v)) ∈
      v.adicCompletionIntegers ℚ
    simpa using hvi i j

end RationalQuadraticSpaceMatrix
