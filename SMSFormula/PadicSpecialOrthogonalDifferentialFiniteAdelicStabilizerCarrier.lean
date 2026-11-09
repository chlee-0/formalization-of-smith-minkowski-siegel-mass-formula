import SMSFormula.PadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
import SMSFormula.AdelicProperFinitePresentation

/-!
# Differential local stabilizer product and the finite-adelic stabilizer

This module identifies the dependent product of the literal corrected local
special-orthogonal stabilizers with the integral special-orthogonal
stabilizer inside the concrete finite adeles.  The identification is built
from the actual local integral matrices and the restricted-product structure
map.

No measure normalization or comparison with reference Haar occurs here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix RestrictedProduct

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicCarrierPrimeFact
    (q : {p : ℕ // Nat.Prime p}) : Fact (Nat.Prime q.1) :=
  ⟨q.2⟩

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicCarrierHeightOnePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicCarrierMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicCarrierBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  ⟨rfl⟩

/-- The canonical ring equivalence from a height-one completion integer ring
to the corresponding p-adic integer ring. -/
noncomputable def heightOneAdicCompletionIntegersEquivPadicInt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    v.adicCompletionIntegers ℚ ≃+*
      ℤ_[Rat.HeightOneSpectrum.primesEquiv v] := by
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  exact
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv

/-- Read a corrected local stabilizer family as integral general-linear
matrices indexed by height-one primes of `ℤ`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    GL (Fin n) (v.adicCompletionIntegers ℚ) := by
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
      q.1 (g q)
  let A : GL (Fin n) ℤ_[q.1] :=
    L.localPadicLatticeStabilizerIntegralGL q.1 h.1
  exact
    (Units.mapEquiv
      (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix.toMulEquiv).symm
      A

/-- Mapping the height-one integral matrix back to p-adic integers recovers
the integral matrix attached to the original corrected local stabilizer. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_map
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let q : {p : ℕ // Nat.Prime p} :=
      Rat.HeightOneSpectrum.primesEquiv v
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
        g v).1.map
        (heightOneAdicCompletionIntegersEquivPadicInt v) =
      (L.localPadicLatticeStabilizerIntegralGL q.1
        (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
          q.1 (g q)).1).1 := by
  dsimp only
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
      q.1 (g q)
  let A : GL (Fin n) ℤ_[q.1] :=
    L.localPadicLatticeStabilizerIntegralGL q.1 h.1
  change
    (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix
        ((Units.mapEquiv
          (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix.toMulEquiv).symm
          A).1 =
      A.1
  exact congrArg Units.val
    ((Units.mapEquiv
      (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix.toMulEquiv).apply_symm_apply
      A)

/-- After passage to the completion fields, the height-one integral matrix is
the original corrected local stabilizer matrix. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_fieldComponent
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let q : {p : ℕ // Nat.Prime p} :=
      Rat.HeightOneSpectrum.primesEquiv v
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
          g v)
    Matrix.GeneralLinearGroup.map
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom
        Uv =
      (g q).1.1.1 := by
  dsimp only
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
      q.1 (g q)
  let A : GL (Fin n) ℤ_[q.1] :=
    L.localPadicLatticeStabilizerIntegralGL q.1 h.1
  apply Units.ext
  ext i j
  have hij := congr_fun (congr_fun
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_map
      g v) i) j
  exact congrArg Subtype.val hij

/-- The height-one integral matrix preserves the integral form after
extension to the completion field. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_preserves_form
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
          g v)
    Uv.1ᵀ * L.pairingMatrix.map
        (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
      L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) := by
  dsimp only
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
      q.1 (g q)
  let A : GL (Fin n) ℤ_[q.1] :=
    L.localPadicLatticeStabilizerIntegralGL q.1 h.1
  have hAform :
      A.1ᵀ * L.pairingMatrix_padic q.1 * A.1 =
        L.pairingMatrix_padic q.1 :=
    L.localPadicLatticeStabilizerIntegralGL_preserves_form q.1 h.1
  let ev :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hUv :
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
            g v)).1.map ev.toRingEquiv.toRingHom =
        A.1.map PadicInt.Coe.ringHom := by
    have hcomponent :=
      L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_fieldComponent
        g v
    have hdirect :
        (g q).1.1.1.1 =
          A.1.map PadicInt.Coe.ringHom := by
      ext i j
      exact
        (L.localPadicLatticeStabilizerIntegralGL_apply
          q.1 h.1 i j).symm
    exact (congrArg Units.val hcomponent).trans hdirect
  have hFmap :
      (L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom =
        (L.pairingMatrix_padic q.1).map PadicInt.Coe.ringHom := by
    ext i j
    simp [pairingMatrix_padic, q, ev]
  apply Matrix.map_injective
    (f := ev.toRingEquiv.toRingHom) ev.injective
  change
    ((Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
            g v)).1ᵀ *
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) *
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
            g v)).1).map ev.toRingEquiv.toRingHom =
      (L.pairingMatrix.map
        (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom
  rw [
    Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hUv, hFmap]
  have hmap := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℤ_[q.1] =>
      M.map PadicInt.Coe.ringHom) hAform
  simpa only [Matrix.map_mul, Matrix.transpose_map] using hmap

/-- The height-one completion-field matrix has determinant one. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_det
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
          g v)
    Uv.1.det = 1 := by
  dsimp only
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let ev :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply ev.injective
  change
    ev.toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
            g v)).1.det =
      ev.toRingEquiv.toRingHom 1
  rw [map_one, RingHom.map_det]
  have hcomponent :=
    L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_fieldComponent
      g v
  have hcomponentVal := congrArg Units.val hcomponent
  have hcomponentMatrix :
      ev.toRingEquiv.toRingHom.mapMatrix
          (Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype
            (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL
              g v)).1 =
        (g q).1.1.1.1 := by
    exact hcomponentVal
  rw [hcomponentMatrix]
  exact
    (mem_specialFormPreservingMatrixSubgroup_iff
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))
      (g q).1.1).mp (g q).1.2

/-- Assemble a corrected local stabilizer family into the integral
finite-adelic special stabilizer. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct →
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
  intro g
  let U :=
    L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL g
  let Uf : GL (Fin n) RationalFiniteAdele :=
    localIntegralMatrixUnitsFiniteAdeleGL U
  have hform :
      Uf.1ᵀ * L.finiteAdelicFormMatrix * Uf.1 =
        L.finiteAdelicFormMatrix := by
    simpa [Uf, U, finiteAdelicFormMatrix] using
      (localIntegralMatrixUnitsFiniteAdeleGL_form_eq
        U L.pairingMatrix L.pairingMatrix
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_preserves_form
          g))
  let go : L.ConcreteFiniteAdelicOrthogonalGroup :=
    ⟨Uf, hform⟩
  have hdet : Uf.1.det = 1 := by
    ext v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    change ev Uf.1.det = ev 1
    rw [map_one, RingHom.map_det]
    have hmap := localIntegralMatrixUnitsFiniteAdeleGL_map_eval U v
    have hmapVal := congrArg Units.val hmap
    have hmapMatrix :
        Uf.1.map ev =
          (Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype (U v)).1 := by
      exact hmapVal
    change (Uf.1.map ev).det = 1
    rw [hmapMatrix]
    exact
      L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_det
        g v
  let gs : L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
    ⟨go,
      (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff go).mpr hdet⟩
  exact
    ⟨gs,
      localIntegralMatrixUnitsFiniteAdeleGL_mem_matrixUnitsOverSubring U⟩

/-- Evaluating the assembled finite-adelic stabilizer at a height-one place
and then identifying its completion with `ℚ_p` recovers the original local
corrected stabilizer matrix. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer_component
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let q : {p : ℕ // Nat.Prime p} :=
      Rat.HeightOneSpectrum.primesEquiv v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    Matrix.GeneralLinearGroup.map
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.map ev
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer
            g).1.1.1) =
      (g q).1.1.1 := by
  dsimp only
  let U :=
    L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL g
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  have hmap := localIntegralMatrixUnitsFiniteAdeleGL_map_eval U v
  rw [show
    Matrix.GeneralLinearGroup.map ev
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer
          g).1.1.1 =
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype (U v) by
          exact hmap]
  exact
    L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneIntegralGL_fieldComponent
      g v

/-- Evaluate an integral finite-adelic special stabilizer at a height-one
prime and express the result in the corresponding standard p-adic field. -/
noncomputable def
    finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  let e :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let φ : RationalFiniteAdele →+* ℚ_[q.1] :=
    e.toRingEquiv.toRingHom.comp ev
  let U : GL (Fin n) ℚ_[q.1] :=
    Matrix.GeneralLinearGroup.map φ a.1.1.1
  have hform :
      U.1ᵀ * L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) * U.1 =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) := by
    have hmap := congrArg
      (fun M : Matrix (Fin n) (Fin n) RationalFiniteAdele =>
        M.map φ) a.1.1.2
    change
      (a.1.1.1.1ᵀ * L.finiteAdelicFormMatrix * a.1.1.1.1).map φ =
        L.finiteAdelicFormMatrix.map φ at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    have hF :
        L.finiteAdelicFormMatrix.map φ =
          L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) := by
      rw [L.finiteAdelicFormMatrix_eq_map_rationalFormMatrix]
      ext i j
      exact φ.toRatAlgHom.commutes (L.rationalFormMatrix i j)
    rw [hF] at hmap
    exact hmap
  let gf :
      formPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1])) :=
    ⟨U, hform⟩
  have hdet : U.1.det = 1 := by
    have ha :
        a.1.1.1.1.det = 1 :=
      (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff a.1.1).mp a.1.2
    change (a.1.1.1.1.map φ).det = 1
    calc
      (a.1.1.1.1.map φ).det = φ a.1.1.1.1.det :=
        (RingHom.map_det φ a.1.1.1.1).symm
      _ = 1 := by rw [ha, map_one]
  let gs :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1])) :=
    ⟨gf,
      (mem_specialFormPreservingMatrixSubgroup_iff
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1])) gf).mpr hdet⟩
  refine ⟨gs,
    (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
      q.1 gs).mpr ?_⟩
  have hint :=
    (L.mem_finiteLocalLatticeStabilizerSubgroup_iff_placewise a.1.1).mp a.2
  constructor
  · intro i j
    have hij := hint.1 i j v
    rw [mem_adicCompletionIntegers_iff_padic] at hij
    exact hij
  · intro i j
    have hij := hint.2 i j v
    rw [mem_adicCompletionIntegers_iff_padic] at hij
    exact hij

/-- The height-one component has the literal evaluated ambient matrix. -/
theorem
    finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
        a v).1.1.1 =
      Matrix.GeneralLinearGroup.map
        ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
          ev) a.1.1.1 := by
  rfl

/-- The same dependent product of local stabilizers, indexed by the
height-one primes used by the finite adeles. -/
abbrev
    localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct
    (L : PositiveDefiniteIntegralLattice n) :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1

/-- Canonically reindex the all-rational-prime product by height-one primes
of `ℤ`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct ≃
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct :=
  (Equiv.piCongrLeft
    (fun q : {p : ℕ // Nat.Prime p} =>
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup q.1)
    Rat.HeightOneSpectrum.primesEquiv).symm

/-- Height-one evaluation of an assembled all-prime family recovers its
component at the corresponding rational prime. -/
theorem
    finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_toFiniteAdelic_units
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer
          g) v).1.1.1 =
      (g (Rat.HeightOneSpectrum.primesEquiv v)).1.1.1 := by
  calc
    (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer
            g) v).1.1.1 =
        Matrix.GeneralLinearGroup.map
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
            (RestrictedProduct.evalRingHom
              (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
                w.adicCompletion ℚ) v))
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer
            g).1.1.1 :=
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
        _ v
    _ = (g (Rat.HeightOneSpectrum.primesEquiv v)).1.1.1 :=
      L.localPadicSpecialOrthogonalDifferentialAllPrimeToFiniteAdelicStabilizer_component
        g v

/-- Integral height-one matrix attached directly to a height-one-indexed
family, without dependent reindexing. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    GL (Fin n) (v.adicCompletionIntegers ℚ) := by
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
      q.1 (g v)
  let A : GL (Fin n) ℤ_[q.1] :=
    L.localPadicLatticeStabilizerIntegralGL q.1 h.1
  exact
    (Units.mapEquiv
      (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix.toMulEquiv).symm
      A

/-- The direct height-one integral matrix recovers the local p-adic matrix
after passage to the completion field. -/
theorem
    localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_fieldComponent
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL g v)
    Matrix.GeneralLinearGroup.map
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom
        Uv =
      (g v).1.1.1 := by
  dsimp only
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
      q.1 (g v)
  let A : GL (Fin n) ℤ_[q.1] :=
    L.localPadicLatticeStabilizerIntegralGL q.1 h.1
  apply Units.ext
  ext i j
  have hmap :
      (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix
          ((L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
            g v).1) =
        A.1 := by
    change
      (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix
          (((Units.mapEquiv
            (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix.toMulEquiv).symm
            A).1) =
        A.1
    exact congrArg Units.val
      ((Units.mapEquiv
        (heightOneAdicCompletionIntegersEquivPadicInt v).mapMatrix.toMulEquiv).apply_symm_apply
        A)
  have hij := congr_fun (congr_fun hmap i) j
  exact congrArg Subtype.val hij

/-- The direct height-one integral matrix preserves the integral form after
extension to the completion field. -/
theorem
    localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_preserves_form
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL g v)
    Uv.1ᵀ * L.pairingMatrix.map
        (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
      L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) := by
  dsimp only
  let q : {p : ℕ // Nat.Prime p} :=
    Rat.HeightOneSpectrum.primesEquiv v
  let ev :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply Matrix.map_injective
    (f := ev.toRingEquiv.toRingHom) ev.injective
  change
    ((Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
            g v)).1ᵀ *
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) *
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
            g v)).1).map ev.toRingEquiv.toRingHom =
      (L.pairingMatrix.map
        (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hcomponent :=
    congrArg Units.val
      (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_fieldComponent
        g v)
  have hcomponentMatrix :
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
            g v)).1.map ev.toRingEquiv.toRingHom =
        (g v).1.1.1.1 := by
    exact hcomponent
  have hF :
      (L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) := by
    ext i j
    simp [rationalFormMatrix, q, ev]
  rw [hcomponentMatrix, hF]
  exact (g v).1.1.2

/-- The direct height-one completion-field matrix has determinant one. -/
theorem
    localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_det
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL g v)
    Uv.1.det = 1 := by
  dsimp only
  let ev :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply ev.injective
  change
    ev.toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
            g v)).1.det =
      ev.toRingEquiv.toRingHom 1
  rw [map_one, RingHom.map_det]
  have hcomponent :=
    congrArg Units.val
      (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_fieldComponent
        g v)
  have hcomponentMatrix :
      ev.toRingEquiv.toRingHom.mapMatrix
          (Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype
            (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL
              g v)).1 =
        (g v).1.1.1.1 := by
    exact hcomponent
  rw [hcomponentMatrix]
  exact
    (mem_specialFormPreservingMatrixSubgroup_iff
      (L.rationalFormMatrix.map
        (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
      (g v).1.1).mp (g v).1.2

/-- Assemble a height-one-indexed local stabilizer family directly into the
integral finite-adelic special stabilizer. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct →
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
  intro g
  let U :=
    L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL g
  let Uf : GL (Fin n) RationalFiniteAdele :=
    localIntegralMatrixUnitsFiniteAdeleGL U
  have hform :
      Uf.1ᵀ * L.finiteAdelicFormMatrix * Uf.1 =
        L.finiteAdelicFormMatrix := by
    simpa [Uf, U, finiteAdelicFormMatrix] using
      (localIntegralMatrixUnitsFiniteAdeleGL_form_eq
        U L.pairingMatrix L.pairingMatrix
        (L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_preserves_form
          g))
  let go : L.ConcreteFiniteAdelicOrthogonalGroup :=
    ⟨Uf, hform⟩
  have hdet : Uf.1.det = 1 := by
    ext v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    change ev Uf.1.det = ev 1
    rw [map_one, RingHom.map_det]
    have hmap := localIntegralMatrixUnitsFiniteAdeleGL_map_eval U v
    have hmapVal := congrArg Units.val hmap
    have hmapMatrix :
        Uf.1.map ev =
          (Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype (U v)).1 := by
      exact hmapVal
    change (Uf.1.map ev).det = 1
    rw [hmapMatrix]
    exact
      L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_det
        g v
  let gs : L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
    ⟨go,
      (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff go).mpr hdet⟩
  exact
    ⟨gs,
      localIntegralMatrixUnitsFiniteAdeleGL_mem_matrixUnitsOverSubring U⟩

/-- The direct height-one assembly has the prescribed local p-adic
component. -/
theorem
    localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer_component
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    Matrix.GeneralLinearGroup.map
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.map ev
          (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
            g).1.1.1) =
      (g v).1.1.1 := by
  dsimp only
  let U :=
    L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL g
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  have hmap := localIntegralMatrixUnitsFiniteAdeleGL_map_eval U v
  rw [show
    Matrix.GeneralLinearGroup.map ev
        (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
          g).1.1.1 =
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype (U v) by
          exact hmap]
  exact
    L.localPadicSpecialOrthogonalDifferentialHeightOneIntegralGL_fieldComponent
      g v

/-- Evaluation of direct height-one assembly recovers the local family. -/
theorem
    finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_leftInverse
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct) :
    (fun v =>
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
        (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
          g) v) = g := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  calc
    (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
        (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
          g) v).1.1.1 =
        Matrix.GeneralLinearGroup.map
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
            (RestrictedProduct.evalRingHom
              (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
                w.adicCompletion ℚ) v))
          (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
            g).1.1.1 :=
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
        _ v
    _ = (g v).1.1.1 :=
      L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer_component
        g v

/-- Direct height-one assembly is a left inverse to height-one evaluation on
the finite-adelic stabilizer. -/
theorem
    localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer_rightInverse
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
        (fun v =>
          L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
            a v) = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j v
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  let e :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply e.injective
  have hforward :=
    L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer_component
      (fun w =>
        L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          a w) v
  have hlocal :=
    L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
      a v
  have hcomponent :
      Matrix.GeneralLinearGroup.map e.toRingEquiv.toRingHom
          (Matrix.GeneralLinearGroup.map ev
            (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
              (fun w =>
                L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
                  a w)).1.1.1) =
        Matrix.GeneralLinearGroup.map
          (e.toRingEquiv.toRingHom.comp ev) a.1.1.1 :=
    hforward.trans hlocal
  have hmatrix := congrArg Units.val hcomponent
  have hij := congr_fun (congr_fun hmatrix i) j
  exact hij

/-- Algebraic carrier equivalence on the height-one indexing used by finite
adeles. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct ≃
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup where
  toFun :=
    L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
  invFun := fun a v =>
    L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent a v
  left_inv :=
    L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_leftInverse
  right_inv :=
    L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer_rightInverse

/-- Height-one evaluation is multiplicative. -/
theorem
    finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_mul
    (L : PositiveDefiniteIntegralLattice n)
    (a b : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    (fun v =>
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
        (a * b) v) =
      (fun v =>
        L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          a v) *
      (fun v =>
        L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          b v) := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  let e :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  calc
    (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
        (a * b) v).1.1.1 =
        Matrix.GeneralLinearGroup.map (e.toRingEquiv.toRingHom.comp ev)
          (a * b).1.1.1 :=
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
        (a * b) v
    _ =
        Matrix.GeneralLinearGroup.map (e.toRingEquiv.toRingHom.comp ev)
            a.1.1.1 *
          Matrix.GeneralLinearGroup.map (e.toRingEquiv.toRingHom.comp ev)
            b.1.1.1 :=
      Matrix.GeneralLinearGroup.map_mul
        (e.toRingEquiv.toRingHom.comp ev) a.1.1.1 b.1.1.1
    _ =
        (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
            a v).1.1.1 *
          (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
            b v).1.1.1 := congrArg₂ (· * ·)
      (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
        a v).symm
      (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
        b v).symm

/-- The height-one carrier equivalence is multiplicative. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct ≃*
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup where
  toEquiv :=
    L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicEquiv
  map_mul' g h := by
    apply
      (L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicEquiv).symm.injective
    change
      (fun v =>
        L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
            (g * h)) v) =
      (fun v =>
        L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          (L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
              g *
            L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer
              h) v)
    rw [
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_mul,
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_leftInverse,
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_leftInverse,
      L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_leftInverse]

/-- The rational-prime and height-one indexed products are multiplicatively
equivalent by reindexing. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct ≃*
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct where
  toEquiv :=
    L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneEquiv
  map_mul' g h := by
    funext v
    rfl

/-- Canonical multiplicative equivalence from the literal all-prime product
of corrected local integral stabilizers to the concrete finite-adelic special
stabilizer. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct ≃*
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneMulEquiv).trans
    L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicMulEquiv

/-- Ambient matrix component formula for the canonical all-prime
finite-adelic carrier equivalence. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv_component
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v
    Matrix.GeneralLinearGroup.map
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.map ev
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv
            g).1.1.1) =
      (g (Rat.HeightOneSpectrum.primesEquiv v)).1.1.1 := by
  dsimp only
  calc
    Matrix.GeneralLinearGroup.map
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom
        (Matrix.GeneralLinearGroup.map
          (RestrictedProduct.evalRingHom
            (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
              w.adicCompletion ℚ) v)
          (L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv
            g).1.1.1) =
        ((L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneEquiv
          g) v).1.1.1 :=
      L.localPadicSpecialOrthogonalDifferentialHeightOneToFiniteAdelicStabilizer_component
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneEquiv g) v
    _ = (g (Rat.HeightOneSpectrum.primesEquiv v)).1.1.1 := congrArg
      (fun z => z.1.1.1)
      (Equiv.piCongrLeft_symm_apply
        (fun q : {p : ℕ // Nat.Prime p} =>
          L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup q.1)
        Rat.HeightOneSpectrum.primesEquiv g v)

/-- The finite-adelic equivalence followed by its inverse is literally the
identity on the all-prime local stabilizer product. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv_symm_apply_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct) :
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv).symm
        (L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv
          g) = g :=
  (L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv).symm_apply_apply
    g

/-- The inverse finite-adelic equivalence followed by assembly is literally
the identity on the concrete finite-adelic stabilizer. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv_apply_symm_apply
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv
        ((L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv).symm
          a) = a :=
  (L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv).apply_symm_apply
    a

/-- Evaluation at one height-one place is continuous on the concrete
finite-adelic stabilizer. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
    (L : PositiveDefiniteIntegralLattice n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous
      (fun a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
        L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
          a v) := by
  apply Continuous.subtype_mk
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
  have hcontinuous : Continuous
      (fun a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
      Matrix.GeneralLinearGroup.map
        φ a.1.1.1) := by
    have hev : Continuous (ev : RationalFiniteAdele → v.adicCompletion ℚ) := by
      change Continuous (fun x : RationalFiniteAdele => x v)
      exact RestrictedProduct.continuous_eval v
    have hφ : Continuous φ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous.comp hev
    have hmatrix : Continuous
        (φ.mapMatrix :
          Matrix (Fin n) (Fin n) RationalFiniteAdele →
            Matrix (Fin n) (Fin n)
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
      apply continuous_pi
      intro (i : Fin n)
      apply continuous_pi
      intro (j : Fin n)
      exact hφ.comp ((continuous_apply j).comp (continuous_apply i))
    let fm :
        Matrix (Fin n) (Fin n) RationalFiniteAdele →*
          Matrix (Fin n) (Fin n)
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
      φ.mapMatrix.toMonoidHom
    have hfm : Continuous fm := hmatrix
    have hunits :
        Continuous
          (Units.map fm) :=
      hfm.units_map fm
    exact hunits.comp (by fun_prop)
  apply hcontinuous.congr
  intro a
  exact
    (L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent_units
      a v).symm

/-- Simultaneous height-one evaluation is continuous. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponents
    (L : PositiveDefiniteIntegralLattice n) :
    Continuous
      (fun a : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
        (fun v =>
          L.finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
            a v)) :=
  continuous_pi fun v =>
    L.continuous_finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponent
      v

/-- The algebraic height-one carrier equivalence is a homeomorphism.  Its
inverse is continuous by literal finite-adele evaluation; compactness of the
finite-adelic stabilizer supplies continuity of assembly. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicHomeomorph
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct ≃ₜ
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
  let e :=
    (L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicEquiv).symm
  letI : CompactSpace
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
    isCompact_iff_compactSpace.mp
      L.isCompact_finiteSpecialOrthogonalLatticeStabilizerSubgroup
  let h :
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ≃ₜ
        L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct :=
    e.toHomeomorphOfContinuousClosed
      L.continuous_finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponents
      L.continuous_finiteAdelicSpecialOrthogonalLatticeStabilizerHeightOneComponents.isClosedMap
  exact h.symm

/-- The height-one carrier identification is continuously
multiplicative. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicContinuousMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct ≃ₜ*
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  ContinuousMulEquiv.mk'
    L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicHomeomorph
    L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicMulEquiv.map_mul

/-- Reindexing rational primes by height-one primes is a homeomorphism. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneHomeomorph
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct ≃ₜ
      L.localPadicSpecialOrthogonalDifferentialHeightOneStabilizerProduct :=
  (Homeomorph.piCongrLeft
    (Y := fun q : {p : ℕ // Nat.Prime p} =>
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup q.1)
    Rat.HeightOneSpectrum.primesEquiv).symm

/-- Canonical homeomorphism between the literal all-prime local stabilizer
product and the concrete finite-adelic stabilizer. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerHomeomorph
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct ≃ₜ
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  L.localPadicSpecialOrthogonalDifferentialAllPrimeHeightOneHomeomorph.trans
    L.localPadicSpecialOrthogonalDifferentialHeightOneFiniteAdelicHomeomorph

/-- Canonical continuous multiplicative equivalence between the literal
all-prime product of corrected local integral stabilizers and the concrete
finite-adelic special stabilizer. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerContinuousMulEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct ≃ₜ*
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  ContinuousMulEquiv.mk'
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerHomeomorph
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerMulEquiv.map_mul

end PositiveDefiniteIntegralLattice
