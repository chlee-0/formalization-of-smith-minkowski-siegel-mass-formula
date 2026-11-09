import SMSFormula.AdelicDoubleCosets
import SMSFormula.Mass
import SMSFormula.HasseMinkowskiSource
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Adelic finite-adelic orthogonal presentation

This module contains the abstract finite-adelic orthogonal group presentation
used by the Schulze--Pillot bridge, together with its basic double-coset,
selected-piece, stabilizer, measurable-space, and compact-slice presentation
helpers before quotient-piece Weil packages are introduced.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u
universe v
universe w

variable {n : ℕ}

open MeasureTheory
open TopologicalSpace
open scoped ENNReal Matrix RestrictedProduct Uniformity

/-! ## Concrete finite-adelic orthogonal group -/

/-- The subgroup of invertible matrices preserving a fixed bilinear-form
matrix. -/
def formPreservingMatrixSubgroup {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) :
    Subgroup (Matrix (Fin n) (Fin n) R)ˣ where
  carrier := {g | g.1ᵀ * F * g.1 = F}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul]
    calc
      (h.1ᵀ * g.1ᵀ) * F * (g.1 * h.1) =
          h.1ᵀ * (g.1ᵀ * F * g.1) * h.1 := by
            simp only [Matrix.mul_assoc]
      _ = F := by rw [hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq]
    calc
      (g⁻¹).1ᵀ * F * (g⁻¹).1 =
          (g⁻¹).1ᵀ * (g.1ᵀ * F * g.1) * (g⁻¹).1 := by
            rw [hg]
      _ = F := by
        have hval : g.1 * (g⁻¹).1 = 1 := by
          change (g * g⁻¹).1 = 1
          simp
        calc
          (g⁻¹).1ᵀ * (g.1ᵀ * F * g.1) * (g⁻¹).1 =
              (g.1 * (g⁻¹).1)ᵀ * F * (g.1 * (g⁻¹).1) := by
                simp only [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = F := by rw [hval]; simp

@[simp]
theorem mem_formPreservingMatrixSubgroup_iff {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R)
    (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    g ∈ formPreservingMatrixSubgroup F ↔ g.1ᵀ * F * g.1 = F :=
  Iff.rfl

/-- The finite adele ring of `ℚ`, presented using the Dedekind domain `ℤ`. -/
abbrev RationalFiniteAdele :=
  IsDedekindDomain.FiniteAdeleRing ℤ ℚ

noncomputable instance heightOneSpectrumIntCountable :
    Countable (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Countable.of_equiv Nat.Primes Rat.HeightOneSpectrum.primesEquiv.symm

local instance (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    T2Space (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.symm.t2Space

noncomputable instance rationalAdicCompletionSecondCountableTopology
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding
    |>.secondCountableTopology

local instance : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

/-- The rational finite adeles are second countable.  The restricted product
is covered by the countable family of open principal blocks obtained by
allowing a finite set of nonintegral places. -/
noncomputable instance rationalFiniteAdeleSecondCountableTopology :
    SecondCountableTopology RationalFiniteAdele := by
  let ι := IsDedekindDomain.HeightOneSpectrum ℤ
  let R : ι → Type := fun v => v.adicCompletion ℚ
  let A : (v : ι) → Set (R v) := fun v => v.adicCompletionIntegers ℚ
  have hAopen : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  let S : Finset ι → Set ι := fun T => (T : Set ι)ᶜ
  have hS : ∀ T : Finset ι, Filter.cofinite ≤ Filter.principal (S T) := by
    intro T
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simp [S]
  let U : Finset ι → Set RationalFiniteAdele := fun T =>
    Set.range (RestrictedProduct.inclusion R A (hS T))
  letI (T : Finset ι) :
      SecondCountableTopology (Πʳ v, [R v, A v]_[Filter.principal (S T)]) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  letI (T : Finset ι) : SecondCountableTopology (U T) :=
    (RestrictedProduct.isEmbedding_inclusion_principal (R := R) (A := A)
      (hS T)).toHomeomorph.symm.isEmbedding.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · intro T
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal
      (R := R) (A := A) hAopen (hS T)).isOpen_range
  · apply Set.eq_univ_of_forall
    intro x
    have hfinite : {v : ι | x v ∉ A v}.Finite := by
      simpa only [Set.compl_setOf] using
        (show {v : ι | x v ∈ A v}ᶜ.Finite from Filter.mem_cofinite.mp x.2)
    let T : Finset ι := hfinite.toFinset
    apply Set.mem_iUnion.2
    refine ⟨T, ?_⟩
    change x ∈ Set.range (RestrictedProduct.inclusion R A (hS T))
    rw [RestrictedProduct.range_inclusion]
    change ∀ᶠ v in Filter.principal (S T), x v ∈ A v
    rw [Filter.eventually_principal]
    intro v hv
    by_contra hnot
    have hvT : v ∈ T := by simp [T, hnot]
    exact hv hvT

/-- The form matrix of `L`, transported from `ℤ` to the finite adeles of `ℚ`. -/
def finiteAdelicFormMatrix (L : PositiveDefiniteIntegralLattice n) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  L.pairingMatrix.map (algebraMap ℤ RationalFiniteAdele)

/-- The concrete finite-adelic orthogonal matrix group attached to `L`.

Its elements are invertible matrices over the finite adeles preserving the
transported form matrix.  This is the concrete ambient carrier underlying the
abstract `FiniteAdelicOrthogonalGroup` presentation below. -/
def finiteAdelicOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
  formPreservingMatrixSubgroup L.finiteAdelicFormMatrix

/-- The concrete carrier type for the finite-adelic orthogonal group of `L`. -/
abbrev ConcreteFiniteAdelicOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.finiteAdelicOrthogonalMatrixSubgroup

/-- The concrete finite-adelic orthogonal group is second countable. -/
noncomputable instance concreteFiniteAdelicOrthogonalGroupSecondCountableTopology
    (L : PositiveDefiniteIntegralLattice n) :
    SecondCountableTopology L.ConcreteFiniteAdelicOrthogonalGroup := by
  letI : SecondCountableTopology (Fin n → RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele ×
        (Matrix (Fin n) (Fin n) RationalFiniteAdele)ᵐᵒᵖ) :=
    inferInstance
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_induced
    L.ConcreteFiniteAdelicOrthogonalGroup
    (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ
    ((↑) : L.ConcreteFiniteAdelicOrthogonalGroup →
      (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ)

/-- The concrete finite-adelic orthogonal group carries its inherited Borel
measurable space. -/
instance concreteFiniteAdelicOrthogonalGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
  borel L.ConcreteFiniteAdelicOrthogonalGroup

instance concreteFiniteAdelicOrthogonalGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
  ⟨rfl⟩

@[simp]
theorem mem_finiteAdelicOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) :
    g ∈ L.finiteAdelicOrthogonalMatrixSubgroup ↔
      g.1ᵀ * L.finiteAdelicFormMatrix * g.1 = L.finiteAdelicFormMatrix :=
  Iff.rfl

/-- The finite-adelic orthogonal matrix group is closed in the ambient general
linear group. -/
theorem isClosed_finiteAdelicOrthogonalMatrixSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsClosed (L.finiteAdelicOrthogonalMatrixSubgroup :
      Set (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) := by
  letI : T1Space (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
    inferInstanceAs (T1Space (Fin n → Fin n → RationalFiniteAdele))
  change IsClosed
    {g : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ |
      g.1ᵀ * L.finiteAdelicFormMatrix * g.1 = L.finiteAdelicFormMatrix}
  have hcontinuous : Continuous
      (fun g : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ ↦
        g.1ᵀ * L.finiteAdelicFormMatrix * g.1) := by
    have hvalue : Continuous
        (fun g : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ ↦ g.1) :=
      Units.continuous_val
    exact (hvalue.matrix_transpose.mul continuous_const).mul hvalue
  change IsClosed ((fun g : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ ↦
    g.1ᵀ * L.finiteAdelicFormMatrix * g.1) ⁻¹' {L.finiteAdelicFormMatrix})
  exact isClosed_singleton.preimage hcontinuous

/-- The form matrix of `L`, transported from `ℤ` to `ℚ`. -/
def rationalFormMatrix (L : PositiveDefiniteIntegralLattice n) :
    Matrix (Fin n) (Fin n) ℚ :=
  L.pairingMatrix.map (algebraMap ℤ ℚ)

theorem rationalFormMatrix_det_ne_zero (L : PositiveDefiniteIntegralLattice n) :
    L.rationalFormMatrix.det ≠ 0 := by
  have hdet : L.pairingMatrix.det ≠ 0 := by
    simpa [pairingDeterminant] using (ne_of_gt L.pairingDeterminant_pos)
  have hmapdet : (L.pairingMatrix.det : ℚ) = L.rationalFormMatrix.det := by
    simpa [rationalFormMatrix] using
      (RingHom.map_det (Int.castRingHom ℚ) L.pairingMatrix)
  rw [← hmapdet]
  exact_mod_cast hdet

/-- Hasse--Minkowski supplies a rational comparison matrix from the real and
finite-prime integral comparisons in the definition of the genus. -/
theorem exists_rationalComparison_of_isSameGenus
    (L M : PositiveDefiniteIntegralLattice n) (h : L.IsSameGenus M) :
    ∃ P : GL (Fin n) ℚ,
      P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix := by
  apply Matrix.isCongruent_rat_of_isCongruent_at_all_places
  · exact L.form_symm.map _
  · exact M.form_symm.map _
  · exact L.rationalFormMatrix_det_ne_zero
  · exact M.rationalFormMatrix_det_ne_zero
  · rcases h.2 with ⟨U, hUunit, hU⟩
    apply Matrix.IsCongruent.symm
    refine ⟨hUunit.unit, ?_⟩
    simpa [pairingMatrix_real, rationalFormMatrix, IsUnit.unit_spec] using hU
  · intro p _
    rcases h.1 p with ⟨U, hUunit, hU⟩
    apply Matrix.IsCongruent.symm
    have hcong :
        (M.pairingMatrix_padic p).IsCongruent (L.pairingMatrix_padic p) := by
      refine ⟨hUunit.unit, ?_⟩
      simpa [IsUnit.unit_spec] using hU
    simpa [pairingMatrix_padic, rationalFormMatrix] using
      (hcong.map PadicInt.Coe.ringHom)

/-- The rational orthogonal matrix group attached to `L`. -/
def rationalOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup (Matrix (Fin n) (Fin n) ℚ)ˣ :=
  formPreservingMatrixSubgroup L.rationalFormMatrix

@[simp]
theorem mem_rationalOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    g ∈ L.rationalOrthogonalMatrixSubgroup ↔
      g.1ᵀ * L.rationalFormMatrix * g.1 = L.rationalFormMatrix :=
  Iff.rfl

/-- The finite-adelic form matrix is the diagonal image of the rational form
matrix. -/
theorem finiteAdelicFormMatrix_eq_map_rationalFormMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.finiteAdelicFormMatrix =
      L.rationalFormMatrix.map (algebraMap ℚ RationalFiniteAdele) := by
  ext i j
  simp [finiteAdelicFormMatrix, rationalFormMatrix]

/-- The diagonal homomorphism from rational orthogonal matrices to the
finite-adelic orthogonal group. -/
def rationalOrthogonalDiagonalHom (L : PositiveDefiniteIntegralLattice n) :
    L.rationalOrthogonalMatrixSubgroup →*
      L.ConcreteFiniteAdelicOrthogonalGroup where
  toFun g := by
    let mapped := Matrix.GeneralLinearGroup.map
      (n := Fin n) (algebraMap ℚ RationalFiniteAdele) g.1
    refine ⟨mapped, ?_⟩
    rw [mem_finiteAdelicOrthogonalMatrixSubgroup_iff,
      L.finiteAdelicFormMatrix_eq_map_rationalFormMatrix]
    have hmapped := congrArg
      (fun M ↦ M.map (algebraMap ℚ RationalFiniteAdele)) g.2
    simpa [mapped, Matrix.map_mul, Matrix.transpose_map] using hmapped
  map_one' := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_one
      (n := Fin n) (algebraMap ℚ RationalFiniteAdele)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_mul
      (n := Fin n) (algebraMap ℚ RationalFiniteAdele) g.1 h.1

@[simp]
theorem rationalOrthogonalDiagonalHom_apply_matrix
    (L : PositiveDefiniteIntegralLattice n) (g : L.rationalOrthogonalMatrixSubgroup) :
    (L.rationalOrthogonalDiagonalHom g).1.1 =
      g.1.1.map (algebraMap ℚ RationalFiniteAdele) := by
  apply Matrix.ext
  intro i j
  exact Matrix.GeneralLinearGroup.map_apply
    (algebraMap ℚ RationalFiniteAdele) i j g.1

/-- The diagonal rational orthogonal subgroup inside the concrete
finite-adelic orthogonal group. -/
def rationalOrthogonalDiagonalSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFiniteAdelicOrthogonalGroup :=
  L.rationalOrthogonalDiagonalHom.range

noncomputable instance rationalMatrixCountable :
    Countable (Matrix (Fin n) (Fin n) ℚ) := by
  letI : Countable (Fin n → ℚ) := by
    rw [← Set.countable_univ_iff]
    simpa using Set.countable_univ_pi
      (α := Fin n) (π := fun _ => ℚ) (s := fun _ => Set.univ)
      (fun _ => Set.countable_univ)
  rw [← Set.countable_univ_iff]
  simpa [Matrix] using Set.countable_univ_pi
    (α := Fin n) (π := fun _ => Fin n → ℚ) (s := fun _ => Set.univ)
    (fun _ => Set.countable_univ)

noncomputable instance rationalMatrixUnitsCountable :
    Countable (Matrix (Fin n) (Fin n) ℚ)ˣ :=
  Units.val_injective.countable

noncomputable instance rationalOrthogonalMatrixSubgroupCountable
    (L : PositiveDefiniteIntegralLattice n) :
    Countable L.rationalOrthogonalMatrixSubgroup :=
  Subtype.val_injective.countable

/-- The diagonal rational orthogonal subgroup is countable because it is the
range of the diagonal homomorphism from rational matrices. -/
noncomputable instance rationalOrthogonalDiagonalSubgroupCountable
    (L : PositiveDefiniteIntegralLattice n) :
    Countable L.rationalOrthogonalDiagonalSubgroup :=
  L.rationalOrthogonalDiagonalHom.rangeRestrict_surjective.countable

theorem mem_rationalOrthogonalDiagonalSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    g ∈ L.rationalOrthogonalDiagonalSubgroup ↔
      ∃ q : L.rationalOrthogonalMatrixSubgroup,
        L.rationalOrthogonalDiagonalHom q = g :=
  Iff.rfl

/-- The diagonal embedding of rational orthogonal matrices into the finite
adeles is injective. -/
theorem rationalOrthogonalDiagonalHom_injective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Injective L.rationalOrthogonalDiagonalHom := by
  intro q r h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hm := congrArg
    (fun z : L.ConcreteFiniteAdelicOrthogonalGroup => z.1.1 i j) h
  change algebraMap ℚ RationalFiniteAdele (q.1.1 i j) =
    algebraMap ℚ RationalFiniteAdele (r.1.1 i j) at hm
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hmv := congrArg (fun a : RationalFiniteAdele => a v) hm
  change algebraMap ℚ (v.adicCompletion ℚ) (q.1.1 i j) =
    algebraMap ℚ (v.adicCompletion ℚ) (r.1.1 i j) at hmv
  exact (algebraMap ℚ (v.adicCompletion ℚ)).injective hmv

/-! ## Concrete finite local lattice stabilizer -/

/-- The finite adeles that are integral at every finite place. -/
def integralFiniteAdeleSubring : Subring RationalFiniteAdele where
  carrier :=
    {a | ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      a v ∈ v.adicCompletionIntegers ℚ}
  zero_mem' := by
    intro v
    exact Subring.zero_mem _
  one_mem' := by
    intro v
    exact Subring.one_mem _
  add_mem' := by
    intro a b ha hb v
    exact Subring.add_mem _ (ha v) (hb v)
  neg_mem' := by
    intro a ha v
    exact Subring.neg_mem _ (ha v)
  mul_mem' := by
    intro a b ha hb v
    exact Subring.mul_mem _ (ha v) (hb v)

@[simp]
theorem mem_integralFiniteAdeleSubring_iff (a : RationalFiniteAdele) :
    a ∈ integralFiniteAdeleSubring ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- A rational number is integral at every finite place exactly when it is an
integer. -/
theorem rational_mem_integralFiniteAdeleSubring_iff (q : ℚ) :
    algebraMap ℚ RationalFiniteAdele q ∈ integralFiniteAdeleSubring ↔
      q ∈ (algebraMap ℤ ℚ).range := by
  constructor
  · intro hq
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := hq v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    have hcomp : ((algebraMap ℚ RationalFiniteAdele) q) v =
        algebraMap ℚ (v.adicCompletion ℚ) q := rfl
    rw [hcomp] at hv
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at hv
    simpa using hv
  · rintro ⟨z, rfl⟩
    intro v
    exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem ℤ ℚ v z

/-- The finite set of places where a finite adele is not integral. -/
def finiteAdeleNonintegralPlaces (a : RationalFiniteAdele) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (show Set.Finite
      {v : IsDedekindDomain.HeightOneSpectrum ℤ |
        a v ∉ v.adicCompletionIntegers ℚ} by
    simpa only [Filter.eventually_cofinite] using a.2).toFinset

@[simp]
theorem mem_finiteAdeleNonintegralPlaces_iff (a : RationalFiniteAdele)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    v ∈ finiteAdeleNonintegralPlaces a ↔
      a v ∉ v.adicCompletionIntegers ℚ := by
  simp [finiteAdeleNonintegralPlaces]

/-- A nonzero integer that clears one finite-adele component at one place. -/
noncomputable def finiteAdelePlaceDenominator (a : RationalFiniteAdele)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℤ :=
  Classical.choose
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (R := ℤ) (K := ℚ) v (a v))

theorem finiteAdelePlaceDenominator_mem_nonZeroDivisors
    (a : RationalFiniteAdele) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelePlaceDenominator a v ∈ nonZeroDivisors ℤ :=
  (Classical.choose_spec
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (R := ℤ) (K := ℚ) v (a v))).1

theorem finiteAdele_mul_placeDenominator_mem_adicCompletionIntegers
    (a : RationalFiniteAdele) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    a v * algebraMap ℤ (v.adicCompletion ℚ) (finiteAdelePlaceDenominator a v) ∈
      v.adicCompletionIntegers ℚ :=
  (Classical.choose_spec
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (R := ℤ) (K := ℚ) v (a v))).2

/-- A common nonzero integer denominator for all components of a finite
adele. -/
noncomputable def finiteAdeleDenominator (a : RationalFiniteAdele) : ℤ :=
  ∏ v ∈ finiteAdeleNonintegralPlaces a, finiteAdelePlaceDenominator a v

theorem finiteAdeleDenominator_ne_zero (a : RationalFiniteAdele) :
    finiteAdeleDenominator a ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  exact nonZeroDivisors.ne_zero
    (finiteAdelePlaceDenominator_mem_nonZeroDivisors a v)

theorem finiteAdeleDenominator_mul_mem_integralFiniteAdeleSubring
    (a : RationalFiniteAdele) :
    algebraMap ℤ RationalFiniteAdele (finiteAdeleDenominator a) * a ∈
      integralFiniteAdeleSubring := by
  classical
  intro v
  by_cases hv : v ∈ finiteAdeleNonintegralPlaces a
  · have hclear := finiteAdele_mul_placeDenominator_mem_adicCompletionIntegers a v
    let rest : ℤ := ∏ w ∈ (finiteAdeleNonintegralPlaces a).erase v,
      finiteAdelePlaceDenominator a w
    have hrest : algebraMap ℤ (v.adicCompletion ℚ) rest ∈
        v.adicCompletionIntegers ℚ :=
      IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem ℤ ℚ v rest
    have hprod : finiteAdeleDenominator a =
        finiteAdelePlaceDenominator a v * rest := by
      rw [finiteAdeleDenominator, Finset.mul_prod_erase _ _ hv]
    change algebraMap ℤ (v.adicCompletion ℚ) (finiteAdeleDenominator a) * a v ∈
      v.adicCompletionIntegers ℚ
    rw [hprod, map_mul]
    simpa [rest, mul_comm, mul_left_comm, mul_assoc] using
      Subring.mul_mem _ hclear hrest
  · have ha : a v ∈ v.adicCompletionIntegers ℚ := by
      simpa [mem_finiteAdeleNonintegralPlaces_iff] using hv
    have hden : algebraMap ℤ (v.adicCompletion ℚ) (finiteAdeleDenominator a) ∈
        v.adicCompletionIntegers ℚ :=
      IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem ℤ ℚ v
        (finiteAdeleDenominator a)
    exact Subring.mul_mem _ hden ha

theorem integer_mem_integralFiniteAdeleSubring (z : ℤ) :
    algebraMap ℤ RationalFiniteAdele z ∈ integralFiniteAdeleSubring := by
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem ℤ ℚ v z

/-- A common nonzero integer denominator for every entry of a finite-adele
matrix. -/
noncomputable def finiteAdeleMatrixDenominator
    (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) : ℤ :=
  ∏ ij : Fin n × Fin n, finiteAdeleDenominator (M ij.1 ij.2)

theorem finiteAdeleMatrixDenominator_ne_zero
    (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) :
    finiteAdeleMatrixDenominator M ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  exact finiteAdeleDenominator_ne_zero (M ij.1 ij.2)

theorem finiteAdeleMatrixDenominator_mul_entry_mem_integralFiniteAdeleSubring
    (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) (i j : Fin n) :
    (finiteAdeleMatrixDenominator M : RationalFiniteAdele) * M i j ∈
      integralFiniteAdeleSubring := by
  classical
  let rest : ℤ := ∏ ij ∈ (Finset.univ.erase (i, j)),
    finiteAdeleDenominator (M ij.1 ij.2)
  have hentry := finiteAdeleDenominator_mul_mem_integralFiniteAdeleSubring (M i j)
  have hrest := integer_mem_integralFiniteAdeleSubring rest
  have hprod : finiteAdeleMatrixDenominator M =
      finiteAdeleDenominator (M i j) * rest := by
    dsimp [finiteAdeleMatrixDenominator, rest]
    simpa using (Finset.mul_prod_erase Finset.univ
      (fun ij : Fin n × Fin n ↦ finiteAdeleDenominator (M ij.1 ij.2))
      (Finset.mem_univ (i, j))).symm
  rw [hprod, Int.cast_mul]
  simpa [rest, mul_comm, mul_left_comm, mul_assoc] using
    Subring.mul_mem integralFiniteAdeleSubring hentry hrest

/-- If the outer matrices have fixed integer denominators and the middle
matrix is integral, then the same product denominator clears every entry of
their three-matrix product. -/
theorem matrix_mul_matrix_mul_entry_mem_subring_of_denominators
    {R : Type*} [CommRing R] (S : Subring R) (dA dC : ℤ)
    (A B C : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, (dA : R) * A i j ∈ S)
    (hB : ∀ i j, B i j ∈ S)
    (hC : ∀ i j, (dC : R) * C i j ∈ S)
    (i j : Fin n) :
    ((dA * dC : ℤ) : R) * (A * B * C) i j ∈ S := by
  classical
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Subring.sum_mem
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Subring.sum_mem
  intro l _
  have hterm := Subring.mul_mem S
    (Subring.mul_mem S (hA i l) (hB l k)) (hC k j)
  simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using hterm

/-- The everywhere-integral finite adeles form the canonical open integral
block in the restricted-product topology. -/
theorem isOpen_integralFiniteAdeleSubring :
    IsOpen (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (A := fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

/-- The everywhere-integral finite adeles form a compact subset of the finite
adele ring. -/
theorem isCompact_integralFiniteAdeleSubring :
    IsCompact (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      CompactSpace (v.adicCompletionIntegers ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace
  have hcompact : IsCompact (Set.univ : Set
      ((v : IsDedekindDomain.HeightOneSpectrum ℤ) →
        v.adicCompletionIntegers ℚ)) :=
    isCompact_univ
  have himage := hcompact.image
    (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        v.adicCompletion ℚ)
      (A := fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      (𝓕 := Filter.cofinite)).continuous
  rw [Set.image_univ, RestrictedProduct.range_structureMap] at himage
  exact himage

/-- The completed coordinate lattice `prod_p L_p`, expressed in the chosen
integral basis of `L` as vectors that are integral at every finite place. -/
def integralFiniteAdeleVectors (n : ℕ) : Set (Fin n → RationalFiniteAdele) :=
  {x | ∀ i, x i ∈ integralFiniteAdeleSubring}

@[simp]
theorem mem_integralFiniteAdeleVectors_iff (x : Fin n → RationalFiniteAdele) :
    x ∈ integralFiniteAdeleVectors n ↔
      ∀ i v, x i v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- Multiplying a matrix-vector product by the common matrix denominator is
everywhere integral when the input vector is everywhere integral. -/
theorem finiteAdeleMatrixDenominator_smul_mulVec_mem_integralFiniteAdeleVectors
    (M : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (x : Fin n → RationalFiniteAdele)
    (hx : x ∈ integralFiniteAdeleVectors n) :
    finiteAdeleMatrixDenominator M • M.mulVec x ∈
      integralFiniteAdeleVectors n := by
  intro i
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum]
  apply Subring.sum_mem
  intro j _hj
  rw [← Int.cast_smul_eq_zsmul RationalFiniteAdele]
  change (finiteAdeleMatrixDenominator M : RationalFiniteAdele) *
      (M i j * x j) ∈ integralFiniteAdeleSubring
  rw [← mul_assoc]
  exact Subring.mul_mem integralFiniteAdeleSubring
    (finiteAdeleMatrixDenominator_mul_entry_mem_integralFiniteAdeleSubring M i j)
    (hx j)

/-- Invertible matrices over `R` whose matrix and inverse have entries in the
subring `S`. -/
def matrixUnitsOverSubring {R : Type*} [CommRing R] (S : Subring R) :
    Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
  S.matrix.toSubmonoid.units

@[simp]
theorem mem_matrixUnitsOverSubring_iff {R : Type*} [CommRing R]
    (S : Subring R) (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    g ∈ matrixUnitsOverSubring S ↔
      (∀ i j, g.1 i j ∈ S) ∧ (∀ i j, (g⁻¹).1 i j ∈ S) :=
  Iff.rfl

/-- If `S` is open, then invertible matrices whose matrix and inverse have
entries in `S` form an open subgroup of the general linear group. -/
theorem isOpen_matrixUnitsOverSubring {R : Type*} [CommRing R]
    [TopologicalSpace R] (S : Subring R) (hS : IsOpen (S : Set R)) :
    IsOpen (matrixUnitsOverSubring (n := n) S :
      Set (Matrix (Fin n) (Fin n) R)ˣ) := by
  change IsOpen
    {g : (Matrix (Fin n) (Fin n) R)ˣ |
      g.1 ∈ S.matrix ∧ (g⁻¹).1 ∈ S.matrix}
  exact (hS.matrix.preimage Units.continuous_val).inter
    (hS.matrix.preimage Units.continuous_coe_inv)

/-- Integral finite-adelic matrix units form a compact subgroup of the
finite-adelic general linear group. -/
theorem isCompact_integralFiniteAdeleMatrixUnits :
    IsCompact (matrixUnitsOverSubring (n := n) integralFiniteAdeleSubring :
      Set (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) := by
  letI : T1Space (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
    inferInstanceAs (T1Space (Fin n → Fin n → RationalFiniteAdele))
  have hsubmonoid : IsCompact
      ((Subring.matrix (n := Fin n) integralFiniteAdeleSubring).toSubmonoid :
        Set (Matrix (Fin n) (Fin n) RationalFiniteAdele)) :=
    IsCompact.matrix (m := Fin n) (n := Fin n)
      isCompact_integralFiniteAdeleSubring
  exact Submonoid.units_isCompact hsubmonoid

/-- Assemble a family of integral local matrix units into an everywhere-integral
finite-adelic matrix unit. -/
noncomputable def localIntegralMatrixUnitsFiniteAdeleGL
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ)) :
    GL (Fin n) RationalFiniteAdele := by
  let A : Matrix (Fin n) (Fin n) RationalFiniteAdele := fun i j ↦
    RestrictedProduct.structureMap
      (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
      (fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      Filter.cofinite (fun v ↦ (U v).1 i j)
  let B : Matrix (Fin n) (Fin n) RationalFiniteAdele := fun i j ↦
    RestrictedProduct.structureMap
      (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
      (fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      Filter.cofinite (fun v ↦ (U v).inv i j)
  refine ⟨A, B, ?_, ?_⟩
  · ext i j v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦ w.adicCompletion ℚ) v
    change ev ((A * B) i j) = ev ((1 : Matrix _ _ RationalFiniteAdele) i j)
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul]
    have hA (a b : Fin n) : ev (A a b) =
        ((U v).1 a b : v.adicCompletion ℚ) := rfl
    have hB (a b : Fin n) : ev (B a b) =
        ((U v).inv a b : v.adicCompletion ℚ) := rfl
    simp_rw [hA, hB]
    let Ufield : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype (U v)
    have hij := congr_fun (congr_fun Ufield.val_inv i) j
    change (∑ k, ((U v).1 i k : v.adicCompletion ℚ) *
      ((U v).inv k j : v.adicCompletion ℚ)) =
        (1 : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) i j at hij
    by_cases h : i = j
    · subst j
      simpa [Matrix.one_apply] using hij
    · simpa [Matrix.one_apply, h] using hij
  · ext i j v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦ w.adicCompletion ℚ) v
    change ev ((B * A) i j) = ev ((1 : Matrix _ _ RationalFiniteAdele) i j)
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul]
    have hA (a b : Fin n) : ev (A a b) =
        ((U v).1 a b : v.adicCompletion ℚ) := rfl
    have hB (a b : Fin n) : ev (B a b) =
        ((U v).inv a b : v.adicCompletion ℚ) := rfl
    simp_rw [hA, hB]
    let Ufield : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype (U v)
    have hij := congr_fun (congr_fun Ufield.inv_val i) j
    change (∑ k, ((U v).inv i k : v.adicCompletion ℚ) *
      ((U v).1 k j : v.adicCompletion ℚ)) =
        (1 : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) i j at hij
    by_cases h : i = j
    · subst j
      simpa [Matrix.one_apply] using hij
    · simpa [Matrix.one_apply, h] using hij

/-- Evaluating the assembled finite-adelic matrix unit at a finite place
recovers the corresponding local unit. -/
theorem localIntegralMatrixUnitsFiniteAdeleGL_map_eval
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦ w.adicCompletion ℚ) v
    Matrix.GeneralLinearGroup.map ev
        (localIntegralMatrixUnitsFiniteAdeleGL U) =
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype (U v) := by
  dsimp only
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply]
  change
    (RestrictedProduct.structureMap
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦ w.adicCompletion ℚ)
      (fun w ↦ (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)))
      Filter.cofinite (fun w ↦ (U w).1 i j)) v =
        ((U v).1 i j : v.adicCompletion ℚ)
  rfl

/-- Componentwise integral local form equations assemble to the corresponding
finite-adelic form equation. -/
theorem localIntegralMatrixUnitsFiniteAdeleGL_form_eq
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (F F' : Matrix (Fin n) (Fin n) ℤ)
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * F.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        F'.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    let Uf := localIntegralMatrixUnitsFiniteAdeleGL U
    Uf.1ᵀ * F.map (algebraMap ℤ RationalFiniteAdele) * Uf.1 =
      F'.map (algebraMap ℤ RationalFiniteAdele) := by
  dsimp only
  let Uf := localIntegralMatrixUnitsFiniteAdeleGL U
  ext i j v
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦ w.adicCompletion ℚ) v
  let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
    Matrix.GeneralLinearGroup.map
      (v.adicCompletionIntegers ℚ).subtype (U v)
  have hUf : Uf.1.map ev = Uv.1 := by
    have hmap := localIntegralMatrixUnitsFiniteAdeleGL_map_eval U v
    exact congrArg Units.val hmap
  have hleft :
      (Uf.1ᵀ * F.map (algebraMap ℤ RationalFiniteAdele) * Uf.1).map ev =
        Uv.1ᵀ * F.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hUf]
    congr 2
  have hright :
      (F'.map (algebraMap ℤ RationalFiniteAdele)).map ev =
        F'.map (algebraMap ℤ (v.adicCompletion ℚ)) := by
    ext a b
    simp [ev]
  have hlocal := hU v
  have hmatrix :
      (Uf.1ᵀ * F.map (algebraMap ℤ RationalFiniteAdele) * Uf.1).map ev =
        (F'.map (algebraMap ℤ RationalFiniteAdele)).map ev := by
    rw [hleft, hright]
    exact hlocal
  exact congr_fun (congr_fun hmatrix i) j

/-- Reindex a finite-prime integral comparison from `IsSameGenus` by a
height-one prime of `ℤ`. -/
noncomputable def sameGenusHeightOneLocalIntegralMatrixUnit
    (L M : PositiveDefiniteIntegralLattice n) (h : L.IsSameGenus M)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    GL (Fin n) (v.adicCompletionIntegers ℚ) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let A := Classical.choose (h.1 p)
  have hAunit : IsUnit A := (Classical.choose_spec (h.1 p)).1
  let algA : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  let algB : Algebra ℤ ℤ_[p] := Ring.toIntAlgebra ℤ_[p]
  let e : @ContinuousAlgEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
      _ _ _ _ _ algA algB :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let ae := @ContinuousAlgEquiv.toAlgEquiv ℤ
    (v.adicCompletionIntegers ℚ) ℤ_[p] _ _ _ _ _ algA algB e
  let er := @AlgEquiv.toRingEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
    _ _ _ algA algB ae
  exact (Units.mapEquiv er.mapMatrix.toMulEquiv).symm hAunit.unit

/-- The height-one local units obtained from `IsSameGenus` satisfy the local
form equations consumed by the finite-adelic assembly. -/
theorem exists_heightOneLocalIntegralMatrixUnits_of_isSameGenus
    (L M : PositiveDefiniteIntegralLattice n) (h : L.IsSameGenus M) :
    ∃ U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
        GL (Fin n) (v.adicCompletionIntegers ℚ),
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
          Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype (U v)
        Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
          L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) := by
  let U := sameGenusHeightOneLocalIntegralMatrixUnit L M h
  refine ⟨U, ?_⟩
  intro v
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let A := Classical.choose (h.1 p)
  have hAunit : IsUnit A := (Classical.choose_spec (h.1 p)).1
  have hAform : Aᵀ * M.pairingMatrix_padic p * A = L.pairingMatrix_padic p :=
    (Classical.choose_spec (h.1 p)).2
  let algA : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  let algB : Algebra ℤ ℤ_[p] := Ring.toIntAlgebra ℤ_[p]
  let e : @ContinuousAlgEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
      _ _ _ _ _ algA algB :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let ae := @ContinuousAlgEquiv.toAlgEquiv ℤ
    (v.adicCompletionIntegers ℚ) ℤ_[p] _ _ _ _ _ algA algB e
  let er := @AlgEquiv.toRingEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
    _ _ _ algA algB ae
  have hUe :
      (sameGenusHeightOneLocalIntegralMatrixUnit L M h v).1.map
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v) = A := by
    change er.mapMatrix
      ((Units.mapEquiv er.mapMatrix.toMulEquiv).symm hAunit.unit).1 = A
    exact congrArg Units.val
      ((Units.mapEquiv er.mapMatrix.toMulEquiv).apply_symm_apply hAunit.unit)
  let ev := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hUv :
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)).1.map
            ev.toRingEquiv.toRingHom =
        A.map PadicInt.Coe.ringHom := by
    ext i j
    have hij := congr_fun (congr_fun hUe i) j
    exact congrArg Subtype.val hij
  have hMmap :
      (M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom =
        (M.pairingMatrix_padic p).map PadicInt.Coe.ringHom := by
    ext i j
    simp [pairingMatrix_padic, p, ev]
  have hLmap :
      (L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom := by
    ext i j
    simp [pairingMatrix_padic, p, ev]
  apply Matrix.map_injective (f := ev.toRingEquiv.toRingHom) ev.injective
  change
    (((Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype (U v)).1ᵀ *
          M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) *
        (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)).1).map
      ev.toRingEquiv.toRingHom) =
    (L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
      ev.toRingEquiv.toRingHom
  have hmap := congrArg
    (fun X : Matrix (Fin n) (Fin n) ℤ_[Rat.HeightOneSpectrum.primesEquiv v] =>
      X.map PadicInt.Coe.ringHom) hAform
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hUv,
    hMmap, hLmap]
  simpa [Matrix.map_mul, Matrix.transpose_map] using hmap

/-- Given a rational comparison from `L` to `M` and compatible integral local
comparisons back from `M` to `L`, multiply the diagonal rational matrix by the
assembled local units to obtain a concrete finite-adelic orthogonal element. -/
noncomputable def concreteFiniteAdelicRepresentativeOfRationalComparison
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    L.ConcreteFiniteAdelicOrthogonalGroup := by
  let Pfa : GL (Fin n) RationalFiniteAdele :=
    Matrix.GeneralLinearGroup.map (algebraMap ℚ RationalFiniteAdele) P
  let Uf := localIntegralMatrixUnitsFiniteAdeleGL U
  let g : GL (Fin n) RationalFiniteAdele := Pfa * Uf
  refine ⟨g, ?_⟩
  rw [L.mem_finiteAdelicOrthogonalMatrixSubgroup_iff]
  have hPfa :
      Pfa.1ᵀ * L.finiteAdelicFormMatrix * Pfa.1 =
        M.finiteAdelicFormMatrix := by
    have hmap := congrArg
      (fun A ↦ A.map (algebraMap ℚ RationalFiniteAdele)) hP
    simpa [Pfa, finiteAdelicFormMatrix_eq_map_rationalFormMatrix,
      Matrix.map_mul, Matrix.transpose_map] using hmap
  have hUf :
      Uf.1ᵀ * M.finiteAdelicFormMatrix * Uf.1 =
        L.finiteAdelicFormMatrix := by
    simpa [Uf, finiteAdelicFormMatrix] using
      (localIntegralMatrixUnitsFiniteAdeleGL_form_eq U M.pairingMatrix L.pairingMatrix hU)
  change (Pfa.1 * Uf.1)ᵀ * L.finiteAdelicFormMatrix * (Pfa.1 * Uf.1) =
    L.finiteAdelicFormMatrix
  rw [Matrix.transpose_mul]
  calc
    (Uf.1ᵀ * Pfa.1ᵀ) * L.finiteAdelicFormMatrix * (Pfa.1 * Uf.1) =
        Uf.1ᵀ * (Pfa.1ᵀ * L.finiteAdelicFormMatrix * Pfa.1) * Uf.1 := by
      simp only [Matrix.mul_assoc]
    _ = L.finiteAdelicFormMatrix := by rw [hPfa, hUf]

@[simp]
theorem concreteFiniteAdelicRepresentativeOfRationalComparison_matrix
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    (L.concreteFiniteAdelicRepresentativeOfRationalComparison
      M P hP U hU).1.1 =
      P.1.map (algebraMap ℚ RationalFiniteAdele) *
        (localIntegralMatrixUnitsFiniteAdeleGL U).1 := by
  rfl

theorem localIntegralMatrixUnitsFiniteAdeleGL_mem_matrixUnitsOverSubring
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ)) :
    localIntegralMatrixUnitsFiniteAdeleGL U ∈
      matrixUnitsOverSubring (n := n) integralFiniteAdeleSubring := by
  rw [mem_matrixUnitsOverSubring_iff]
  constructor
  · intro i j v
    change ((U v).1 i j : v.adicCompletion ℚ) ∈
      v.adicCompletionIntegers ℚ
    exact ((U v).1 i j).property
  · intro i j v
    change ((U v).inv i j : v.adicCompletion ℚ) ∈
      v.adicCompletionIntegers ℚ
    exact ((U v).inv i j).property

/-- The finite local stabilizer of `L`, represented in its chosen integral
basis.  It consists of orthogonal matrices whose matrix and inverse are
integral at every finite place. -/
def finiteLocalLatticeStabilizerSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFiniteAdelicOrthogonalGroup :=
  (matrixUnitsOverSubring integralFiniteAdeleSubring).comap
    L.finiteAdelicOrthogonalMatrixSubgroup.subtype

@[simp]
theorem mem_finiteLocalLatticeStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    g ∈ L.finiteLocalLatticeStabilizerSubgroup ↔
      (∀ i j, g.1.1 i j ∈ integralFiniteAdeleSubring) ∧
        (∀ i j, (g.1⁻¹).1 i j ∈ integralFiniteAdeleSubring) :=
  Iff.rfl

theorem mem_finiteLocalLatticeStabilizerSubgroup_iff_placewise
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    g ∈ L.finiteLocalLatticeStabilizerSubgroup ↔
      (∀ i j v, g.1.1 i j v ∈ v.adicCompletionIntegers ℚ) ∧
        (∀ i j v, (g.1⁻¹).1 i j v ∈ v.adicCompletionIntegers ℚ) :=
  Iff.rfl

/-- The arithmetic stabilizer of the identity finite double coset. -/
def concreteIdentityArithmeticStabilizerSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFiniteAdelicOrthogonalGroup :=
  L.finiteLocalLatticeStabilizerSubgroup ⊓
    L.rationalOrthogonalDiagonalSubgroup

/-- A rational orthogonal lift of an element of the identity arithmetic
stabilizer. -/
noncomputable def rationalOrthogonalOfConcreteIdentityArithmeticStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.concreteIdentityArithmeticStabilizerSubgroup) :
    L.rationalOrthogonalMatrixSubgroup :=
  Classical.choose g.2.2

theorem rationalOrthogonalDiagonalHom_rationalOrthogonalOfConcreteIdentityArithmeticStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.concreteIdentityArithmeticStabilizerSubgroup) :
    L.rationalOrthogonalDiagonalHom
        (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g) = g.1 :=
  Classical.choose_spec g.2.2

theorem rationalOrthogonalOfConcreteIdentityArithmeticStabilizer_entry_integral
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.concreteIdentityArithmeticStabilizerSubgroup) (i j : Fin n) :
    algebraMap ℚ RationalFiniteAdele
        ((L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1.1 i j) ∈
      integralFiniteAdeleSubring := by
  have hg := (L.mem_finiteLocalLatticeStabilizerSubgroup_iff g.1).mp g.2.1
  rw [← L.rationalOrthogonalDiagonalHom_rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g]
    at hg
  simpa using hg.1 i j

/-- The integral matrix underlying an element of the identity arithmetic
stabilizer. -/
noncomputable def integralMatrixOfConcreteIdentityArithmeticStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.concreteIdentityArithmeticStabilizerSubgroup) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ Classical.choose
    ((rational_mem_integralFiniteAdeleSubring_iff
      ((L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1.1 i j)).mp
      (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer_entry_integral g i j))

theorem integralMatrixOfConcreteIdentityArithmeticStabilizer_map
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.concreteIdentityArithmeticStabilizerSubgroup) :
    (L.integralMatrixOfConcreteIdentityArithmeticStabilizer g).map
        (algebraMap ℤ ℚ) =
      (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1.1 := by
  ext i j
  exact Classical.choose_spec
    ((rational_mem_integralFiniteAdeleSubring_iff
      ((L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1.1 i j)).mp
      (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer_entry_integral g i j))

theorem integralMatrixOfConcreteIdentityArithmeticStabilizer_preserves_form
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.concreteIdentityArithmeticStabilizerSubgroup) :
    (L.integralMatrixOfConcreteIdentityArithmeticStabilizer g).transpose *
        L.pairingMatrix * L.integralMatrixOfConcreteIdentityArithmeticStabilizer g =
      L.pairingMatrix := by
  apply Matrix.map_injective (f := algebraMap ℤ ℚ)
    (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ))
  have hg := (L.mem_rationalOrthogonalMatrixSubgroup_iff
    (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1).mp
      (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).2
  rw [← L.integralMatrixOfConcreteIdentityArithmeticStabilizer_map g] at hg
  change ((L.integralMatrixOfConcreteIdentityArithmeticStabilizer g).transpose *
      L.pairingMatrix * L.integralMatrixOfConcreteIdentityArithmeticStabilizer g).map
        (algebraMap ℤ ℚ) = L.pairingMatrix.map (algebraMap ℤ ℚ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  simpa [rationalFormMatrix] using hg

/-- Forgetting the adelic presentation embeds the identity arithmetic
stabilizer into integral form-preserving matrices. -/
noncomputable def concreteIdentityArithmeticStabilizerToFormPreservingMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteIdentityArithmeticStabilizerSubgroup →
      {U : Matrix (Fin n) (Fin n) ℤ //
        U.transpose * L.pairingMatrix * U = L.pairingMatrix} :=
  fun g ↦ ⟨L.integralMatrixOfConcreteIdentityArithmeticStabilizer g,
    L.integralMatrixOfConcreteIdentityArithmeticStabilizer_preserves_form g⟩

theorem concreteIdentityArithmeticStabilizerToFormPreservingMatrix_injective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Injective L.concreteIdentityArithmeticStabilizerToFormPreservingMatrix := by
  intro g h hgh
  have hmatrix : L.integralMatrixOfConcreteIdentityArithmeticStabilizer g =
      L.integralMatrixOfConcreteIdentityArithmeticStabilizer h :=
    congrArg Subtype.val hgh
  have hqmatrix :
      (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1.1 =
        (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer h).1.1 := by
    rw [← L.integralMatrixOfConcreteIdentityArithmeticStabilizer_map g,
      ← L.integralMatrixOfConcreteIdentityArithmeticStabilizer_map h, hmatrix]
  have hqunits :
      (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g).1 =
        (L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer h).1 :=
    Units.ext hqmatrix
  have hq : L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g =
      L.rationalOrthogonalOfConcreteIdentityArithmeticStabilizer h :=
    Subtype.ext hqunits
  apply Subtype.ext
  rw [← L.rationalOrthogonalDiagonalHom_rationalOrthogonalOfConcreteIdentityArithmeticStabilizer g,
    ← L.rationalOrthogonalDiagonalHom_rationalOrthogonalOfConcreteIdentityArithmeticStabilizer h,
    hq]

/-- The arithmetic stabilizer of the identity finite double coset is finite. -/
theorem finite_concreteIdentityArithmeticStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    Finite L.concreteIdentityArithmeticStabilizerSubgroup := by
  letI : Fintype {U : Matrix (Fin n) (Fin n) ℤ //
      U.transpose * L.pairingMatrix * U = L.pairingMatrix} :=
    (finite_form_preserving_matrices L).fintype
  exact Finite.of_injective
    L.concreteIdentityArithmeticStabilizerToFormPreservingMatrix
    L.concreteIdentityArithmeticStabilizerToFormPreservingMatrix_injective

/-- The concrete right-piece stabilizer at `g`, namely
`H_f ∩ g⁻¹ O(V)(ℚ) g`. -/
def concreteLocalRightStabilizerSubgroup (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Subgroup L.ConcreteFiniteAdelicOrthogonalGroup :=
  L.finiteLocalLatticeStabilizerSubgroup ⊓
    conjugateSubgroupCore L.rationalOrthogonalDiagonalSubgroup g⁻¹

/-- The concrete arithmetic stabilizer `O(V)(Q) ∩ g H_f g⁻¹`. -/
def concreteArithmeticStabilizerSubgroup (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Subgroup L.ConcreteFiniteAdelicOrthogonalGroup :=
  L.rationalOrthogonalDiagonalSubgroup ⊓
    conjugateSubgroupCore L.finiteLocalLatticeStabilizerSubgroup g

/-- Rational orthogonal matrices whose diagonal finite-adelic image belongs
to the arithmetic stabilizer at `g`. -/
def concreteRationalArithmeticStabilizerSubgroup (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Subgroup L.rationalOrthogonalMatrixSubgroup :=
  (conjugateSubgroupCore L.finiteLocalLatticeStabilizerSubgroup g).comap
    L.rationalOrthogonalDiagonalHom

/-- Faithfulness of the rational diagonal embedding identifies the ambient
arithmetic stabilizer with its rational orthogonal preimage. -/
noncomputable def concreteRationalArithmeticStabilizerEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteRationalArithmeticStabilizerSubgroup g ≃
      L.concreteArithmeticStabilizerSubgroup g where
  toFun q := ⟨L.rationalOrthogonalDiagonalHom q.1,
    ⟨⟨q.1, rfl⟩, q.2⟩⟩
  invFun a := by
    let q : L.rationalOrthogonalMatrixSubgroup := Classical.choose a.2.1
    have hq : L.rationalOrthogonalDiagonalHom q = a.1 :=
      Classical.choose_spec a.2.1
    refine ⟨q, ?_⟩
    change L.rationalOrthogonalDiagonalHom q ∈
      conjugateSubgroupCore L.finiteLocalLatticeStabilizerSubgroup g
    rw [hq]
    exact a.2.2
  left_inv q := by
    apply Subtype.ext
    apply L.rationalOrthogonalDiagonalHom_injective
    exact Classical.choose_spec
      ((show L.rationalOrthogonalDiagonalHom q.1 ∈
          L.rationalOrthogonalDiagonalSubgroup from ⟨q.1, rfl⟩))
  right_inv a := by
    apply Subtype.ext
    exact Classical.choose_spec a.2.1

theorem mem_concreteLocalRightStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g x : L.ConcreteFiniteAdelicOrthogonalGroup) :
    x ∈ L.concreteLocalRightStabilizerSubgroup g ↔
      x ∈ L.finiteLocalLatticeStabilizerSubgroup ∧
        ∃ q : L.rationalOrthogonalMatrixSubgroup,
          x = g⁻¹ * L.rationalOrthogonalDiagonalHom q * g := by
  constructor
  · rintro ⟨hxH, q, hq⟩
    rcases q.2 with ⟨q, hqdiag⟩
    refine ⟨hxH, q, ?_⟩
    rw [hqdiag]
    simpa using hq
  · rintro ⟨hxH, q, rfl⟩
    refine ⟨hxH, ⟨L.rationalOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩, ?_⟩
    simp

/-- A rational orthogonal lift of an element of the concrete local right
stabilizer. -/
noncomputable def rationalOrthogonalOfConcreteLocalRightStabilizer
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) :
    L.rationalOrthogonalMatrixSubgroup :=
  Classical.choose
    ((L.mem_concreteLocalRightStabilizerSubgroup_iff g x.1).mp x.2).2

theorem concreteLocalRightStabilizer_eq_conjugate_rationalOrthogonal
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) :
    x.1 = g⁻¹ * L.rationalOrthogonalDiagonalHom
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x) * g :=
  Classical.choose_spec
    ((L.mem_concreteLocalRightStabilizerSubgroup_iff g x.1).mp x.2).2

theorem rationalOrthogonalOfConcreteLocalRightStabilizer_eq_conjugate
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) :
    L.rationalOrthogonalDiagonalHom
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x) =
      g * x.1 * g⁻¹ := by
  rw [L.concreteLocalRightStabilizer_eq_conjugate_rationalOrthogonal g x]
  simp [mul_assoc]

/-- A common nonzero denominator for the entries of both `g` and `g⁻¹`. -/
noncomputable def concreteConjugationDenominator
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) : ℤ :=
  finiteAdeleMatrixDenominator g.1.1 *
    finiteAdeleMatrixDenominator (g.1⁻¹).1

theorem concreteConjugationDenominator_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteConjugationDenominator g ≠ 0 :=
  mul_ne_zero (finiteAdeleMatrixDenominator_ne_zero g.1.1)
    (finiteAdeleMatrixDenominator_ne_zero (g.1⁻¹).1)

theorem rationalOrthogonalOfConcreteLocalRightStabilizer_scaled_entry_integral
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) (i j : Fin n) :
    algebraMap ℚ RationalFiniteAdele
        ((L.concreteConjugationDenominator g : ℚ) *
          (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 i j) ∈
      integralFiniteAdeleSubring := by
  have hxH := (L.mem_finiteLocalLatticeStabilizerSubgroup_iff x.1).mp x.2.1
  have hproduct := matrix_mul_matrix_mul_entry_mem_subring_of_denominators
    integralFiniteAdeleSubring
    (finiteAdeleMatrixDenominator g.1.1)
    (finiteAdeleMatrixDenominator (g.1⁻¹).1)
    g.1.1 x.1.1 (g.1⁻¹).1
    (finiteAdeleMatrixDenominator_mul_entry_mem_integralFiniteAdeleSubring g.1.1)
    hxH.1
    (finiteAdeleMatrixDenominator_mul_entry_mem_integralFiniteAdeleSubring (g.1⁻¹).1)
    i j
  have hmatrix := congrArg
    (fun y : L.ConcreteFiniteAdelicOrthogonalGroup ↦ y.1.1)
    (L.rationalOrthogonalOfConcreteLocalRightStabilizer_eq_conjugate g x)
  change (L.rationalOrthogonalDiagonalHom
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x)).1.1 =
    (g * x.1 * g⁻¹).1.1 at hmatrix
  rw [L.rationalOrthogonalDiagonalHom_apply_matrix] at hmatrix
  change (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1.map
      (algebraMap ℚ RationalFiniteAdele) =
    g.1.1 * x.1.1 * (g.1⁻¹).1 at hmatrix
  have hmatrixEntry := congrFun (congrFun hmatrix i) j
  have hmatrixEntry' : algebraMap ℚ RationalFiniteAdele
      ((L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 i j) =
    (g.1.1 * x.1.1 * (g.1⁻¹).1) i j := by
    simpa using hmatrixEntry
  change algebraMap ℚ RationalFiniteAdele
      ((L.concreteConjugationDenominator g : ℚ) *
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 i j) ∈
    integralFiniteAdeleSubring
  rw [map_mul]
  have hcast : algebraMap ℚ RationalFiniteAdele
      (L.concreteConjugationDenominator g : ℚ) =
      (L.concreteConjugationDenominator g : RationalFiniteAdele) := by
    exact congrFun (algebraMap_comp_intCast ℚ RationalFiniteAdele)
      (L.concreteConjugationDenominator g)
  rw [hcast, hmatrixEntry']
  exact hproduct

/-- The integral matrix obtained by clearing the representative-dependent
denominator of a rational element in the concrete local right stabilizer. -/
noncomputable def integralMatrixOfConcreteLocalRightStabilizer
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ Classical.choose
    ((rational_mem_integralFiniteAdeleSubring_iff
      ((L.concreteConjugationDenominator g : ℚ) *
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 i j)).mp
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer_scaled_entry_integral g x i j))

theorem integralMatrixOfConcreteLocalRightStabilizer_map
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) :
    (L.integralMatrixOfConcreteLocalRightStabilizer g x).map
        (algebraMap ℤ ℚ) =
      (L.concreteConjugationDenominator g : ℚ) •
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 := by
  ext i j
  exact Classical.choose_spec
    ((rational_mem_integralFiniteAdeleSubring_iff
      ((L.concreteConjugationDenominator g : ℚ) *
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 i j)).mp
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer_scaled_entry_integral g x i j))

theorem integralMatrixOfConcreteLocalRightStabilizer_preserves_scaled_form
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : L.concreteLocalRightStabilizerSubgroup g) :
    (L.integralMatrixOfConcreteLocalRightStabilizer g x).transpose *
        L.pairingMatrix * L.integralMatrixOfConcreteLocalRightStabilizer g x =
      (L.concreteConjugationDenominator g ^ 2) • L.pairingMatrix := by
  apply Matrix.map_injective (f := algebraMap ℤ ℚ)
    (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ))
  have hq := (L.mem_rationalOrthogonalMatrixSubgroup_iff
    (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1).mp
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).2
  change ((L.integralMatrixOfConcreteLocalRightStabilizer g x).transpose *
      L.pairingMatrix * L.integralMatrixOfConcreteLocalRightStabilizer g x).map
        (algebraMap ℤ ℚ) =
    ((L.concreteConjugationDenominator g ^ 2) • L.pairingMatrix).map
      (algebraMap ℤ ℚ)
  have hscaled :
      ((L.concreteConjugationDenominator g ^ 2) • L.pairingMatrix).map
          (algebraMap ℤ ℚ) =
        (L.concreteConjugationDenominator g : ℚ) ^ 2 •
          L.pairingMatrix.map (algebraMap ℤ ℚ) := by
    ext i j
    change (((L.concreteConjugationDenominator g ^ 2) * L.pairingMatrix i j : ℤ) : ℚ) =
      (L.concreteConjugationDenominator g : ℚ) ^ 2 * (L.pairingMatrix i j : ℚ)
    norm_cast
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    L.integralMatrixOfConcreteLocalRightStabilizer_map g x, hscaled]
  simpa [rationalFormMatrix, pow_two, smul_smul, Matrix.smul_mul,
    Matrix.mul_smul] using
      congrArg (fun M ↦
        ((L.concreteConjugationDenominator g : ℚ) *
          (L.concreteConjugationDenominator g : ℚ)) • M) hq

/-- Clearing denominators embeds the concrete local right stabilizer into a
fixed finite set of scaled integral form-preserving matrices. -/
noncomputable def concreteLocalRightStabilizerToScaledFormMatrix
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteLocalRightStabilizerSubgroup g →
      {U : Matrix (Fin n) (Fin n) ℤ //
        U.transpose * L.pairingMatrix * U =
          (L.concreteConjugationDenominator g ^ 2) • L.pairingMatrix} :=
  fun x ↦ ⟨L.integralMatrixOfConcreteLocalRightStabilizer g x,
    L.integralMatrixOfConcreteLocalRightStabilizer_preserves_scaled_form g x⟩

theorem concreteLocalRightStabilizerToScaledFormMatrix_injective
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Function.Injective (L.concreteLocalRightStabilizerToScaledFormMatrix g) := by
  intro x y hxy
  have hmatrix : L.integralMatrixOfConcreteLocalRightStabilizer g x =
      L.integralMatrixOfConcreteLocalRightStabilizer g y :=
    congrArg Subtype.val hxy
  have hscaled :
      (L.concreteConjugationDenominator g : ℚ) •
          (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 =
        (L.concreteConjugationDenominator g : ℚ) •
          (L.rationalOrthogonalOfConcreteLocalRightStabilizer g y).1.1 := by
    rw [← L.integralMatrixOfConcreteLocalRightStabilizer_map g x,
      ← L.integralMatrixOfConcreteLocalRightStabilizer_map g y, hmatrix]
  have hden : (L.concreteConjugationDenominator g : ℚ) ≠ 0 := by
    exact_mod_cast L.concreteConjugationDenominator_ne_zero g
  have hqmatrix :
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1.1 =
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g y).1.1 := by
    ext i j
    have hij := congrFun (congrFun hscaled i) j
    exact mul_left_cancel₀ hden hij
  have hqunits :
      (L.rationalOrthogonalOfConcreteLocalRightStabilizer g x).1 =
        (L.rationalOrthogonalOfConcreteLocalRightStabilizer g y).1 :=
    Units.ext hqmatrix
  have hq : L.rationalOrthogonalOfConcreteLocalRightStabilizer g x =
      L.rationalOrthogonalOfConcreteLocalRightStabilizer g y :=
    Subtype.ext hqunits
  apply Subtype.ext
  rw [L.concreteLocalRightStabilizer_eq_conjugate_rationalOrthogonal g x,
    L.concreteLocalRightStabilizer_eq_conjugate_rationalOrthogonal g y, hq]

/-- Every concrete local right stabilizer
`H_f ∩ g⁻¹ O(V)(ℚ) g` is finite. -/
theorem finite_concreteLocalRightStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Finite (L.concreteLocalRightStabilizerSubgroup g) := by
  letI : Fintype {U : Matrix (Fin n) (Fin n) ℤ //
      U.transpose * L.pairingMatrix * U =
        (L.concreteConjugationDenominator g ^ 2) • L.pairingMatrix} :=
    (finite_matrices_preserving_form_to_fixed_target L
      ((L.concreteConjugationDenominator g ^ 2) • L.pairingMatrix)).fintype
  exact Finite.of_injective
    (L.concreteLocalRightStabilizerToScaledFormMatrix g)
    (L.concreteLocalRightStabilizerToScaledFormMatrix_injective g)

/-- The concrete local right stabilizer, regarded as a subgroup of the compact
open subgroup `H_f` itself. -/
def concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Subgroup L.finiteLocalLatticeStabilizerSubgroup where
  carrier := {h | (h : L.ConcreteFiniteAdelicOrthogonalGroup) ∈
    L.concreteLocalRightStabilizerSubgroup g}
  one_mem' := by
    exact (L.concreteLocalRightStabilizerSubgroup g).one_mem
  mul_mem' := by
    intro ha hb hha hhb
    exact (L.concreteLocalRightStabilizerSubgroup g).mul_mem hha hhb
  inv_mem' := by
    intro h hh
    exact (L.concreteLocalRightStabilizerSubgroup g).inv_mem hh

@[simp]
theorem mem_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (h : L.finiteLocalLatticeStabilizerSubgroup) :
    h ∈ L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g ↔
      (h : L.ConcreteFiniteAdelicOrthogonalGroup) ∈
        L.concreteLocalRightStabilizerSubgroup g :=
  Iff.rfl

/-- Finiteness of each concrete ambient intersection supplies the finite
subgroup of `H_f` used by the standard-Borel local selector. -/
theorem finite_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Finite
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) := by
  letI : Finite (L.concreteLocalRightStabilizerSubgroup g) :=
    L.finite_concreteLocalRightStabilizerSubgroup g
  exact Finite.of_injective
    (fun h : L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g =>
      (⟨h.1.1, (show h.1.1 ∈ L.concreteLocalRightStabilizerSubgroup g from h.2)⟩ :
        L.concreteLocalRightStabilizerSubgroup g))
    (by
      intro h k hhk
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : L.concreteLocalRightStabilizerSubgroup g => x.1) hhk)

/-- The finite local lattice stabilizer is open in the concrete finite-adelic
orthogonal group. -/
theorem isOpen_finiteLocalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsOpen (L.finiteLocalLatticeStabilizerSubgroup :
      Set L.ConcreteFiniteAdelicOrthogonalGroup) := by
  have hcontinuous : Continuous
      (fun g : L.ConcreteFiniteAdelicOrthogonalGroup ↦ g.1) :=
    continuous_subtype_val
  change IsOpen
    {g : L.ConcreteFiniteAdelicOrthogonalGroup |
      g.1 ∈ matrixUnitsOverSubring integralFiniteAdeleSubring}
  exact (isOpen_matrixUnitsOverSubring integralFiniteAdeleSubring
    isOpen_integralFiniteAdeleSubring).preimage hcontinuous

/-- The concrete finite local lattice stabilizer is compact. -/
theorem isCompact_finiteLocalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsCompact (L.finiteLocalLatticeStabilizerSubgroup :
      Set L.ConcreteFiniteAdelicOrthogonalGroup) := by
  have hembedding :=
    (isClosed_finiteAdelicOrthogonalMatrixSubgroup L).isClosedEmbedding_subtypeVal
  exact hembedding.isCompact_preimage isCompact_integralFiniteAdeleMatrixUnits

/-- The finite local lattice stabilizer is measurable in every measurable
structure that contains the open sets. -/
theorem measurableSet_finiteLocalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n)
    [MeasurableSpace L.ConcreteFiniteAdelicOrthogonalGroup]
    [OpensMeasurableSpace L.ConcreteFiniteAdelicOrthogonalGroup] :
    MeasurableSet (L.finiteLocalLatticeStabilizerSubgroup :
      Set L.ConcreteFiniteAdelicOrthogonalGroup) :=
  L.isOpen_finiteLocalLatticeStabilizerSubgroup.measurableSet

/-- The finite local lattice stabilizer is measurable for the inherited Borel
measurable space on the concrete finite-adelic orthogonal group. -/
theorem measurableSet_finiteLocalLatticeStabilizerSubgroup_borel
    (L : PositiveDefiniteIntegralLattice n) :
    @MeasurableSet L.ConcreteFiniteAdelicOrthogonalGroup
      (borel L.ConcreteFiniteAdelicOrthogonalGroup)
      L.finiteLocalLatticeStabilizerSubgroup := by
  letI : MeasurableSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
    borel L.ConcreteFiniteAdelicOrthogonalGroup
  letI : BorelSpace L.ConcreteFiniteAdelicOrthogonalGroup := ⟨rfl⟩
  exact L.measurableSet_finiteLocalLatticeStabilizerSubgroup

/-! ## Concrete normalized Haar measures -/

/-- The compact-open finite local stabilizer, bundled as the normalization set
for Haar measure on the concrete finite-adelic orthogonal group. -/
def finiteLocalLatticeStabilizerPositiveCompacts (L : PositiveDefiniteIntegralLattice n) :
    PositiveCompacts L.ConcreteFiniteAdelicOrthogonalGroup where
  carrier := L.finiteLocalLatticeStabilizerSubgroup
  isCompact' := L.isCompact_finiteLocalLatticeStabilizerSubgroup
  interior_nonempty' := by
    rw [L.isOpen_finiteLocalLatticeStabilizerSubgroup.interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩

/-- The compact neighborhood `H_f` supplies local compactness of the concrete
finite-adelic orthogonal group. -/
instance concreteFiniteAdelicOrthogonalGroupLocallyCompactSpace
    (L : PositiveDefiniteIntegralLattice n) :
    LocallyCompactSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
  L.finiteLocalLatticeStabilizerPositiveCompacts.locallyCompactSpace_of_group

/-- The locally compact, second-countable concrete orthogonal group is Polish.
We use its right uniformity, which is complete by local compactness. -/
noncomputable instance concreteFiniteAdelicOrthogonalGroupPolishSpace
    (L : PositiveDefiniteIntegralLattice n) :
    PolishSpace L.ConcreteFiniteAdelicOrthogonalGroup := by
  letI : UniformSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
    IsTopologicalGroup.rightUniformSpace _
  letI : IsRightUniformGroup L.ConcreteFiniteAdelicOrthogonalGroup := ⟨rfl⟩
  letI : FirstCountableTopology L.ConcreteFiniteAdelicOrthogonalGroup :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  letI : CompleteSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
    IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (𝓤 L.ConcreteFiniteAdelicOrthogonalGroup).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one' L.ConcreteFiniteAdelicOrthogonalGroup]
    exact Filter.comap.isCountablyGenerated _ _
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space (Matrix (Fin n) (Fin n) RationalFiniteAdele) := inferInstance
  letI : T2Space (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
    Units.isEmbedding_embedProduct.t2Space
  letI : T2Space L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.isClosed_finiteAdelicOrthogonalMatrixSubgroup
      |>.isClosedEmbedding_subtypeVal.isEmbedding.t2Space
  letI : T1Space L.ConcreteFiniteAdelicOrthogonalGroup := T2Space.t1Space
  letI : T0Space L.ConcreteFiniteAdelicOrthogonalGroup := T1Space.t0Space
  letI : TopologicalSpace.IsCompletelyMetrizableSpace
      L.ConcreteFiniteAdelicOrthogonalGroup :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
  exact {}

/-- The inherited Borel structure on the concrete orthogonal group is
standard Borel. -/
noncomputable instance concreteFiniteAdelicOrthogonalGroupStandardBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    StandardBorelSpace L.ConcreteFiniteAdelicOrthogonalGroup where
  polish :=
    ⟨(inferInstance : TopologicalSpace L.ConcreteFiniteAdelicOrthogonalGroup),
      L.concreteFiniteAdelicOrthogonalGroupBorelSpace,
      L.concreteFiniteAdelicOrthogonalGroupPolishSpace⟩

/-- The finite local lattice stabilizer, with its default subtype measurable
space, is standard Borel. -/
noncomputable instance concreteFiniteLocalLatticeStabilizerStandardBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    StandardBorelSpace L.finiteLocalLatticeStabilizerSubgroup := by
  letI : StandardBorelSpace L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.concreteFiniteAdelicOrthogonalGroupStandardBorelSpace
  exact L.measurableSet_finiteLocalLatticeStabilizerSubgroup.standardBorel

/-- Haar measure on the concrete finite-adelic orthogonal group, normalized so
that the finite local stabilizer has mass one. -/
noncomputable def concreteFiniteAdelicOrthogonalHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.ConcreteFiniteAdelicOrthogonalGroup :=
  Measure.haarMeasure L.finiteLocalLatticeStabilizerPositiveCompacts

instance concreteFiniteAdelicOrthogonalHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant L.concreteFiniteAdelicOrthogonalHaarMeasure := by
  unfold concreteFiniteAdelicOrthogonalHaarMeasure
  infer_instance

/-- The normalized ambient Haar measure gives the concrete finite local
stabilizer mass one. -/
theorem concreteFiniteAdelicOrthogonalHaarMeasure_stabilizer
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteFiniteAdelicOrthogonalHaarMeasure
        L.finiteLocalLatticeStabilizerSubgroup = 1 := by
  exact Measure.haarMeasure_self

/-- The concrete subgroup Haar measure is the ambient Haar measure transported
through the default subtype inclusion. -/
noncomputable def concreteFiniteLocalLatticeStabilizerHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.finiteLocalLatticeStabilizerSubgroup :=
  Measure.comap
    (fun h : L.finiteLocalLatticeStabilizerSubgroup =>
      (h : L.ConcreteFiniteAdelicOrthogonalGroup))
    L.concreteFiniteAdelicOrthogonalHaarMeasure

/-- The concrete subgroup Haar measure is definitionally the comap of the
normalized ambient Haar measure. -/
theorem concreteFiniteLocalLatticeStabilizerHaarMeasure_eq_comap
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteFiniteLocalLatticeStabilizerHaarMeasure =
      Measure.comap
        (fun h : L.finiteLocalLatticeStabilizerSubgroup =>
          (h : L.ConcreteFiniteAdelicOrthogonalGroup))
        L.concreteFiniteAdelicOrthogonalHaarMeasure :=
  rfl

/-- The concrete finite local stabilizer uses the ordinary subtype measurable
space inherited from the concrete ambient group. -/
theorem concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
    (L : PositiveDefiniteIntegralLattice n) :
    (inferInstance : MeasurableSpace L.finiteLocalLatticeStabilizerSubgroup) =
      (@Subtype.instMeasurableSpace L.ConcreteFiniteAdelicOrthogonalGroup
        (fun x => x ∈ L.finiteLocalLatticeStabilizerSubgroup)
        (borel L.ConcreteFiniteAdelicOrthogonalGroup)) :=
  rfl

/-- The concrete subgroup comap measure pushes forward to ambient Haar measure
restricted to the finite local stabilizer. -/
theorem concreteFiniteLocalLatticeStabilizerHaarMeasure_map_eq_restrict
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.map
        (fun h : L.finiteLocalLatticeStabilizerSubgroup =>
          (h : L.ConcreteFiniteAdelicOrthogonalGroup))
        L.concreteFiniteLocalLatticeStabilizerHaarMeasure =
      L.concreteFiniteAdelicOrthogonalHaarMeasure.restrict
        (L.finiteLocalLatticeStabilizerSubgroup :
          Set L.ConcreteFiniteAdelicOrthogonalGroup) := by
  exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
    L.measurableSet_finiteLocalLatticeStabilizerSubgroup

/-- The concrete subgroup Haar measure has total mass one. -/
theorem concreteFiniteLocalLatticeStabilizerHaarMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteFiniteLocalLatticeStabilizerHaarMeasure Set.univ = 1 := by
  change (Measure.comap
    (fun h : L.finiteLocalLatticeStabilizerSubgroup =>
      (h : L.ConcreteFiniteAdelicOrthogonalGroup))
    L.concreteFiniteAdelicOrthogonalHaarMeasure) Set.univ = 1
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
    L.measurableSet_finiteLocalLatticeStabilizerSubgroup]
  exact L.concreteFiniteAdelicOrthogonalHaarMeasure_stabilizer

instance concreteFiniteLocalLatticeStabilizerHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure := by
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
    L.measurableSet_finiteLocalLatticeStabilizerSubgroup

/-! ## Concrete finite local stabilizer selectors -/

/-- The concrete `embeddingReal` transversal for
`H_f ∩ g⁻¹ O(V)(ℚ) g` acting on `H_f` by left multiplication. -/
noncomputable def concreteLocalRightStabilizerEmbeddingRealSlice
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Set L.finiteLocalLatticeStabilizerSubgroup :=
  finiteSubgroupEmbeddingRealSlice
    (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- Every concrete local `embeddingReal` slice is measurable in `H_f`. -/
theorem concreteLocalRightStabilizerEmbeddingRealSlice_measurableSet
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    MeasurableSet (L.concreteLocalRightStabilizerEmbeddingRealSlice g) := by
  letI : Finite
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    L.finite_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g
  letI : Fintype
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Fintype.ofFinite _
  exact finiteSubgroupEmbeddingRealSlice_measurableSet
    (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g)
    (fun gamma => measurable_const_mul
      (gamma : L.finiteLocalLatticeStabilizerSubgroup))

/-- Every concrete local `embeddingReal` slice is a left-coset transversal for
the corresponding finite stabilizer inside `H_f`. -/
theorem concreteLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    IsLeftCosetTransversal
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g)
      (L.concreteLocalRightStabilizerEmbeddingRealSlice g) := by
  letI : Finite
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    L.finite_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g
  letI : Fintype
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Fintype.ofFinite _
  exact finiteSubgroupEmbeddingRealSlice_isLeftCosetTransversal
    (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- The normalized concrete subgroup Haar measure of a local selector is the
reciprocal cardinality of its finite local right stabilizer. -/
theorem concreteLocalRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteFiniteLocalLatticeStabilizerHaarMeasure
        (L.concreteLocalRightStabilizerEmbeddingRealSlice g) =
      ENNReal.ofReal
        (1 / (Nat.card
          (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) : ℝ)) := by
  letI : Finite
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    L.finite_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g
  letI : Fintype
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Fintype.ofFinite _
  letI : Measure.IsMulLeftInvariant
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure :=
    concreteFiniteLocalLatticeStabilizerHaarMeasure_isMulLeftInvariant L
  have hμ_univ :
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure Set.univ =
        ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure_univ
  exact finiteSubgroupEmbeddingRealSlice_measure_eq_inv_natCard
    (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g)
    (μ := L.concreteFiniteLocalLatticeStabilizerHaarMeasure)
    hμ_univ

/-! ## Concrete rational left quotient -/

/-- The concrete rational left quotient
`O(V)(ℚ) \ O(V)(𝔸_f)` attached to `L`. -/
abbrev ConcreteRationalLeftQuotient (L : PositiveDefiniteIntegralLattice n) :=
  leftCosetSet L.rationalOrthogonalDiagonalSubgroup

/-- The canonical projection from the concrete finite-adelic orthogonal group
to its rational left quotient. -/
def concreteRationalLeftQuotientMap (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFiniteAdelicOrthogonalGroup → L.ConcreteRationalLeftQuotient :=
  leftCosetMap L.rationalOrthogonalDiagonalSubgroup

/-- The concrete rational quotient carries the measurable structure generated
by its quotient map from the inherited ambient Borel structure. -/
instance concreteRationalLeftQuotientMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteRationalLeftQuotient :=
  MeasurableSpace.map L.concreteRationalLeftQuotientMap
    (borel L.ConcreteFiniteAdelicOrthogonalGroup)

/-- The selected measurable structure on the concrete rational quotient is
exactly the map measurable structure. -/
theorem concreteRationalLeftQuotientMeasurableSpace_eq_map
    (L : PositiveDefiniteIntegralLattice n) :
    (inferInstance : MeasurableSpace L.ConcreteRationalLeftQuotient) =
      MeasurableSpace.map L.concreteRationalLeftQuotientMap
        (borel L.ConcreteFiniteAdelicOrthogonalGroup) :=
  rfl

/-- The canonical concrete rational quotient map is measurable for the map
measurable structure. -/
theorem concreteRationalLeftQuotientMap_measurable
    (L : PositiveDefiniteIntegralLattice n) :
    Measurable L.concreteRationalLeftQuotientMap := by
  exact leftCosetMap_measurable_map L.rationalOrthogonalDiagonalSubgroup

/-- The concrete rational quotient measure obtained by restricting normalized
ambient Haar measure to a fundamental-domain candidate and pushing it forward
along the quotient map. -/
noncomputable def concreteRationalLeftQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) :
    Measure L.ConcreteRationalLeftQuotient :=
  leftQuotientFundamentalDomainMeasure
    L.rationalOrthogonalDiagonalSubgroup
    L.concreteFiniteAdelicOrthogonalHaarMeasure F

/-- The concrete quotient measure is the pushforward of restricted normalized
ambient Haar measure. -/
theorem concreteRationalLeftQuotientMeasure_eq_map_restrict
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteRationalLeftQuotientMeasure F =
      Measure.map L.concreteRationalLeftQuotientMap
        (L.concreteFiniteAdelicOrthogonalHaarMeasure.restrict F) :=
  rfl

/-- Setwise evaluation of the concrete quotient measure on measurable sets. -/
theorem concreteRationalLeftQuotientMeasure_apply
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    {A : Set L.ConcreteRationalLeftQuotient} (hA : MeasurableSet A) :
    L.concreteRationalLeftQuotientMeasure F A =
      L.concreteFiniteAdelicOrthogonalHaarMeasure
        (F ∩ L.concreteRationalLeftQuotientMap ⁻¹' A) := by
  exact leftQuotientFundamentalDomainMeasure_apply_map_mspace
    L.concreteRationalLeftQuotientMeasurableSpace_eq_map hA

/-- The total concrete quotient mass is the normalized ambient Haar volume of
the chosen fundamental-domain candidate. -/
theorem concreteRationalLeftQuotientMeasure_univ
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteRationalLeftQuotientMeasure F Set.univ =
      L.concreteFiniteAdelicOrthogonalHaarMeasure F := by
  exact leftQuotientFundamentalDomainMeasure_univ_map_mspace
    L.concreteRationalLeftQuotientMeasurableSpace_eq_map

/-- Real-valued total-mass form of the concrete quotient normalization. -/
theorem concreteRationalLeftQuotientMeasure_univ_toReal
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteRationalLeftQuotientMeasure F Set.univ).toReal =
      (L.concreteFiniteAdelicOrthogonalHaarMeasure F).toReal := by
  exact leftQuotientFundamentalDomainMeasure_univ_toReal_map_mspace
    L.concreteRationalLeftQuotientMeasurableSpace_eq_map

/-! ## Concrete rational double quotient and selected fibers -/

/-- The concrete rational/local-stabilizer double quotient
`O(V)(ℚ) \ O(V)(𝔸_f) / H_f`. -/
abbrev ConcreteRationalDoubleCosetSet (L : PositiveDefiniteIntegralLattice n) :=
  leftRightDoubleCosetSet L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup

/-- The canonical projection from the concrete rational left quotient to the
concrete rational/local-stabilizer double quotient. -/
def concreteRationalLeftQuotientToDoubleCoset (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteRationalLeftQuotient → L.ConcreteRationalDoubleCosetSet :=
  leftCosetToLeftRightDoubleCoset L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup

/-- The concrete double quotient carries the map measurable structure from
the concrete rational left quotient. -/
instance concreteRationalDoubleCosetMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteRationalDoubleCosetSet :=
  MeasurableSpace.map L.concreteRationalLeftQuotientToDoubleCoset
    (inferInstance : MeasurableSpace L.ConcreteRationalLeftQuotient)

theorem concreteRationalDoubleCosetMeasurableSpace_eq_map
    (L : PositiveDefiniteIntegralLattice n) :
    (inferInstance : MeasurableSpace L.ConcreteRationalDoubleCosetSet) =
      MeasurableSpace.map L.concreteRationalLeftQuotientToDoubleCoset
        (inferInstance : MeasurableSpace L.ConcreteRationalLeftQuotient) :=
  rfl

/-- The concrete left-to-double-quotient projection is measurable for the map
measurable structure. -/
theorem concreteRationalLeftQuotientToDoubleCoset_measurable
    (L : PositiveDefiniteIntegralLattice n) :
    Measurable L.concreteRationalLeftQuotientToDoubleCoset := by
  exact leftCosetToLeftRightDoubleCoset_measurable_map
    L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup

/-- A right translate of concrete compact-open `H_f` is open. -/
theorem isOpen_finiteLocalLatticeStabilizer_rightTranslate
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    IsOpen
      (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup g Set.univ) := by
  rw [rightTranslateSliceSet_eq_image]
  have hset :
      (fun h : L.finiteLocalLatticeStabilizerSubgroup =>
          g * (h : L.ConcreteFiniteAdelicOrthogonalGroup)) '' Set.univ =
        (fun x : L.ConcreteFiniteAdelicOrthogonalGroup => g * x) ''
          (L.finiteLocalLatticeStabilizerSubgroup :
            Set L.ConcreteFiniteAdelicOrthogonalGroup) := by
    ext x
    constructor
    · rintro ⟨h, _hh, rfl⟩
      exact ⟨h, h.property, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, Set.mem_univ _, rfl⟩
  rw [hset]
  exact (isOpenMap_mul_left g)
    (L.finiteLocalLatticeStabilizerSubgroup :
      Set L.ConcreteFiniteAdelicOrthogonalGroup)
    L.isOpen_finiteLocalLatticeStabilizerSubgroup

/-- Every strict concrete double coset is open in the finite-adelic ambient
group.  No countability of the rational subgroup is needed because arbitrary
unions of open left translates are open. -/
theorem isOpen_rationalOrthogonal_doubleCoset
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    IsOpen {y : L.ConcreteFiniteAdelicOrthogonalGroup |
      ∃ gamma : L.rationalOrthogonalDiagonalSubgroup,
        ∃ h : L.finiteLocalLatticeStabilizerSubgroup,
          y = (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
            (h : L.ConcreteFiniteAdelicOrthogonalGroup)} := by
  have hslice := L.isOpen_finiteLocalLatticeStabilizer_rightTranslate g
  have hsat : IsOpen
      (leftSubgroupSaturation L.rationalOrthogonalDiagonalSubgroup
        (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
          g Set.univ)) := by
    rw [leftSubgroupSaturation_eq_iUnion_image]
    exact isOpen_iUnion fun gamma =>
      (isOpenMap_mul_left
        (gamma : L.ConcreteFiniteAdelicOrthogonalGroup)) _ hslice
  convert hsat using 1
  ext y
  simp only [leftSubgroupSaturation, rightTranslateSliceSet, Set.mem_setOf_eq,
    Set.mem_univ, true_and]
  constructor
  · rintro ⟨gamma, h, rfl⟩
    exact ⟨gamma, g * (h : L.ConcreteFiniteAdelicOrthogonalGroup),
      ⟨h, rfl⟩, by simp [mul_assoc]⟩
  · rintro ⟨gamma, x, ⟨h, rfl⟩, rfl⟩
    exact ⟨gamma, h, by simp [mul_assoc]⟩

/-- Every selected concrete double-coset fiber is measurable in the rational
left quotient.  Its ambient preimage is an open strict double coset. -/
theorem measurableSet_concreteRationalDoubleCosetPiece
    (L : PositiveDefiniteIntegralLattice n) (C : L.ConcreteRationalDoubleCosetSet) :
    MeasurableSet
      (leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C) := by
  change MeasurableSet
    (L.concreteRationalLeftQuotientMap ⁻¹'
      leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C)
  simp only [concreteRationalLeftQuotientMap]
  rw [← Quot.out_eq C,
    leftCosetMap_preimage_leftRightDoubleCosetPieceSet_mk]
  exact (L.isOpen_rationalOrthogonal_doubleCoset (Quot.out C)).measurableSet

/-- Singletons are measurable in the concrete double quotient because their
preimages are the measurable selected fibers. -/
instance concreteRationalDoubleCosetMeasurableSingletonClass
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSingletonClass L.ConcreteRationalDoubleCosetSet where
  measurableSet_singleton C := by
    change MeasurableSet
      (L.concreteRationalLeftQuotientToDoubleCoset ⁻¹'
        ({C} : Set L.ConcreteRationalDoubleCosetSet))
    change MeasurableSet
      (leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C)
    exact L.measurableSet_concreteRationalDoubleCosetPiece C

/-- The selected fiber in the concrete rational left quotient over one
concrete double coset. -/
abbrev ConcreteRationalDoubleCosetQuotientPiece
    (L : PositiveDefiniteIntegralLattice n) (C : L.ConcreteRationalDoubleCosetSet) :=
  leftRightDoubleCosetPiece L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup C

/-- Concrete selected fibers use the ordinary subtype measurable space from
the rational left quotient. -/
instance concreteRationalDoubleCosetQuotientPieceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (C : L.ConcreteRationalDoubleCosetSet) :
    MeasurableSpace (L.ConcreteRationalDoubleCosetQuotientPiece C) := by
  change MeasurableSpace
    {X : L.ConcreteRationalLeftQuotient //
      L.concreteRationalLeftQuotientToDoubleCoset X = C}
  exact Subtype.instMeasurableSpace

theorem concreteRationalDoubleCosetQuotientPieceMeasurableSpace_eq_subtype
    (L : PositiveDefiniteIntegralLattice n) (C : L.ConcreteRationalDoubleCosetSet) :
    (inferInstance :
      MeasurableSpace (L.ConcreteRationalDoubleCosetQuotientPiece C)) =
      (@Subtype.instMeasurableSpace L.ConcreteRationalLeftQuotient
        (fun X => L.concreteRationalLeftQuotientToDoubleCoset X = C)
        (inferInstance : MeasurableSpace L.ConcreteRationalLeftQuotient)) :=
  rfl

/-- The concrete selected right-`H_f` orbit map is measurable for the inherited
subgroup, map-quotient, and selected-fiber subtype measurable spaces. -/
theorem concreteRationalRightOrbitToDoubleCosetPiece_measurable
    (L : PositiveDefiniteIntegralLattice n) (C : L.ConcreteRationalDoubleCosetSet) :
    Measurable
      (rightOrbitToLeftRightDoubleCosetPiece
        L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C) := by
  exact
    rightOrbitToLeftRightDoubleCosetPiece_measurable_of_map_subtype_mspace
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup C
      L.measurableSet_finiteLocalLatticeStabilizerSubgroup
      L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
      L.concreteRationalLeftQuotientMeasurableSpace_eq_map
      (L.concreteRationalDoubleCosetQuotientPieceMeasurableSpace_eq_subtype C)

/-- The concrete selected-fiber measure is the comap of the rational quotient
measure along the fiber value map. -/
noncomputable def concreteRationalDoubleCosetPieceQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (C : L.ConcreteRationalDoubleCosetSet) :
    Measure (L.ConcreteRationalDoubleCosetQuotientPiece C) :=
  Measure.comap
    (fun X : L.ConcreteRationalDoubleCosetQuotientPiece C => X.1)
    (L.concreteRationalLeftQuotientMeasure F)

theorem concreteRationalDoubleCosetPieceQuotientMeasure_eq_comap
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (C : L.ConcreteRationalDoubleCosetSet) :
    L.concreteRationalDoubleCosetPieceQuotientMeasure F C =
      Measure.comap
        (fun X : L.ConcreteRationalDoubleCosetQuotientPiece C => X.1)
        (L.concreteRationalLeftQuotientMeasure F) :=
  rfl

/-- The selected-fiber comap measure pushes forward to the rational quotient
measure restricted to that fiber. -/
theorem concreteRationalDoubleCosetPieceQuotientMeasure_map_eq_restrict
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (C : L.ConcreteRationalDoubleCosetSet) :
    Measure.map
        (fun X : L.ConcreteRationalDoubleCosetQuotientPiece C => X.1)
        (L.concreteRationalDoubleCosetPieceQuotientMeasure F C) =
      (L.concreteRationalLeftQuotientMeasure F).restrict
        (leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) := by
  have hmap := subtype_comap_measure_map_eq_restrict_of_subtype_mspace
    (μα := L.concreteRationalLeftQuotientMeasure F)
    (p := fun X : L.ConcreteRationalLeftQuotient =>
      L.concreteRationalLeftQuotientToDoubleCoset X = C)
    rfl (L.measurableSet_concreteRationalDoubleCosetPiece C)
  simpa [concreteRationalDoubleCosetPieceQuotientMeasure,
    leftRightDoubleCosetPieceSet, subtype_val_range] using hmap

/-- The total selected-fiber mass is the rational quotient measure of the
corresponding double-coset fiber. -/
theorem concreteRationalDoubleCosetPieceQuotientMeasure_univ
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (C : L.ConcreteRationalDoubleCosetSet) :
    L.concreteRationalDoubleCosetPieceQuotientMeasure F C Set.univ =
      L.concreteRationalLeftQuotientMeasure F
        (leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) := by
  have hrange := subtype_comap_measure_range_eq_univ_of_subtype_mspace
    (μα := L.concreteRationalLeftQuotientMeasure F)
    (p := fun X : L.ConcreteRationalLeftQuotient =>
      L.concreteRationalLeftQuotientToDoubleCoset X = C)
    rfl (L.measurableSet_concreteRationalDoubleCosetPiece C)
  simpa [concreteRationalDoubleCosetPieceQuotientMeasure,
    leftRightDoubleCosetPieceSet, subtype_val_range] using hrange.symm

/-- Real-valued form of the concrete selected-fiber total-mass identity. -/
theorem concreteRationalDoubleCosetPieceQuotientMeasure_univ_toReal
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (C : L.ConcreteRationalDoubleCosetSet) :
    (L.concreteRationalDoubleCosetPieceQuotientMeasure F C Set.univ).toReal =
      (L.concreteRationalLeftQuotientMeasure F
        (leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C)).toReal := by
  rw [L.concreteRationalDoubleCosetPieceQuotientMeasure_univ F C]

/-! ## Concrete rational quotient real volumes -/

/-- The concrete finite-adelic quotient volume attached to a domain candidate
is the real total mass of its rational left-quotient measure. -/
noncomputable def concreteFiniteAdelicQuotientVolume
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) : ℝ :=
  (L.concreteRationalLeftQuotientMeasure F Set.univ).toReal

/-- The concrete quotient volume is the real ambient Haar mass of the domain
candidate. -/
theorem concreteFiniteAdelicQuotientVolume_eq_ambient
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteFiniteAdelicQuotientVolume F =
      (L.concreteFiniteAdelicOrthogonalHaarMeasure F).toReal := by
  simpa [concreteFiniteAdelicQuotientVolume] using
    L.concreteRationalLeftQuotientMeasure_univ_toReal F

theorem concreteFiniteAdelicQuotientVolume_nonneg
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup) :
    0 ≤ L.concreteFiniteAdelicQuotientVolume F :=
  ENNReal.toReal_nonneg

/-- The concrete quotient-piece volume over a raw representative is the real
total mass of the corresponding selected-fiber comap measure. -/
noncomputable def concreteDoubleCosetPieceQuotientVolume
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) : ℝ :=
  (L.concreteRationalDoubleCosetPieceQuotientMeasure F
    (Quot.mk
      (leftRightDoubleCosetSetoid L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup) g) Set.univ).toReal

theorem concreteDoubleCosetPieceQuotientVolume_nonneg
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    0 ≤ L.concreteDoubleCosetPieceQuotientVolume F g :=
  ENNReal.toReal_nonneg

/-- If the candidate domain has finite ambient Haar mass, every selected-fiber
measure is recovered from its concrete real volume by `ENNReal.ofReal`. -/
theorem concreteDoubleCosetPieceQuotientMeasure_univ_eq_ofReal
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (hF : L.concreteFiniteAdelicOrthogonalHaarMeasure F ≠ ∞)
    (C : L.ConcreteRationalDoubleCosetSet) :
    L.concreteRationalDoubleCosetPieceQuotientMeasure F C Set.univ =
      ENNReal.ofReal
        (L.concreteDoubleCosetPieceQuotientVolume F (Quot.out C)) := by
  have hpiece_le :
      L.concreteRationalDoubleCosetPieceQuotientMeasure F C Set.univ ≤
        L.concreteRationalLeftQuotientMeasure F Set.univ := by
    rw [L.concreteRationalDoubleCosetPieceQuotientMeasure_univ F C]
    exact measure_mono (Set.subset_univ _)
  have htotal_ne :
      L.concreteRationalLeftQuotientMeasure F Set.univ ≠ ∞ := by
    rw [L.concreteRationalLeftQuotientMeasure_univ F]
    exact hF
  have hpiece_ne :
      L.concreteRationalDoubleCosetPieceQuotientMeasure F C Set.univ ≠ ∞ :=
    ne_top_of_le_ne_top htotal_ne hpiece_le
  rw [concreteDoubleCosetPieceQuotientVolume, Quot.out_eq C]
  exact (ENNReal.ofReal_toReal hpiece_ne).symm

/-- Conditional only on finiteness of the candidate domain and an explicitly
supplied finite double quotient, the concrete quotient volume is the finite
sum of the concrete selected-piece volumes. -/
theorem concreteFiniteAdelicQuotientVolume_eq_doubleCosetPieceQuotientVolumeSum
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (hF : L.concreteFiniteAdelicOrthogonalHaarMeasure F ≠ ∞)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet) :
    L.concreteFiniteAdelicQuotientVolume F =
      @Finset.sum L.ConcreteRationalDoubleCosetSet ℝ _
        (@Finset.univ L.ConcreteRationalDoubleCosetSet inst)
        (fun C =>
          L.concreteDoubleCosetPieceQuotientVolume F (Quot.out C)) := by
  letI : Fintype L.ConcreteRationalDoubleCosetSet := inst
  exact leftRightDoubleCosetPieceSet_measure_univ_toReal_eq_sum
    L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup
    (L.concreteRationalLeftQuotientMeasure F)
    (fun C =>
      L.concreteDoubleCosetPieceQuotientVolume F (Quot.out C))
    L.measurableSet_concreteRationalDoubleCosetPiece
    (fun C => L.concreteDoubleCosetPieceQuotientVolume_nonneg F (Quot.out C))
    (fun C => by
      rw [← L.concreteRationalDoubleCosetPieceQuotientMeasure_univ F C]
      exact L.concreteDoubleCosetPieceQuotientMeasure_univ_eq_ofReal F hF C)

/-- The concrete finite-transversal domain obtained by choosing the canonical
representative of every rational double coset and the `embeddingReal` slice of
its finite local right stabilizer. -/
noncomputable def concreteFiniteTransversalFundamentalDomain
    (L : PositiveDefiniteIntegralLattice n) :
    Set L.ConcreteFiniteAdelicOrthogonalGroup :=
  finiteRightTransversalFundamentalDomain
    L.finiteLocalLatticeStabilizerSubgroup
    (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C)
    (fun C : L.ConcreteRationalDoubleCosetSet =>
      L.concreteLocalRightStabilizerEmbeddingRealSlice (Quot.out C))

theorem concreteLocalRightStabilizer_conjugates
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (s : L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :
    ∃ gamma : L.rationalOrthogonalDiagonalSubgroup,
      (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g =
        g * ((s : L.finiteLocalLatticeStabilizerSubgroup) :
          L.ConcreteFiniteAdelicOrthogonalGroup) := by
  have hs := (L.mem_concreteLocalRightStabilizerSubgroup_iff g s.1.1).mp s.2
  rcases hs.2 with ⟨q, hq⟩
  refine ⟨⟨L.rationalOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩, ?_⟩
  rw [hq]
  simp [mul_assoc]

theorem concreteFiniteTransversalFundamentalDomain_measurableSet
    (L : PositiveDefiniteIntegralLattice n)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet) :
    MeasurableSet L.concreteFiniteTransversalFundamentalDomain := by
  letI : Fintype L.ConcreteRationalDoubleCosetSet := inst
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
  exact finiteRightTransversalFundamentalDomain_measurableSet_of_subgroup_comap
    L.finiteLocalLatticeStabilizerSubgroup
    (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C)
    (fun C : L.ConcreteRationalDoubleCosetSet =>
      L.concreteLocalRightStabilizerEmbeddingRealSlice (Quot.out C))
    hsub_comap L.measurableSet_finiteLocalLatticeStabilizerSubgroup
    (fun C =>
      L.concreteLocalRightStabilizerEmbeddingRealSlice_measurableSet (Quot.out C))

set_option synthInstance.maxHeartbeats 100000 in
theorem concreteFiniteTransversalFundamentalDomain_isFundamentalDomain
    (L : PositiveDefiniteIntegralLattice n)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet) :
    IsFundamentalDomain L.rationalOrthogonalDiagonalSubgroup
      L.concreteFiniteTransversalFundamentalDomain
      L.concreteFiniteAdelicOrthogonalHaarMeasure := by
  letI : Fintype L.ConcreteRationalDoubleCosetSet := inst
  let slice : L.ConcreteRationalDoubleCosetSet →
      Set L.finiteLocalLatticeStabilizerSubgroup := fun C =>
    L.concreteLocalRightStabilizerEmbeddingRealSlice (Quot.out C)
  have htrans : ∀ C : L.ConcreteRationalDoubleCosetSet,
      IsLeftCosetTransversal
        (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer (Quot.out C))
        (slice C) := fun C =>
    L.concreteLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
      (Quot.out C)
  have hlocal : ∀ C : L.ConcreteRationalDoubleCosetSet,
      ∀ h : L.finiteLocalLatticeStabilizerSubgroup,
        ∃ gamma : L.rationalOrthogonalDiagonalSubgroup,
          ∃ c : L.finiteLocalLatticeStabilizerSubgroup,
            c ∈ slice C ∧
              (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) *
                  (Quot.out C *
                    (h : L.ConcreteFiniteAdelicOrthogonalGroup)) =
                Quot.out C * (c : L.ConcreteFiniteAdelicOrthogonalGroup) := by
    intro C
    exact local_right_cover_of_stabilizer_transversal
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup (Quot.out C)
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer (Quot.out C))
      (slice C)
      (L.concreteLocalRightStabilizer_conjugates (Quot.out C))
      (htrans C).decomp
  have hcover := finiteRightTransversalFundamentalDomain_cover_of_local_right_cover
    L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup
    (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C)
    (fun C => Quot.out_eq C) slice hlocal
  have hlocal_unique : ∀ (C : L.ConcreteRationalDoubleCosetSet)
      (h₁ h₂ : L.finiteLocalLatticeStabilizerSubgroup),
      h₁ ∈ slice C → h₂ ∈ slice C →
      (∃ gamma : L.rationalOrthogonalDiagonalSubgroup,
        (((h₂ * h₁⁻¹ : L.finiteLocalLatticeStabilizerSubgroup) :
            L.ConcreteFiniteAdelicOrthogonalGroup) =
          (Quot.out C)⁻¹ *
            (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * Quot.out C)) →
      h₂ = h₁ := by
    intro C h₁ h₂ hh₁ hh₂ hstab
    apply (htrans C).unique h₁ h₂ hh₁ hh₂
    rw [L.mem_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer_iff]
    apply (L.mem_concreteLocalRightStabilizerSubgroup_iff
      (Quot.out C) ((h₂ * h₁⁻¹ : L.finiteLocalLatticeStabilizerSubgroup) :
        L.ConcreteFiniteAdelicOrthogonalGroup)).2
    refine ⟨(h₂ * h₁⁻¹).property, ?_⟩
    rcases hstab with ⟨gamma, hgamma⟩
    rcases gamma.2 with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hq]
    exact hgamma
  have hgamma_unique :=
    finiteRightTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup
      (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C) slice hlocal_unique
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
  exact finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_cover_unique_witness
    L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup
    (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C) slice
    hsub_comap L.measurableSet_finiteLocalLatticeStabilizerSubgroup
    (fun C =>
      L.concreteLocalRightStabilizerEmbeddingRealSlice_measurableSet (Quot.out C))
    hcover hgamma_unique

theorem concreteFiniteTransversalFundamentalDomain_measure_eq_sum
    (L : PositiveDefiniteIntegralLattice n)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet) :
    L.concreteFiniteAdelicOrthogonalHaarMeasure
        L.concreteFiniteTransversalFundamentalDomain =
      @Finset.sum L.ConcreteRationalDoubleCosetSet ℝ≥0∞ _
        (@Finset.univ L.ConcreteRationalDoubleCosetSet inst)
        (fun C => ENNReal.ofReal
          (1 / (Nat.card
            (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer
              (Quot.out C)) : ℝ))) := by
  letI : Fintype L.ConcreteRationalDoubleCosetSet := inst
  let slice : L.ConcreteRationalDoubleCosetSet →
      Set L.finiteLocalLatticeStabilizerSubgroup := fun C =>
    L.concreteLocalRightStabilizerEmbeddingRealSlice (Quot.out C)
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
  have hdisj :=
    rightTranslateSliceSet_pairwiseDisjoint_of_leftRightDoubleCosetRepresentatives
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup
      (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C) slice
  calc
    L.concreteFiniteAdelicOrthogonalHaarMeasure
        L.concreteFiniteTransversalFundamentalDomain =
        ∑ C : L.ConcreteRationalDoubleCosetSet,
          L.concreteFiniteLocalLatticeStabilizerHaarMeasure (slice C) := by
      exact finiteRightTransversalFundamentalDomain_measure_eq_sum_subgroupHaar
        L.finiteLocalLatticeStabilizerSubgroup
        (fun C : L.ConcreteRationalDoubleCosetSet => Quot.out C) slice
        hsub_comap L.measurableSet_finiteLocalLatticeStabilizerSubgroup
        L.concreteFiniteLocalLatticeStabilizerHaarMeasure_map_eq_restrict
        (fun C =>
          L.concreteLocalRightStabilizerEmbeddingRealSlice_measurableSet (Quot.out C))
        hdisj
    _ = ∑ C : L.ConcreteRationalDoubleCosetSet,
          ENNReal.ofReal
            (1 / (Nat.card
              (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer
                (Quot.out C)) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro C _
      exact L.concreteLocalRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard
        (Quot.out C)

theorem concreteFiniteTransversalFundamentalDomain_measure_ne_top
    (L : PositiveDefiniteIntegralLattice n)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet) :
    L.concreteFiniteAdelicOrthogonalHaarMeasure
        L.concreteFiniteTransversalFundamentalDomain ≠ ∞ := by
  rw [L.concreteFiniteTransversalFundamentalDomain_measure_eq_sum inst]
  exact ENNReal.sum_ne_top.2 fun C _ => ENNReal.ofReal_ne_top

theorem concreteFiniteTransversalFundamentalDomain_volume_eq_sum
    (L : PositiveDefiniteIntegralLattice n)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet) :
    L.concreteFiniteAdelicQuotientVolume
        L.concreteFiniteTransversalFundamentalDomain =
      @Finset.sum L.ConcreteRationalDoubleCosetSet ℝ _
        (@Finset.univ L.ConcreteRationalDoubleCosetSet inst)
        (fun C =>
          1 / (Nat.card
            (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer
              (Quot.out C)) : ℝ)) := by
  letI : Fintype L.ConcreteRationalDoubleCosetSet := inst
  let v : L.ConcreteRationalDoubleCosetSet → ℝ := fun C =>
    1 / (Nat.card
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer
        (Quot.out C)) : ℝ)
  have hv_nonneg : ∀ C, 0 ≤ v C := fun C =>
    one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hsum_ofReal :
      ENNReal.ofReal (∑ C : L.ConcreteRationalDoubleCosetSet, v C) =
        ∑ C : L.ConcreteRationalDoubleCosetSet, ENNReal.ofReal (v C) :=
    ENNReal.ofReal_sum_of_nonneg (fun C _ => hv_nonneg C)
  calc
    L.concreteFiniteAdelicQuotientVolume
        L.concreteFiniteTransversalFundamentalDomain =
        (L.concreteFiniteAdelicOrthogonalHaarMeasure
          L.concreteFiniteTransversalFundamentalDomain).toReal :=
      L.concreteFiniteAdelicQuotientVolume_eq_ambient _
    _ = (∑ C : L.ConcreteRationalDoubleCosetSet,
          ENNReal.ofReal (v C)).toReal := by
      rw [L.concreteFiniteTransversalFundamentalDomain_measure_eq_sum inst]
    _ = (ENNReal.ofReal
          (∑ C : L.ConcreteRationalDoubleCosetSet, v C)).toReal := by
      rw [hsum_ofReal]
    _ = ∑ C : L.ConcreteRationalDoubleCosetSet, v C := by
      exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun C _ => hv_nonneg C)

/-! ## Concrete translated-slice periodization -/

/-- Rational elements carrying one point of `gH_f` back into `gH_f` are
equivalent to the concrete local right stabilizer at `g`. -/
noncomputable def concreteRationalElementsSendingRightTranslateEquivLocalRightStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (h₀ : L.finiteLocalLatticeStabilizerSubgroup) :
    { gamma : L.rationalOrthogonalDiagonalSubgroup //
      ∃ h : L.finiteLocalLatticeStabilizerSubgroup,
        (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
            (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup) =
          g * (h : L.ConcreteFiniteAdelicOrthogonalGroup) } ≃
      L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g :=
  Equiv.ofBijective
    (fun gamma => by
      let h : L.finiteLocalLatticeStabilizerSubgroup := Classical.choose gamma.2
      have hgamma :
          (gamma.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
              (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup) =
            g * (h : L.ConcreteFiniteAdelicOrthogonalGroup) :=
        Classical.choose_spec gamma.2
      let x : L.ConcreteFiniteAdelicOrthogonalGroup :=
        g⁻¹ * (gamma.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g
      have hx_eq : x =
          (h : L.ConcreteFiniteAdelicOrthogonalGroup) *
            (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup)⁻¹ := by
        calc
          x = g⁻¹ *
                ((gamma.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
                  (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup)) *
                (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup)⁻¹ := by
              simp [x, mul_assoc]
          _ = g⁻¹ * (g * (h : L.ConcreteFiniteAdelicOrthogonalGroup)) *
                (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup)⁻¹ := by
              rw [hgamma]
          _ = (h : L.ConcreteFiniteAdelicOrthogonalGroup) *
                (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup)⁻¹ := by simp
      have hxH : x ∈ L.finiteLocalLatticeStabilizerSubgroup := by
        rw [hx_eq]
        exact L.finiteLocalLatticeStabilizerSubgroup.mul_mem h.2
          (L.finiteLocalLatticeStabilizerSubgroup.inv_mem h₀.2)
      refine ⟨⟨x, hxH⟩, ?_⟩
      rw [L.mem_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer_iff,
        L.mem_concreteLocalRightStabilizerSubgroup_iff]
      rcases gamma.1.2 with ⟨q, hq⟩
      exact ⟨hxH, q, by rw [hq]⟩)
    (by
      constructor
      · intro gamma₁ gamma₂ hEq
        apply Subtype.ext
        apply Subtype.ext
        have hcarrier :
            g⁻¹ * (gamma₁.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g =
              g⁻¹ * (gamma₂.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g := by
          exact congrArg
            (fun s : L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g =>
              ((s : L.finiteLocalLatticeStabilizerSubgroup) :
                L.ConcreteFiniteAdelicOrthogonalGroup)) hEq
        calc
          (gamma₁.1 : L.ConcreteFiniteAdelicOrthogonalGroup) =
              g * (g⁻¹ * (gamma₁.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g) *
                g⁻¹ := by simp [mul_assoc]
          _ = g * (g⁻¹ * (gamma₂.1 : L.ConcreteFiniteAdelicOrthogonalGroup) * g) *
                g⁻¹ := by rw [hcarrier]
          _ = (gamma₂.1 : L.ConcreteFiniteAdelicOrthogonalGroup) := by
                simp [mul_assoc]
      · intro s
        rcases L.concreteLocalRightStabilizer_conjugates g s with
          ⟨gamma, hgamma⟩
        let gammaWitness :
            { gamma : L.rationalOrthogonalDiagonalSubgroup //
              ∃ h : L.finiteLocalLatticeStabilizerSubgroup,
                (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
                    (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup) =
                  g * (h : L.ConcreteFiniteAdelicOrthogonalGroup) } := by
          refine ⟨gamma, (s : L.finiteLocalLatticeStabilizerSubgroup) * h₀, ?_⟩
          calc
            (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
                (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup) =
                (g * (((s :
                  L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :
                    L.finiteLocalLatticeStabilizerSubgroup) :
                      L.ConcreteFiniteAdelicOrthogonalGroup)) *
                  (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup) := by
                    rw [hgamma]
            _ = g * (((s : L.finiteLocalLatticeStabilizerSubgroup) * h₀ :
                  L.finiteLocalLatticeStabilizerSubgroup) :
                    L.ConcreteFiniteAdelicOrthogonalGroup) := by simp [mul_assoc]
        refine ⟨gammaWitness, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change g⁻¹ * (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g =
          ((s : L.finiteLocalLatticeStabilizerSubgroup) :
            L.ConcreteFiniteAdelicOrthogonalGroup)
        calc
          g⁻¹ * (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g =
              g⁻¹ * ((gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g) := by
                simp [mul_assoc]
          _ = g⁻¹ * (g * ((s : L.finiteLocalLatticeStabilizerSubgroup) :
                L.ConcreteFiniteAdelicOrthogonalGroup)) := by rw [hgamma]
          _ = ((s : L.finiteLocalLatticeStabilizerSubgroup) :
                L.ConcreteFiniteAdelicOrthogonalGroup) := by simp)

theorem finite_concreteRationalElementsSendingRightTranslate
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (h₀ : L.finiteLocalLatticeStabilizerSubgroup) :
    Finite
      { gamma : L.rationalOrthogonalDiagonalSubgroup //
        ∃ h : L.finiteLocalLatticeStabilizerSubgroup,
          (gamma : L.ConcreteFiniteAdelicOrthogonalGroup) * g *
              (h₀ : L.ConcreteFiniteAdelicOrthogonalGroup) =
            g * (h : L.ConcreteFiniteAdelicOrthogonalGroup) } := by
  letI : Finite
      (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    L.finite_concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g
  exact Finite.of_equiv
    (L.concreteLocalRightStabilizerInFiniteLocalLatticeStabilizer g)
    (L.concreteRationalElementsSendingRightTranslateEquivLocalRightStabilizer g h₀).symm

/-- The actual selected-piece periodization of a translated concrete `H_f`
slice, obtained by restricting ambient rational left periodization to the
selected quotient fiber. -/
noncomputable def concreteDoubleCosetPieceTranslatedSlicePeriodize
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteRationalDoubleCosetSet)
    (A : Set L.finiteLocalLatticeStabilizerSubgroup)
    (X : L.ConcreteRationalDoubleCosetQuotientPiece C) : ℝ≥0∞ :=
  leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
    (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
      (Quot.out C) A) X.1

/-- The actual concrete periodization of an orbit-preimage slice is exactly
the canonical representative-slice count, pointwise on the selected fiber. -/
theorem concreteDoubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice_orbitPreimage
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteRationalDoubleCosetSet)
    (B : Set (L.ConcreteRationalDoubleCosetQuotientPiece C)) :
    L.concreteDoubleCosetPieceTranslatedSlicePeriodize C
        ((rightOrbitToLeftRightDoubleCosetPiece
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) ⁻¹' B) =
      doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore
        L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C
        ((rightOrbitToLeftRightDoubleCosetPiece
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) ⁻¹' B) := by
  simpa [concreteDoubleCosetPieceTranslatedSlicePeriodize] using
    leftSetPeriodize_rightTranslateSliceSet_orbitPreimage_eq_representativeCore
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup C B
      (fun X =>
        L.finite_concreteRationalElementsSendingRightTranslate
          (Quot.out C)
          (leftRightDoubleCosetPieceRightTranslateRepresentative
            L.rationalOrthogonalDiagonalSubgroup
            L.finiteLocalLatticeStabilizerSubgroup C X))

/-- Almost-everywhere form of the concrete representative-slice comparison
for the transported selected-fiber quotient measure. -/
theorem concreteDoubleCosetPieceTranslatedSlicePeriodize_ae_eq_representativeSlice_orbitPreimage
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicOrthogonalGroup)
    (C : L.ConcreteRationalDoubleCosetSet)
    (B : Set (L.ConcreteRationalDoubleCosetQuotientPiece C)) :
    L.concreteDoubleCosetPieceTranslatedSlicePeriodize C
        ((rightOrbitToLeftRightDoubleCosetPiece
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) ⁻¹' B) =ᵐ[
      L.concreteRationalDoubleCosetPieceQuotientMeasure F C]
      doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore
        L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C
        ((rightOrbitToLeftRightDoubleCosetPiece
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) ⁻¹' B) :=
  Filter.Eventually.of_forall fun X =>
    congrFun
      (L.concreteDoubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice_orbitPreimage
        C B) X

set_option synthInstance.maxHeartbeats 100000 in
/-- On orbit-map preimages, the concrete translated-slice periodization
integrates over the selected quotient piece to the normalized subgroup Haar
measure of the preimage. -/
theorem concreteDoubleCosetPieceTranslatedSlicePeriodize_lintegral_eq_orbitPreimage
    (L : PositiveDefiniteIntegralLattice n)
    (inst : Fintype L.ConcreteRationalDoubleCosetSet)
    (C : L.ConcreteRationalDoubleCosetSet)
    {B : Set (L.ConcreteRationalDoubleCosetQuotientPiece C)}
    (hB : MeasurableSet B) :
    ∫⁻ X,
        L.concreteDoubleCosetPieceTranslatedSlicePeriodize C
          ((rightOrbitToLeftRightDoubleCosetPiece
            L.rationalOrthogonalDiagonalSubgroup
            L.finiteLocalLatticeStabilizerSubgroup C) ⁻¹' B) X
        ∂L.concreteRationalDoubleCosetPieceQuotientMeasure
          L.concreteFiniteTransversalFundamentalDomain C =
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure
        ((rightOrbitToLeftRightDoubleCosetPiece
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup C) ⁻¹' B) := by
  letI : Fintype L.ConcreteRationalDoubleCosetSet := inst
  letI : MulAction L.ConcreteFiniteAdelicOrthogonalGroup
      L.ConcreteFiniteAdelicOrthogonalGroup :=
    Monoid.toMulAction L.ConcreteFiniteAdelicOrthogonalGroup
  letI : MulAction L.rationalOrthogonalDiagonalSubgroup
      L.ConcreteFiniteAdelicOrthogonalGroup :=
    Subgroup.instMulAction
  letI : MeasurableConstSMul L.rationalOrthogonalDiagonalSubgroup
      L.ConcreteFiniteAdelicOrthogonalGroup :=
    ⟨fun c => by
      change Measurable (fun x : L.ConcreteFiniteAdelicOrthogonalGroup =>
        (c : L.ConcreteFiniteAdelicOrthogonalGroup) * x)
      exact measurable_const_mul _⟩
  letI : SMulInvariantMeasure L.rationalOrthogonalDiagonalSubgroup
      L.ConcreteFiniteAdelicOrthogonalGroup
      L.concreteFiniteAdelicOrthogonalHaarMeasure := by
    constructor
    intro c s hs
    change L.concreteFiniteAdelicOrthogonalHaarMeasure
      ((fun x : L.ConcreteFiniteAdelicOrthogonalGroup =>
        (c : L.ConcreteFiniteAdelicOrthogonalGroup) * x) ⁻¹' s) =
      L.concreteFiniteAdelicOrthogonalHaarMeasure s
    exact Measure.measure_preimage_of_map_eq_self
      (map_mul_left_eq_self L.concreteFiniteAdelicOrthogonalHaarMeasure
        (c : L.ConcreteFiniteAdelicOrthogonalGroup)) hs.nullMeasurableSet
  let orbit := rightOrbitToLeftRightDoubleCosetPiece
    L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup C
  let A : Set L.finiteLocalLatticeStabilizerSubgroup := orbit ⁻¹' B
  have hA : MeasurableSet A :=
    (L.concreteRationalRightOrbitToDoubleCosetPiece_measurable C) hB
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteLocalLatticeStabilizerSubgroup
    L.concreteFiniteLocalLatticeStabilizerMeasurableSpace_eq
  have hSmeas : MeasurableSet
      (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
        (Quot.out C) A) :=
    rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul
      L.finiteLocalLatticeStabilizerSubgroup (Quot.out C)
      hsub_comap L.measurableSet_finiteLocalLatticeStabilizerSubgroup hA
  have hfund :=
    L.concreteFiniteTransversalFundamentalDomain_isFundamentalDomain inst
  have hstrict :
      ∫⁻ y in L.concreteFiniteTransversalFundamentalDomain,
          leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
            (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
              (Quot.out C) A)
            (leftCosetMap L.rationalOrthogonalDiagonalSubgroup y)
          ∂L.concreteFiniteAdelicOrthogonalHaarMeasure =
        L.concreteFiniteAdelicOrthogonalHaarMeasure
          (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
            (Quot.out C) A) :=
    lintegral_restrict_leftSetPeriodize_eq_measure_of_isFundamentalDomain
      L.rationalOrthogonalDiagonalSubgroup hfund hSmeas
  have hquotient :
      ∫⁻ X,
          (leftRightDoubleCosetPieceSet
            L.rationalOrthogonalDiagonalSubgroup
            L.finiteLocalLatticeStabilizerSubgroup C).indicator
            (leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
              (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
                (Quot.out C) A)) X
          ∂L.concreteRationalLeftQuotientMeasure
            L.concreteFiniteTransversalFundamentalDomain =
        L.concreteFiniteAdelicOrthogonalHaarMeasure
          (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
            (Quot.out C) A) := by
    simpa [concreteRationalLeftQuotientMeasure, Quot.out_eq C] using
      (lintegral_indicator_leftSetPeriodize_rightTranslateSliceSet_eq_of_map_restrict_fundamentalDomain_countable
        L.concreteRationalLeftQuotientMeasurableSpace_eq_map hSmeas hstrict)
  have hpiece_embedding : MeasurableEmbedding
      (fun X : L.ConcreteRationalDoubleCosetQuotientPiece C => X.1) := by
    simpa [leftRightDoubleCosetPieceSet] using
      (MeasurableEmbedding.subtype_coe
        (L.measurableSet_concreteRationalDoubleCosetPiece C))
  have hpiece :
      ∫⁻ X,
          leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
            (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
              (Quot.out C) A) X.1
          ∂L.concreteRationalDoubleCosetPieceQuotientMeasure
            L.concreteFiniteTransversalFundamentalDomain C =
        ∫⁻ X,
          (leftRightDoubleCosetPieceSet
            L.rationalOrthogonalDiagonalSubgroup
            L.finiteLocalLatticeStabilizerSubgroup C).indicator
            (leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
              (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
                (Quot.out C) A)) X
          ∂L.concreteRationalLeftQuotientMeasure
            L.concreteFiniteTransversalFundamentalDomain := by
    exact lintegral_map_eq_lintegral_indicator_of_map_eq_restrict
      (L.concreteRationalDoubleCosetPieceQuotientMeasure
        L.concreteFiniteTransversalFundamentalDomain C)
      (L.concreteRationalLeftQuotientMeasure
        L.concreteFiniteTransversalFundamentalDomain)
      (fun X : L.ConcreteRationalDoubleCosetQuotientPiece C => X.1)
      (leftRightDoubleCosetPieceSet L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup C)
      hpiece_embedding (L.measurableSet_concreteRationalDoubleCosetPiece C)
      (L.concreteRationalDoubleCosetPieceQuotientMeasure_map_eq_restrict
        L.concreteFiniteTransversalFundamentalDomain C)
      (leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
        (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
          (Quot.out C) A))
  have hhaar :
      L.concreteFiniteAdelicOrthogonalHaarMeasure
          (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
            (Quot.out C) A) =
        L.concreteFiniteLocalLatticeStabilizerHaarMeasure A :=
    measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict_of_isMulLeftInvariant
      L.finiteLocalLatticeStabilizerSubgroup (Quot.out C)
      hsub_comap L.measurableSet_finiteLocalLatticeStabilizerSubgroup
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure_map_eq_restrict hA
  change (∫⁻ X,
      leftSetPeriodize L.rationalOrthogonalDiagonalSubgroup
        (rightTranslateSliceSet L.finiteLocalLatticeStabilizerSubgroup
          (Quot.out C) A) X.1
      ∂L.concreteRationalDoubleCosetPieceQuotientMeasure
        L.concreteFiniteTransversalFundamentalDomain C) =
    L.concreteFiniteLocalLatticeStabilizerHaarMeasure A
  exact hpiece.trans (hquotient.trans hhaar)

theorem matrix_mulVec_mem_integralFiniteAdeleVectors
    {M : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hM : ∀ i j, M i j ∈ integralFiniteAdeleSubring)
    {x : Fin n → RationalFiniteAdele}
    (hx : x ∈ integralFiniteAdeleVectors n) :
    M *ᵥ x ∈ integralFiniteAdeleVectors n := by
  intro i
  change (∑ j, M i j * x j) ∈ integralFiniteAdeleSubring
  exact Subring.sum_mem integralFiniteAdeleSubring fun j _ ↦
    Subring.mul_mem integralFiniteAdeleSubring (hM i j) (hx j)

/-- An everywhere-integral finite-adelic matrix unit preserves membership in
the completed coordinate lattice in both directions. -/
theorem integralFiniteAdeleMatrixUnit_mulVec_mem_iff
    (g : GL (Fin n) RationalFiniteAdele)
    (hg : g ∈ matrixUnitsOverSubring (n := n) integralFiniteAdeleSubring)
    (x : Fin n → RationalFiniteAdele) :
    g.1.mulVec x ∈ integralFiniteAdeleVectors n ↔
      x ∈ integralFiniteAdeleVectors n := by
  constructor
  · intro hgx
    have hx := matrix_mulVec_mem_integralFiniteAdeleVectors hg.2 hgx
    rw [Matrix.mulVec_mulVec] at hx
    have hval : (g⁻¹).1 * g.1 = 1 := by
      change (g⁻¹ * g).1 = 1
      simp
    change ((g⁻¹).1 * g.1).mulVec x ∈ integralFiniteAdeleVectors n at hx
    rwa [hval, Matrix.one_mulVec] at hx
  · exact matrix_mulVec_mem_integralFiniteAdeleVectors hg.1

/-- Every element of the concrete finite local stabilizer preserves the
completed lattice in the chosen integral coordinates. -/
theorem finiteLocalLatticeStabilizerSubgroup_mapsTo
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup) :
    Set.MapsTo (g.1.1.mulVec) (integralFiniteAdeleVectors n)
      (integralFiniteAdeleVectors n) := by
  intro x hx
  exact matrix_mulVec_mem_integralFiniteAdeleVectors hg.1 hx

/-- The inverse of every element of the concrete finite local stabilizer also
preserves the completed lattice. -/
theorem finiteLocalLatticeStabilizerSubgroup_inverse_mapsTo
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup) :
    Set.MapsTo ((g.1⁻¹).1.mulVec) (integralFiniteAdeleVectors n)
      (integralFiniteAdeleVectors n) := by
  intro x hx
  exact matrix_mulVec_mem_integralFiniteAdeleVectors hg.2 hx

/-- Every element of the concrete finite local stabilizer carries the
completed lattice onto itself. -/
theorem finiteLocalLatticeStabilizerSubgroup_image_eq
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup) :
    g.1.1.mulVec '' integralFiniteAdeleVectors n =
      integralFiniteAdeleVectors n := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact L.finiteLocalLatticeStabilizerSubgroup_mapsTo hg hx
  · intro y hy
    let x := (g.1⁻¹).1.mulVec y
    have hx : x ∈ integralFiniteAdeleVectors n :=
      L.finiteLocalLatticeStabilizerSubgroup_inverse_mapsTo hg hy
    refine ⟨x, hx, ?_⟩
    dsimp only [x]
    rw [Matrix.mulVec_mulVec]
    have hval : g.1.1 * (g.1⁻¹).1 = 1 := by
      change (g.1 * g.1⁻¹).1 = 1
      simp
    rw [hval, Matrix.one_mulVec]

/-- Membership in the completed coordinate lattice is invariant under an
element of the concrete finite local stabilizer. -/
theorem finiteLocalLatticeStabilizerSubgroup_mulVec_mem_iff
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup)
    (x : Fin n → RationalFiniteAdele) :
    g.1.1.mulVec x ∈ integralFiniteAdeleVectors n ↔
      x ∈ integralFiniteAdeleVectors n := by
  constructor
  · intro hgx
    have hx := L.finiteLocalLatticeStabilizerSubgroup_inverse_mapsTo hg hgx
    rw [Matrix.mulVec_mulVec] at hx
    have hval : (g.1⁻¹).1 * g.1.1 = 1 := by
      change (g.1⁻¹ * g.1).1 = 1
      simp
    rwa [hval, Matrix.one_mulVec] at hx
  · intro hx
    exact L.finiteLocalLatticeStabilizerSubgroup_mapsTo hg hx

/-- The diagonal finite-adele vector attached to a rational coordinate
vector. -/
def rationalVectorFiniteAdele (x : Fin n → ℚ) : Fin n → RationalFiniteAdele :=
  fun i ↦ algebraMap ℚ RationalFiniteAdele (x i)

@[simp]
theorem rationalVectorFiniteAdele_zero :
    rationalVectorFiniteAdele (0 : Fin n → ℚ) = 0 := by
  ext i
  simp [rationalVectorFiniteAdele]

@[simp]
theorem rationalVectorFiniteAdele_add (x y : Fin n → ℚ) :
    rationalVectorFiniteAdele (x + y) =
      rationalVectorFiniteAdele x + rationalVectorFiniteAdele y := by
  ext i
  simp [rationalVectorFiniteAdele]

@[simp]
theorem rationalVectorFiniteAdele_int_smul (z : ℤ) (x : Fin n → ℚ) :
    rationalVectorFiniteAdele (z • x) =
      z • rationalVectorFiniteAdele x := by
  ext i v
  simp [rationalVectorFiniteAdele]

/-- Diagonal finite-adele embedding commutes with rational matrix-vector
multiplication. -/
theorem rationalMatrix_map_mulVec_rationalVectorFiniteAdele
    (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    (M.map (algebraMap ℚ RationalFiniteAdele)).mulVec
        (rationalVectorFiniteAdele x) =
      rationalVectorFiniteAdele (M.mulVec x) := by
  ext i v
  simp [Matrix.mulVec, dotProduct, rationalVectorFiniteAdele, map_sum]

/-- A matrix satisfying `Xᵀ A X = A` preserves mixed bilinear pairings. -/
theorem dotProduct_mulVec_eq_of_matrix_conj
    {R : Type*} [CommSemiring R]
    {A X : Matrix (Fin n) (Fin n) R}
    (hX : Xᵀ * A * X = A)
    (x y : Fin n → R) :
    dotProduct (X.mulVec x) (A.mulVec (X.mulVec y)) =
      dotProduct x (A.mulVec y) := by
  symm
  calc
    dotProduct x (A.mulVec y) =
        dotProduct x ((Xᵀ * A * X).mulVec y) := by rw [hX]
    _ = (x ᵥ* (Xᵀ * A * X)) ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec]
    _ = (((x ᵥ* Xᵀ) ᵥ* A) ᵥ* X) ⬝ᵥ y := by
      simp [Matrix.mul_assoc]
    _ = ((X *ᵥ x) ᵥ* A) ⬝ᵥ (X *ᵥ y) := by
      rw [← Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct (X.mulVec x) (A.mulVec (X.mulVec y)) := by
      exact (Matrix.dotProduct_mulVec (X *ᵥ x) A (X *ᵥ y)).symm

/-- Extending the rational bilinear value diagonally to the finite adeles is
the bilinear value of the diagonally embedded vectors. -/
theorem rationalBilinearFormValue_map
    (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℚ) :
    algebraMap ℚ RationalFiniteAdele (L.bilinearFormValueRat x y) =
      dotProduct (rationalVectorFiniteAdele x)
        (L.finiteAdelicFormMatrix.mulVec (rationalVectorFiniteAdele y)) := by
  simp [bilinearFormValueRat, finiteAdelicFormMatrix, rationalVectorFiniteAdele,
    Matrix.mulVec, dotProduct, map_sum]

/-- The finite-adelic bilinear form is integral on two everywhere-integral
vectors. -/
theorem finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring
    (L : PositiveDefiniteIntegralLattice n)
    (x y : Fin n → RationalFiniteAdele)
    (hx : x ∈ integralFiniteAdeleVectors n)
    (hy : y ∈ integralFiniteAdeleVectors n) :
    dotProduct x (L.finiteAdelicFormMatrix.mulVec y) ∈
      integralFiniteAdeleSubring := by
  rw [dotProduct]
  apply Subring.sum_mem
  intro i _hi
  apply Subring.mul_mem integralFiniteAdeleSubring (hx i)
  rw [Matrix.mulVec, dotProduct]
  apply Subring.sum_mem
  intro j _hj
  apply Subring.mul_mem integralFiniteAdeleSubring
  · exact integer_mem_integralFiniteAdeleSubring (L.pairingMatrix i j)
  · exact hy j

/-- The rational lattice attached to a concrete finite-adelic representative
`g`, using the convention `M_g = ℚ^n ∩ g (∏_p ℤ_p^n)`.  Equivalently, a rational
vector belongs to `M_g` when applying `g⁻¹` to its diagonal finite-adele
image gives an everywhere-integral vector. -/
def concreteAttachedRationalLatticeSubmodule
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Submodule ℤ (Fin n → ℚ) where
  carrier := {x |
    (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x) ∈
      integralFiniteAdeleVectors n}
  zero_mem' := by
    change (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele 0) ∈
      integralFiniteAdeleVectors n
    rw [rationalVectorFiniteAdele_zero, Matrix.mulVec_zero]
    intro i
    exact Subring.zero_mem integralFiniteAdeleSubring
  add_mem' := by
    intro x y hx hy
    change (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele (x + y)) ∈
      integralFiniteAdeleVectors n
    rw [rationalVectorFiniteAdele_add, Matrix.mulVec_add]
    intro i
    exact Subring.add_mem integralFiniteAdeleSubring (hx i) (hy i)
  smul_mem' := by
    intro z x hx
    change (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele (z • x)) ∈
      integralFiniteAdeleVectors n
    rw [rationalVectorFiniteAdele_int_smul]
    let f : (Fin n → RationalFiniteAdele) →+
        (Fin n → RationalFiniteAdele) :=
      { toFun := (g.1⁻¹).1.mulVec
        map_zero' := by simp
        map_add' := by
          intro u v
          exact Matrix.mulVec_add (g.1⁻¹).1 u v }
    have hmul :
        (g.1⁻¹).1.mulVec (z • rationalVectorFiniteAdele x) =
          z • (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x) :=
      map_zsmul f z (rationalVectorFiniteAdele x)
    rw [hmul]
    intro i
    exact integralFiniteAdeleSubring.toAddSubgroup.zsmul_mem (hx i) z

@[simp]
theorem mem_concreteAttachedRationalLatticeSubmodule_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : Fin n → ℚ) :
    x ∈ L.concreteAttachedRationalLatticeSubmodule g ↔
      (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x) ∈
        integralFiniteAdeleVectors n :=
  Iff.rfl

/-- The standard integral coordinate lattice `ℤ^n`, viewed inside `ℚ^n`. -/
def rationalIntegralCoordinateSubmodule (n : ℕ) :
    Submodule ℤ (Fin n → ℚ) :=
  LinearMap.range (intVectorToRatLinear n)

@[simp]
theorem mem_rationalIntegralCoordinateSubmodule_iff
    (x : Fin n → ℚ) :
    x ∈ rationalIntegralCoordinateSubmodule n ↔
      ∃ z : Fin n → ℤ, intVectorToRatLinear n z = x :=
  Iff.rfl

/-- The attached lattice at the identity representative is the original
integral coordinate lattice. -/
theorem concreteAttachedRationalLatticeSubmodule_one
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteAttachedRationalLatticeSubmodule 1 =
      rationalIntegralCoordinateSubmodule n := by
  ext x
  rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff,
    mem_rationalIntegralCoordinateSubmodule_iff]
  have hone : (((1 : L.ConcreteFiniteAdelicOrthogonalGroup).1⁻¹).1) = 1 := by
    simp
  rw [hone, Matrix.one_mulVec]
  constructor
  · intro hx
    have hcoord : ∀ i : Fin n, ∃ z : ℤ, (z : ℚ) = x i := by
      intro i
      exact (rational_mem_integralFiniteAdeleSubring_iff (x i)).mp (hx i)
    choose z hz using hcoord
    refine ⟨z, ?_⟩
    ext i
    exact hz i
  · rintro ⟨z, rfl⟩
    intro i
    exact (rational_mem_integralFiniteAdeleSubring_iff
      (intVectorToRatLinear n z i)).mpr ⟨z i, rfl⟩

/-- Membership in the lattice attached to the conditional representative
`diag(P) U` is equivalent to integrality of the coordinates after applying
`P⁻¹`. -/
theorem mem_concreteAttachedRationalLatticeSubmodule_representativeOfRationalComparison_iff
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)))
    (x : Fin n → ℚ) :
    x ∈ L.concreteAttachedRationalLatticeSubmodule
        (L.concreteFiniteAdelicRepresentativeOfRationalComparison
          M P hP U hU) ↔
      (P⁻¹).1.mulVec x ∈ rationalIntegralCoordinateSubmodule n := by
  rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff]
  let Uf := localIntegralMatrixUnitsFiniteAdeleGL U
  have hUf : Uf ∈
      matrixUnitsOverSubring (n := n) integralFiniteAdeleSubring :=
    localIntegralMatrixUnitsFiniteAdeleGL_mem_matrixUnitsOverSubring U
  have hinv :
      ((((L.concreteFiniteAdelicRepresentativeOfRationalComparison
        M P hP U hU).1)⁻¹).1) =
        (Uf⁻¹).1 * (P⁻¹).1.map (algebraMap ℚ RationalFiniteAdele) := by
    change (((Matrix.GeneralLinearGroup.map
      (algebraMap ℚ RationalFiniteAdele) P * Uf)⁻¹).1) = _
    rw [mul_inv_rev]
    congr 1
  rw [hinv, ← Matrix.mulVec_mulVec,
    integralFiniteAdeleMatrixUnit_mulVec_mem_iff (Uf⁻¹)
      ((matrixUnitsOverSubring (n := n) integralFiniteAdeleSubring).inv_mem hUf),
    rationalMatrix_map_mulVec_rationalVectorFiniteAdele]
  rw [← L.concreteAttachedRationalLatticeSubmodule_one,
    L.mem_concreteAttachedRationalLatticeSubmodule_iff]
  simp

/-- The lattice attached to the conditional representative `diag(P) U` is
exactly the image `P Z^n` of the standard integral coordinate lattice. -/
theorem concreteAttachedRationalLatticeSubmodule_representativeOfRationalComparison
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    P.1.mulVec '' (rationalIntegralCoordinateSubmodule n : Set (Fin n → ℚ)) =
      (L.concreteAttachedRationalLatticeSubmodule
        (L.concreteFiniteAdelicRepresentativeOfRationalComparison
          M P hP U hU) : Set (Fin n → ℚ)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (L.mem_concreteAttachedRationalLatticeSubmodule_representativeOfRationalComparison_iff
      M P hP U hU _).2
    rw [Matrix.mulVec_mulVec]
    have hval : (P⁻¹).1 * P.1 = 1 := by
      change (P⁻¹ * P).1 = 1
      simp
    rwa [hval, Matrix.one_mulVec]
  · intro hy
    let x := (P⁻¹).1.mulVec y
    have hx : x ∈ rationalIntegralCoordinateSubmodule n :=
      (L.mem_concreteAttachedRationalLatticeSubmodule_representativeOfRationalComparison_iff
        M P hP U hU y).1 hy
    refine ⟨x, hx, ?_⟩
    dsimp only [x]
    rw [Matrix.mulVec_mulVec]
    have hval : P.1 * (P⁻¹).1 = 1 := by
      change (P * P⁻¹).1 = 1
      simp
    rw [hval, Matrix.one_mulVec]

/-- Right multiplication by the finite local stabilizer does not change the
attached rational lattice. -/
theorem concreteAttachedRationalLatticeSubmodule_mul_finiteLocalStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (h : L.finiteLocalLatticeStabilizerSubgroup) :
    L.concreteAttachedRationalLatticeSubmodule
        (g * (h : L.ConcreteFiniteAdelicOrthogonalGroup)) =
      L.concreteAttachedRationalLatticeSubmodule g := by
  ext x
  rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff,
    L.mem_concreteAttachedRationalLatticeSubmodule_iff]
  have hinv :
      (((g * (h : L.ConcreteFiniteAdelicOrthogonalGroup)).1⁻¹).1) =
        ((h.1⁻¹).1 * (g.1⁻¹).1) := by
    change (((g.1 * h.1)⁻¹).1) = ((h.1⁻¹).1 * (g.1⁻¹).1)
    simp
  rw [hinv, ← Matrix.mulVec_mulVec]
  exact L.finiteLocalLatticeStabilizerSubgroup_mulVec_mem_iff
    (L.finiteLocalLatticeStabilizerSubgroup.inv_mem h.2)
    ((g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x))

/-- Left multiplication by a diagonal rational orthogonal matrix transports
the attached lattice by the corresponding rational linear change of
coordinates. -/
theorem mem_concreteAttachedRationalLatticeSubmodule_rational_mul_iff
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.rationalOrthogonalMatrixSubgroup)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : Fin n → ℚ) :
    x ∈ L.concreteAttachedRationalLatticeSubmodule
        (L.rationalOrthogonalDiagonalHom q * g) ↔
      (q.1⁻¹).1.mulVec x ∈
        L.concreteAttachedRationalLatticeSubmodule g := by
  rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff,
    L.mem_concreteAttachedRationalLatticeSubmodule_iff]
  have hinv :
      ((((L.rationalOrthogonalDiagonalHom q * g).1)⁻¹).1) =
        (g.1⁻¹).1 * ((L.rationalOrthogonalDiagonalHom q).1⁻¹).1 := by
    change ((((L.rationalOrthogonalDiagonalHom q).1 * g.1)⁻¹).1) =
      (g.1⁻¹).1 * ((L.rationalOrthogonalDiagonalHom q).1⁻¹).1
    simp
  have hdiag_inv :
      ((L.rationalOrthogonalDiagonalHom q).1⁻¹).1 =
        (q.1⁻¹).1.map (algebraMap ℚ RationalFiniteAdele) := by
    have hmap_inv := map_inv L.rationalOrthogonalDiagonalHom q
    have hval := congrArg
      (fun y : L.ConcreteFiniteAdelicOrthogonalGroup ↦ y.1.1) hmap_inv
    calc
      ((L.rationalOrthogonalDiagonalHom q).1⁻¹).1 =
          (L.rationalOrthogonalDiagonalHom q⁻¹).1.1 := hval.symm
      _ = (q.1⁻¹).1.map (algebraMap ℚ RationalFiniteAdele) :=
        L.rationalOrthogonalDiagonalHom_apply_matrix q⁻¹
  rw [hinv, ← Matrix.mulVec_mulVec, hdiag_inv,
    rationalMatrix_map_mulVec_rationalVectorFiniteAdele]

/-- Rational matrix multiplication carries `M_g` onto the lattice attached
to the corresponding left rational translate of `g`. -/
theorem rational_mulVec_image_concreteAttachedRationalLatticeSubmodule
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.rationalOrthogonalMatrixSubgroup)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    q.1.1.mulVec ''
        (L.concreteAttachedRationalLatticeSubmodule g : Set (Fin n → ℚ)) =
      (L.concreteAttachedRationalLatticeSubmodule
        (L.rationalOrthogonalDiagonalHom q * g) : Set (Fin n → ℚ)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (L.mem_concreteAttachedRationalLatticeSubmodule_rational_mul_iff
      q g (q.1.1.mulVec x)).2
    rw [Matrix.mulVec_mulVec]
    have hq : (q.1⁻¹).1 * q.1.1 = 1 := by
      change (q.1⁻¹ * q.1).1 = 1
      simp
    rwa [hq, Matrix.one_mulVec]
  · intro hy
    let x := (q.1⁻¹).1.mulVec y
    have hx : x ∈ L.concreteAttachedRationalLatticeSubmodule g :=
      (L.mem_concreteAttachedRationalLatticeSubmodule_rational_mul_iff
        q g y).1 hy
    refine ⟨x, hx, ?_⟩
    dsimp only [x]
    rw [Matrix.mulVec_mulVec]
    have hq : q.1.1 * (q.1⁻¹).1 = 1 := by
      change (q.1 * q.1⁻¹).1 = 1
      simp
    rw [hq, Matrix.one_mulVec]

/-- The denominator of `g⁻¹` gives a full-rank lower coordinate lattice inside
the attached rational lattice. -/
theorem scaled_rationalIntegralCoordinateSubmodule_le_concreteAttached
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    LinearMap.range
        (finiteAdeleMatrixDenominator (g.1⁻¹).1 • intVectorToRatLinear n) ≤
      L.concreteAttachedRationalLatticeSubmodule g := by
  rintro _x ⟨z, rfl⟩
  rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff,
    LinearMap.smul_apply, rationalVectorFiniteAdele_int_smul,
    Matrix.mulVec_smul]
  apply finiteAdeleMatrixDenominator_smul_mulVec_mem_integralFiniteAdeleVectors
  intro i
  exact (rational_mem_integralFiniteAdeleSubring_iff
    (intVectorToRatLinear n z i)).mpr ⟨z i, rfl⟩

/-- The denominator of `g` bounds the attached rational lattice inside the
coordinate overmodule `d⁻¹ ℤⁿ`. -/
theorem concreteAttachedRationalLatticeSubmodule_le_invScalar
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteAttachedRationalLatticeSubmodule g ≤
      invScalarIntegralLatticeSubmodule
        (finiteAdeleMatrixDenominator g.1.1) n := by
  intro x hx
  let d := finiteAdeleMatrixDenominator g.1.1
  have hy : (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x) ∈
      integralFiniteAdeleVectors n :=
    (L.mem_concreteAttachedRationalLatticeSubmodule_iff g x).mp hx
  have hclear :=
    finiteAdeleMatrixDenominator_smul_mulVec_mem_integralFiniteAdeleVectors
      g.1.1 ((g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x)) hy
  rw [Matrix.mulVec_mulVec] at hclear
  have hval : g.1.1 * (g.1⁻¹).1 = 1 := by
    change (g.1 * g.1⁻¹).1 = 1
    simp
  rw [hval, Matrix.one_mulVec] at hclear
  have hcoord : ∀ i : Fin n, ∃ z : ℤ, (z : ℚ) = (d : ℚ) * x i := by
    intro i
    have hi : algebraMap ℚ RationalFiniteAdele ((d : ℚ) * x i) ∈
        integralFiniteAdeleSubring := by
      simpa [d, rationalVectorFiniteAdele, smul_eq_mul] using hclear i
    exact (rational_mem_integralFiniteAdeleSubring_iff ((d : ℚ) * x i)).mp hi
  choose z hz using hcoord
  refine ⟨z, ?_⟩
  have hd : (d : ℚ) ≠ 0 := by
    exact_mod_cast finiteAdeleMatrixDenominator_ne_zero g.1.1
  ext i
  change x i = (d : ℚ)⁻¹ * (z i : ℚ)
  rw [hz i]
  field_simp

/-- The attached rational lattice is finitely generated as a `ℤ`-module.
The upper denominator bound embeds its scaled image into the standard
coordinate lattice. -/
theorem concreteAttachedRationalLatticeSubmodule_fg
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedRationalLatticeSubmodule g).FG := by
  let d := finiteAdeleMatrixDenominator g.1.1
  let f : (Fin n → ℚ) →ₗ[ℤ] (Fin n → ℚ) :=
    (LinearMap.lsmul ℤ (Fin n → ℚ)) d
  have hd : d ≠ 0 := finiteAdeleMatrixDenominator_ne_zero g.1.1
  have hf : Function.Injective f := by
    exact LinearMap.lsmul_injective hd
  have hmap_le :
      (L.concreteAttachedRationalLatticeSubmodule g).map f ≤
        rationalIntegralCoordinateSubmodule n := by
    rintro _y ⟨x, hx, rfl⟩
    rcases L.concreteAttachedRationalLatticeSubmodule_le_invScalar g hx with
      ⟨z, hz⟩
    rw [mem_rationalIntegralCoordinateSubmodule_iff]
    refine ⟨z, ?_⟩
    rw [hz]
    ext i
    change (z i : ℚ) = (d : ℚ) * ((d : ℚ)⁻¹ * (z i : ℚ))
    field_simp
  have hmap_fg :
      ((L.concreteAttachedRationalLatticeSubmodule g).map f).FG :=
    (Submodule.fg_range (intVectorToRatLinear n)).of_le hmap_le
  exact Submodule.fg_of_fg_map f (LinearMap.ker_eq_bot.mpr hf) hmap_fg

/-- The rational bilinear form of `L` is integer-valued on the concrete
attached lattice. -/
theorem concreteAttachedRationalLatticeSubmodule_integralOnLattice
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    rationalSubmoduleIntegralOnLattice L
      (L.concreteAttachedRationalLatticeSubmodule g) := by
  intro x hx y hy
  let u := (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x)
  let v := (g.1⁻¹).1.mulVec (rationalVectorFiniteAdele y)
  have hu : u ∈ integralFiniteAdeleVectors n :=
    (L.mem_concreteAttachedRationalLatticeSubmodule_iff g x).mp hx
  have hv : v ∈ integralFiniteAdeleVectors n :=
    (L.mem_concreteAttachedRationalLatticeSubmodule_iff g y).mp hy
  have hrecover_x : g.1.1.mulVec u = rationalVectorFiniteAdele x := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec]
    have hval : g.1.1 * (g.1⁻¹).1 = 1 := by
      change (g.1 * g.1⁻¹).1 = 1
      simp
    rw [hval, Matrix.one_mulVec]
  have hrecover_y : g.1.1.mulVec v = rationalVectorFiniteAdele y := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec]
    have hval : g.1.1 * (g.1⁻¹).1 = 1 := by
      change (g.1 * g.1⁻¹).1 = 1
      simp
    rw [hval, Matrix.one_mulVec]
  have hpair :
      algebraMap ℚ RationalFiniteAdele (L.bilinearFormValueRat x y) =
        dotProduct u (L.finiteAdelicFormMatrix.mulVec v) := by
    rw [rationalBilinearFormValue_map, ← hrecover_x, ← hrecover_y]
    exact dotProduct_mulVec_eq_of_matrix_conj g.2 u v
  have hint :
      algebraMap ℚ RationalFiniteAdele (L.bilinearFormValueRat x y) ∈
        integralFiniteAdeleSubring := by
    rw [hpair]
    exact L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring
      u v hu hv
  rcases (rational_mem_integralFiniteAdeleSubring_iff
    (L.bilinearFormValueRat x y)).mp hint with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

/-- The integral coordinate model obtained by clearing the fixed denominator
of the concrete attached rational lattice. -/
def concreteAttachedDenominatorClearedSubmodule
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Submodule ℤ (Fin n → ℤ) :=
  denominatorClearedSubmodule (finiteAdeleMatrixDenominator g.1.1)
    (L.concreteAttachedRationalLatticeSubmodule g)

/-- The product of the denominators of `g` and `g⁻¹` gives a full-rank
coordinate submodule inside the denominator-cleared attached lattice. -/
theorem scalarSubmodule_le_concreteAttachedDenominatorClearedSubmodule
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    let d := finiteAdeleMatrixDenominator g.1.1
    let e := finiteAdeleMatrixDenominator (g.1⁻¹).1
    LinearMap.range
        ((d * e) •
          (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))) ≤
      L.concreteAttachedDenominatorClearedSubmodule g := by
  dsimp only
  let d := finiteAdeleMatrixDenominator g.1.1
  let e := finiteAdeleMatrixDenominator (g.1⁻¹).1
  have hd : d ≠ 0 := finiteAdeleMatrixDenominator_ne_zero g.1.1
  have hlower :=
    L.scaled_rationalIntegralCoordinateSubmodule_le_concreteAttached g
  rintro _z ⟨y, rfl⟩
  change (d * e) • y ∈
    denominatorClearedSubmodule d
      (L.concreteAttachedRationalLatticeSubmodule g)
  rw [mem_denominatorClearedSubmodule]
  have hrecover :
      (d : ℚ)⁻¹ • intVectorToRatLinear n ((d * e) • y) =
        (e : ℤ) • intVectorToRatLinear n y := by
    ext i
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    change (d : ℚ)⁻¹ * (((d * e) * y i : ℤ) : ℚ) =
      (e : ℚ) * (y i : ℚ)
    push_cast
    field_simp
  rw [hrecover]
  exact hlower ⟨y, rfl⟩

/-- Clearing the denominator of the attached rational lattice produces a
full-rank integral coordinate submodule. -/
theorem concreteAttachedDenominatorClearedSubmodule_finrank_eq
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Module.finrank ℤ (L.concreteAttachedDenominatorClearedSubmodule g) = n := by
  let d := finiteAdeleMatrixDenominator g.1.1
  let e := finiteAdeleMatrixDenominator (g.1⁻¹).1
  let E : Submodule ℤ (Fin n → ℤ) :=
    LinearMap.range
      ((d * e) •
        (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)))
  have hde : d * e ≠ 0 := mul_ne_zero
    (finiteAdeleMatrixDenominator_ne_zero g.1.1)
    (finiteAdeleMatrixDenominator_ne_zero (g.1⁻¹).1)
  have hE : Module.finrank ℤ E = n := by
    simpa [E] using
      smul_top_integral_coordinate_submodule_finrank (n := n) (d * e) hde
  have hle : E ≤ L.concreteAttachedDenominatorClearedSubmodule g := by
    simpa [E, d, e] using
      L.scalarSubmodule_le_concreteAttachedDenominatorClearedSubmodule g
  have hmono := Submodule.finrank_mono hle
  have hupper :
      Module.finrank ℤ
          (L.concreteAttachedDenominatorClearedSubmodule g) ≤ n := by
    simpa [Module.finrank_pi] using
      (L.concreteAttachedDenominatorClearedSubmodule g).finrank_le
  exact le_antisymm hupper (by simpa [hE] using hmono)

/-- The canonical square basis of the denominator-cleared coordinate model
of the concrete attached lattice. -/
noncomputable def concreteAttachedDenominatorClearedBasis
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Module.Basis (Fin n) ℤ
      (L.concreteAttachedDenominatorClearedSubmodule g) :=
  fullRankCoordinateSubmoduleBasis
    (L.concreteAttachedDenominatorClearedSubmodule g)
    (L.concreteAttachedDenominatorClearedSubmodule_finrank_eq g)

/-- Scaling by the inverse clearing denominator identifies the cleared
coordinate model with the attached rational lattice. -/
noncomputable def concreteAttachedDenominatorClearedEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteAttachedDenominatorClearedSubmodule g ≃ₗ[ℤ]
      L.concreteAttachedRationalLatticeSubmodule g := by
  let d := finiteAdeleMatrixDenominator g.1.1
  let B := L.concreteAttachedDenominatorClearedSubmodule g
  let M := L.concreteAttachedRationalLatticeSubmodule g
  let f : B →ₗ[ℤ] M :=
    { toFun := fun z => ⟨(d : ℚ)⁻¹ • intVectorToRatLinear n z,
        by exact z.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [map_add, smul_add]
      map_smul' := by
        intro r x
        apply Subtype.ext
        ext i
        simp [smul_eq_mul]
        ring }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    ext i
    have hi := congr_fun (congrArg Subtype.val hxy) i
    have hd : d ≠ 0 := finiteAdeleMatrixDenominator_ne_zero g.1.1
    have hdq : (d : ℚ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd)
    change (d : ℚ)⁻¹ * (x.1 i : ℚ) =
      (d : ℚ)⁻¹ * (y.1 i : ℚ) at hi
    have hcast : (x.1 i : ℚ) = (y.1 i : ℚ) :=
      mul_left_cancel₀ hdq hi
    exact_mod_cast hcast
  · intro x
    have hupper := L.concreteAttachedRationalLatticeSubmodule_le_invScalar g
    rcases (mem_iff_exists_denominatorClearedSubmodule d hupper x.1).mp
        x.property with ⟨z, hz, hx⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hx.symm

/-- A square `ℤ`-basis of the concrete attached rational lattice itself. -/
noncomputable def concreteAttachedRationalLatticeBasis
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Module.Basis (Fin n) ℤ
      (L.concreteAttachedRationalLatticeSubmodule g) :=
  (L.concreteAttachedDenominatorClearedBasis g).map
    (L.concreteAttachedDenominatorClearedEquiv g)

@[simp]
theorem concreteAttachedRationalLatticeBasis_apply_val
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) (i : Fin n) :
    ((L.concreteAttachedRationalLatticeBasis g i :
        L.concreteAttachedRationalLatticeSubmodule g) : Fin n → ℚ) =
      (finiteAdeleMatrixDenominator g.1.1 : ℚ)⁻¹ •
        intVectorToRatLinear n
          ((L.concreteAttachedDenominatorClearedBasis g i :
              L.concreteAttachedDenominatorClearedSubmodule g) :
            Fin n → ℤ) := by
  rfl

/-- The chosen square basis reconstructs every element of the attached
rational lattice from an integral coordinate vector. -/
theorem mem_concreteAttachedRationalLatticeSubmodule_iff_exists_basisCoords
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (x : Fin n → ℚ) :
    x ∈ L.concreteAttachedRationalLatticeSubmodule g ↔
      ∃ z : Fin n → ℤ,
        x = (finiteAdeleMatrixDenominator g.1.1 : ℚ)⁻¹ •
          intVectorToRatLinear n
            (((L.concreteAttachedDenominatorClearedBasis g).equivFun.symm z :
                L.concreteAttachedDenominatorClearedSubmodule g) :
              Fin n → ℤ) := by
  let d := finiteAdeleMatrixDenominator g.1.1
  have hupper := L.concreteAttachedRationalLatticeSubmodule_le_invScalar g
  rw [mem_iff_exists_denominatorClearedSubmodule d hupper x]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(L.concreteAttachedDenominatorClearedBasis g).equivFun
      ⟨y, hy⟩, ?_⟩
    change (d : ℚ)⁻¹ • intVectorToRatLinear n y =
      (d : ℚ)⁻¹ • intVectorToRatLinear n
        (((L.concreteAttachedDenominatorClearedBasis g).equivFun.symm
          ((L.concreteAttachedDenominatorClearedBasis g).equivFun ⟨y, hy⟩) :
            L.concreteAttachedDenominatorClearedSubmodule g) :
          Fin n → ℤ)
    simp
  · rintro ⟨z, rfl⟩
    refine ⟨(L.concreteAttachedDenominatorClearedBasis g).equivFun.symm z,
      ?_, ?_⟩
    · exact
        ((L.concreteAttachedDenominatorClearedBasis g).equivFun.symm z).property
    · rfl

/-- The integral form matrix of the concrete attached rational lattice in its
chosen square basis. -/
noncomputable def concreteAttachedRationalLatticeFormMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Matrix (Fin n) (Fin n) ℤ :=
  integerMatrixOfRatMatrix
    (fun i j => L.bilinearFormValueRat
      (L.concreteAttachedRationalLatticeBasis g i).1
      (L.concreteAttachedRationalLatticeBasis g j).1)
    (fun i j =>
      L.concreteAttachedRationalLatticeSubmodule_integralOnLattice g
        (L.concreteAttachedRationalLatticeBasis g i).1
        (L.concreteAttachedRationalLatticeBasis g i).property
        (L.concreteAttachedRationalLatticeBasis g j).1
        (L.concreteAttachedRationalLatticeBasis g j).property)

@[simp]
theorem concreteAttachedRationalLatticeFormMatrix_cast
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedRationalLatticeFormMatrix g).map
        (Int.cast : ℤ → ℚ) =
      fun i j => L.bilinearFormValueRat
        (L.concreteAttachedRationalLatticeBasis g i).1
        (L.concreteAttachedRationalLatticeBasis g j).1 := by
  exact integerMatrixOfRatMatrix_cast _ _

/-- The form matrix in the chosen basis of the attached lattice is
symmetric. -/
theorem concreteAttachedRationalLatticeFormMatrix_symm
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedRationalLatticeFormMatrix g).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  change
    ((L.concreteAttachedRationalLatticeFormMatrix g).map
        (Int.cast : ℤ → ℚ)) j i =
      ((L.concreteAttachedRationalLatticeFormMatrix g).map
        (Int.cast : ℤ → ℚ)) i j
  rw [L.concreteAttachedRationalLatticeFormMatrix_cast]
  exact L.bilinearFormValueRat_comm _ _

/-- The rational matrix whose columns are the chosen basis vectors of the
concrete attached lattice in the ambient rational coordinates. -/
noncomputable def concreteAttachedRationalLatticeBasisMatrixRat
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Matrix (Fin n) (Fin n) ℚ :=
  let d := finiteAdeleMatrixDenominator g.1.1
  let B := L.concreteAttachedDenominatorClearedSubmodule g
  let hB := L.concreteAttachedDenominatorClearedSubmodule_finrank_eq g
  (d : ℚ)⁻¹ •
    (fullRankCoordinateSubmoduleBasisMatrix B hB).map (Int.cast : ℤ → ℚ)

/-- The columns of the rational basis matrix are the chosen attached-lattice
basis vectors. -/
theorem concreteAttachedRationalLatticeBasisMatrixRat_col
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) (j : Fin n) :
    (L.concreteAttachedRationalLatticeBasisMatrixRat g).col j =
      (L.concreteAttachedRationalLatticeBasis g j).1 := by
  ext i
  rw [L.concreteAttachedRationalLatticeBasis_apply_val]
  rfl

/-- The rational matrix of the chosen attached-lattice basis is
nonsingular. -/
theorem concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedRationalLatticeBasisMatrixRat g).det ≠ 0 := by
  let d := finiteAdeleMatrixDenominator g.1.1
  let B := L.concreteAttachedDenominatorClearedSubmodule g
  let hB := L.concreteAttachedDenominatorClearedSubmodule_finrank_eq g
  let Pℤ := fullRankCoordinateSubmoduleBasisMatrix B hB
  have hd : (d : ℚ)⁻¹ ≠ 0 := inv_ne_zero (by
    exact_mod_cast finiteAdeleMatrixDenominator_ne_zero g.1.1)
  have hPℤ : Pℤ.det ≠ 0 := by
    simpa [Pℤ] using fullRankCoordinateSubmoduleBasisMatrix_det_ne_zero B hB
  have hPmap : (Pℤ.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hPℤ
  change (((d : ℚ)⁻¹ • Pℤ.map (Int.cast : ℤ → ℚ)).det) ≠ 0
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero (Fintype.card (Fin n)) hd) hPmap

/-- The rational cast of the attached-lattice form matrix is the conjugate of
the ambient form matrix by the chosen rational basis matrix. -/
theorem concreteAttachedRationalLatticeFormMatrix_cast_eq_conj
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedRationalLatticeFormMatrix g).map
        (Int.cast : ℤ → ℚ) =
      (L.concreteAttachedRationalLatticeBasisMatrixRat g).transpose *
        L.pairingMatrix.map (Int.cast : ℤ → ℚ) *
          L.concreteAttachedRationalLatticeBasisMatrixRat g := by
  rw [L.concreteAttachedRationalLatticeFormMatrix_cast]
  ext i j
  rw [transpose_mul_rat_form_mul_apply_dot]
  rw [L.concreteAttachedRationalLatticeBasisMatrixRat_col,
    L.concreteAttachedRationalLatticeBasisMatrixRat_col]
  rfl

/-- The integral form matrix in the chosen attached-lattice basis is positive
definite over `ℝ`. -/
theorem concreteAttachedRationalLatticeFormMatrix_posDef
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    ((L.concreteAttachedRationalLatticeFormMatrix g).map
      (Int.cast : ℤ → ℝ)).PosDef := by
  let Pℚ := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let Pℝ : Matrix (Fin n) (Fin n) ℝ := Pℚ.map (Rat.castHom ℝ)
  have hdetℚ : Pℚ.det ≠ 0 := by
    simpa [Pℚ] using
      L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g
  have hdetℝ : Pℝ.det ≠ 0 := by
    have hcast : (Pℚ.det : ℝ) = Pℝ.det := by
      simpa [Pℝ] using (RingHom.map_det (Rat.castHom ℝ) Pℚ)
    rw [← hcast]
    exact_mod_cast hdetℚ
  have hPunit : IsUnit Pℝ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdetℝ
  have hPinj : Function.Injective Pℝ.mulVec :=
    Matrix.mulVec_injective_of_isUnit hPunit
  have hpos := L.form_posDef.conjTranspose_mul_mul_same (B := Pℝ) hPinj
  have hmatrix :
      (L.concreteAttachedRationalLatticeFormMatrix g).map
          (Int.cast : ℤ → ℝ) =
        Pℝ.transpose * L.pairingMatrix.map (Int.cast : ℤ → ℝ) * Pℝ := by
    have hq := L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
    ext i j
    have hij := congr_fun (congr_fun hq i) j
    have hijR := congrArg (fun q : ℚ => (q : ℝ)) hij
    simpa [Pℚ, Pℝ, Matrix.mul_apply] using hijR
  rw [hmatrix]
  simpa [Pℝ, Matrix.conjTranspose_apply] using hpos

/-- The positive-definite based integral lattice attached to a concrete
finite-adelic orthogonal representative. -/
noncomputable def concreteAttachedIntegralLattice
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := L.concreteAttachedRationalLatticeFormMatrix g
  form_symm := L.concreteAttachedRationalLatticeFormMatrix_symm g
  form_posDef := L.concreteAttachedRationalLatticeFormMatrix_posDef g

/-- At a finite place, the integral comparison matrix from the chosen basis of
the attached lattice to the standard completed lattice.  In the ambient local
field it is `g_v⁻¹ P`, where `P` is the rational attached-lattice basis
matrix. -/
noncomputable def concreteAttachedLocalComparisonMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Matrix (Fin n) (Fin n) (v.adicCompletionIntegers ℚ) :=
  fun i j =>
    ⟨((g.1⁻¹).1.mulVec
        (rationalVectorFiniteAdele
          (L.concreteAttachedRationalLatticeBasis g j).1)) i v,
      ((L.mem_concreteAttachedRationalLatticeSubmodule_iff g
        (L.concreteAttachedRationalLatticeBasis g j).1).mp
          (L.concreteAttachedRationalLatticeBasis g j).property) i v⟩

@[simp]
theorem concreteAttachedLocalComparisonMatrix_apply_coe
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (i j : Fin n) :
    (L.concreteAttachedLocalComparisonMatrix g v i j :
        v.adicCompletion ℚ) =
      ((g.1⁻¹).1.mulVec
        (rationalVectorFiniteAdele
          (L.concreteAttachedRationalLatticeBasis g j).1)) i v := rfl

/-- In the local field, the integral comparison matrix is the product of the
local component of `g⁻¹` and the rational attached-lattice basis matrix. -/
theorem concreteAttachedLocalComparisonMatrix_map_subtype_eq
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (L.concreteAttachedLocalComparisonMatrix g v).map
        (v.adicCompletionIntegers ℚ).subtype =
      (show Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) from
        fun i j => (g.1⁻¹).1 i j v) *
        (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
          (algebraMap ℚ (v.adicCompletion ℚ)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  change (L.concreteAttachedLocalComparisonMatrix g v i j :
    v.adicCompletion ℚ) = _
  rw [L.concreteAttachedLocalComparisonMatrix_apply_coe]
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ => w.adicCompletion ℚ) v
  change ev (∑ k, (g.1⁻¹).1 i k *
      rationalVectorFiniteAdele
        (L.concreteAttachedRationalLatticeBasis g j).1 k) =
    ∑ k, (g.1⁻¹).1 i k v *
      algebraMap ℚ (v.adicCompletion ℚ)
        (L.concreteAttachedRationalLatticeBasisMatrixRat g k j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [map_mul, ev]
  change (g.1⁻¹).1 i k v *
      algebraMap ℚ (v.adicCompletion ℚ)
        ((L.concreteAttachedRationalLatticeBasis g j).1 k) = _
  rw [← congr_fun
    (L.concreteAttachedRationalLatticeBasisMatrixRat_col g j) k]
  rfl

/-- The local integral comparison matrix carries the ambient form to the form
of the attached integral lattice after inclusion into the local field. -/
theorem concreteAttachedLocalComparisonMatrix_form_eq
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let U := (L.concreteAttachedLocalComparisonMatrix g v).map
      (v.adicCompletionIntegers ℚ).subtype
    let F := L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))
    let Fg := (L.concreteAttachedIntegralLattice g).pairingMatrix.map
      (algebraMap ℤ (v.adicCompletion ℚ))
    U.transpose * F * U = Fg := by
  dsimp only
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ => w.adicCompletion ℚ) v
  let Ginv : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) :=
    (g.1⁻¹).1.map ev
  let P : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) :=
    (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
      (algebraMap ℚ (v.adicCompletion ℚ))
  let F : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) :=
    L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))
  have hU :
      (L.concreteAttachedLocalComparisonMatrix g v).map
          (v.adicCompletionIntegers ℚ).subtype = Ginv * P := by
    simpa [Ginv, P, ev] using
      L.concreteAttachedLocalComparisonMatrix_map_subtype_eq g v
  have hFmap : L.finiteAdelicFormMatrix.map ev = F := by
    ext i j
    rfl
  have hGorth : Ginv.transpose * F * Ginv = F := by
    have hg := (g⁻¹).2
    have hmap := congrArg (fun M => M.map ev) hg
    change (((g.1⁻¹).1.transpose * L.finiteAdelicFormMatrix *
      (g.1⁻¹).1).map ev) = L.finiteAdelicFormMatrix.map ev at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [Ginv, hFmap] using hmap
  have hAttached :
      (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (algebraMap ℤ (v.adicCompletion ℚ)) =
        P.transpose * F * P := by
    have hq := L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
    have hmap := congrArg
      (fun M => M.map (algebraMap ℚ (v.adicCompletion ℚ))) hq
    change ((L.concreteAttachedRationalLatticeFormMatrix g).map
        (Int.cast : ℤ → ℚ)).map
          (algebraMap ℚ (v.adicCompletion ℚ)) =
      (((L.concreteAttachedRationalLatticeBasisMatrixRat g).transpose *
          L.pairingMatrix.map (Int.cast : ℤ → ℚ) *
          L.concreteAttachedRationalLatticeBasisMatrixRat g).map
        (algebraMap ℚ (v.adicCompletion ℚ))) at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    calc
      (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (algebraMap ℤ (v.adicCompletion ℚ)) =
          ((L.concreteAttachedRationalLatticeFormMatrix g).map
            (Int.cast : ℤ → ℚ)).map
              (algebraMap ℚ (v.adicCompletion ℚ)) := by
            ext i j
            rfl
      _ = ((L.concreteAttachedRationalLatticeBasisMatrixRat g).map
              (algebraMap ℚ (v.adicCompletion ℚ))).transpose *
            (L.pairingMatrix.map (Int.cast : ℤ → ℚ)).map
              (algebraMap ℚ (v.adicCompletion ℚ)) *
            (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
              (algebraMap ℚ (v.adicCompletion ℚ)) := hmap
      _ = P.transpose * F * P := by
            congr 2
  rw [hU]
  calc
    (Ginv * P).transpose * F * (Ginv * P) =
        P.transpose * (Ginv.transpose * F * Ginv) * P := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = P.transpose * F * P :=
      congrArg (fun X => P.transpose * X * P) hGorth
    _ = (L.concreteAttachedIntegralLattice g).pairingMatrix.map
        (algebraMap ℤ (v.adicCompletion ℚ)) := hAttached.symm

/-- Membership in the local integer ring can be checked after transport to
the corresponding p-adic field. -/
theorem mem_adicCompletionIntegers_iff_padic
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  constructor
  · intro hx
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx
  · intro hx
    obtain ⟨y, hy, heq⟩ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn hx
    have hxy :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective heq
    exact hxy ▸ hy

private theorem concreteAttachedLocalComparisonMatrix_nonunit_kernel
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hU : ¬ IsUnit (L.concreteAttachedLocalComparisonMatrix g v)) :
    let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
    let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
    let B := ((L.concreteAttachedLocalComparisonMatrix g v).map e).map
      (PadicInt.toZMod (p := p))
    ∃ z : Fin n → ZMod p, z ≠ 0 ∧ B.mulVec z = 0 := by
  dsimp only
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let U := L.concreteAttachedLocalComparisonMatrix g v
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := U.map e
  let B : Matrix (Fin n) (Fin n) (ZMod p) := A.map PadicInt.toZMod
  have hdetU : ¬ IsUnit U.det := by
    exact fun h => hU (Matrix.isUnit_iff_isUnit_det U |>.mpr h)
  have hdetA : ¬ IsUnit A.det := by
    have hedet : e U.det = A.det := by
      simp [Matrix.det_apply, A]
    rw [← hedet]
    exact (not_congr (isUnit_map_iff e U.det)).mpr hdetU
  have hdetAker :
      A.det ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact hdetA
  have hdetB : B.det = 0 := by
    have hBdet : PadicInt.toZMod A.det = B.det := by
      simpa [B] using
        RingHom.map_det (PadicInt.toZMod : ℤ_[p] →+* ZMod p) A
    rw [← hBdet]
    exact hdetAker
  simpa [p, e, A, B, U] using
    (Matrix.exists_mulVec_eq_zero_iff.mpr hdetB)

private theorem concreteAttachedLocalComparisonMatrix_nonunit_integerKernel
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hU : ¬ IsUnit (L.concreteAttachedLocalComparisonMatrix g v)) :
    let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
    let U := L.concreteAttachedLocalComparisonMatrix g v
    ∃ c : Fin n → ℤ,
      (∃ i, ¬ (p : ℤ) ∣ c i) ∧
      ∀ i, ∃ y : ℤ_[p],
        Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
            (U.mulVec (fun j =>
              (c j : v.adicCompletionIntegers ℚ)) i) =
          (p : ℤ_[p]) * y := by
  dsimp only
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let U := L.concreteAttachedLocalComparisonMatrix g v
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := U.map e
  let B : Matrix (Fin n) (Fin n) (ZMod p) := A.map PadicInt.toZMod
  obtain ⟨z, hz_ne, hz_zero⟩ :=
    L.concreteAttachedLocalComparisonMatrix_nonunit_kernel g v hU
  let c : Fin n → ℤ := fun i => (z i).val
  have hc_mod (i : Fin n) : (c i : ZMod p) = z i := by
    simpa [c] using ZMod.natCast_zmod_val (z i)
  have hc_not : ∃ i, ¬ (p : ℤ) ∣ c i := by
    have hz_some : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz_ne (funext h)
    obtain ⟨i, hi⟩ := hz_some
    refine ⟨i, ?_⟩
    intro hdiv
    apply hi
    rw [← hc_mod i, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  refine ⟨c, hc_not, ?_⟩
  intro i
  have hz_i := congr_fun hz_zero i
  have hc_res (j : Fin n) :
      PadicInt.toZMod
        (e (c j : v.adicCompletionIntegers ℚ)) = z j := by
    rw [map_intCast, map_intCast, hc_mod]
  have hres :
      PadicInt.toZMod
        (e (U.mulVec
          (fun j => (c j : v.adicCompletionIntegers ℚ)) i)) = 0 := by
    change (B.mulVec z) i = 0 at hz_i
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, hc_res,
      B, A, Matrix.map_apply] using hz_i
  have hker :
      e (U.mulVec (fun j => (c j : v.adicCompletionIntegers ℚ)) i) ∈
        RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := hres
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at hker
  obtain ⟨y, hy⟩ := hker
  exact ⟨y, hy⟩

private theorem inv_mulVec_attachedBasisMatrix_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (a : Fin n → ℚ)
    (w : IsDedekindDomain.HeightOneSpectrum ℤ) (i : Fin n) :
    ((g.1⁻¹).1.mulVec
        (rationalVectorFiniteAdele
          ((L.concreteAttachedRationalLatticeBasisMatrixRat g).mulVec a)) i) w =
      ((L.concreteAttachedLocalComparisonMatrix g w).map
          (w.adicCompletionIntegers ℚ).subtype).mulVec
        (fun j => algebraMap ℚ (w.adicCompletion ℚ) (a j)) i := by
  rw [← rationalMatrix_map_mulVec_rationalVectorFiniteAdele]
  rw [Matrix.mulVec_mulVec]
  rw [L.concreteAttachedLocalComparisonMatrix_map_subtype_eq]
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct,
    rationalVectorFiniteAdele]
  let ev : RationalFiniteAdele →+* w.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun u : IsDedekindDomain.HeightOneSpectrum ℤ => u.adicCompletion ℚ) w
  change ev (∑ x, (g.1⁻¹).1 i x *
      ∑ y, algebraMap ℚ RationalFiniteAdele
        (L.concreteAttachedRationalLatticeBasisMatrixRat g x y) *
          algebraMap ℚ RationalFiniteAdele (a y)) = _
  rw [map_sum]
  simp only [map_mul, map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
  have hev (z : ℚ) :
      ev (algebraMap ℚ RationalFiniteAdele z) =
        algebraMap ℚ (w.adicCompletion ℚ) z := rfl
  simp only [hev, Matrix.map_apply]
  rw [Finset.sum_comm]
  rfl

private theorem inv_heightOnePrime_mem_adicCompletionIntegers
    (v w : IsDedekindDomain.HeightOneSpectrum ℤ) (hvw : w ≠ v) :
    algebraMap ℚ (w.adicCompletion ℚ)
        (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ)⁻¹) ∈
      w.adicCompletionIntegers ℚ := by
  rw [mem_adicCompletionIntegers_iff_padic]
  rw [map_inv₀, map_inv₀, map_natCast]
  have hpq : (Rat.HeightOneSpectrum.primesEquiv w : ℕ) ≠
      (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
    exact fun h => hvw (Rat.HeightOneSpectrum.primesEquiv.injective
      (Subtype.ext h))
  have hnorm : ‖((Rat.HeightOneSpectrum.primesEquiv v : ℕ) :
      ℚ_[Rat.HeightOneSpectrum.primesEquiv w])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Rat.HeightOneSpectrum.primesEquiv w).property.coprime_iff_not_dvd.mpr
      (fun hdiv => hpq
        ((Nat.dvd_prime (Rat.HeightOneSpectrum.primesEquiv v).property).mp hdiv
          |>.resolve_left
            (Rat.HeightOneSpectrum.primesEquiv w).property.ne_one))
  rw [PadicInt.mem_subring_iff, norm_inv]
  have hnorm' :
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv w
        ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) :
          w.adicCompletion ℚ)‖ = 1 := by
    simpa using hnorm
  rw [hnorm', inv_one]

private theorem concreteAttachedLocalComparisonMatrix_nonunit_dividedBasis_mem
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hU : ¬ IsUnit (L.concreteAttachedLocalComparisonMatrix g v)) :
    let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
    ∃ c : Fin n → ℤ,
      (∃ i, ¬ (p : ℤ) ∣ c i) ∧
      ((p : ℚ)⁻¹ •
          (L.concreteAttachedRationalLatticeBasisMatrixRat g).mulVec
            (fun j => (c j : ℚ))) ∈
        L.concreteAttachedRationalLatticeSubmodule g := by
  dsimp only
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  obtain ⟨c, hc_not, hc_div⟩ :=
    L.concreteAttachedLocalComparisonMatrix_nonunit_integerKernel g v hU
  refine ⟨c, hc_not, ?_⟩
  rw [L.mem_concreteAttachedRationalLatticeSubmodule_iff]
  intro i w
  let a : Fin n → ℚ := fun j => (c j : ℚ)
  let s := (L.concreteAttachedRationalLatticeBasisMatrixRat g).mulVec a
  let x : Fin n → ℚ := (p : ℚ)⁻¹ • s
  let Uw := L.concreteAttachedLocalComparisonMatrix g w
  let uw : w.adicCompletionIntegers ℚ :=
    Uw.mulVec (fun j => (c j : w.adicCompletionIntegers ℚ)) i
  have hbase := L.inv_mulVec_attachedBasisMatrix_apply g a w i
  have hbase' :
      ((g.1⁻¹).1.mulVec (rationalVectorFiniteAdele s) i) w =
        (uw : w.adicCompletion ℚ) := by
    simpa [s, a, uw, Uw, Matrix.mulVec, dotProduct] using hbase
  have hxval :
      ((g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x) i) w =
        algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)⁻¹) *
          (uw : w.adicCompletion ℚ) := by
    have hxvec :
        rationalVectorFiniteAdele x =
          algebraMap ℚ RationalFiniteAdele ((p : ℚ)⁻¹) •
            rationalVectorFiniteAdele s := by
      ext j u
      simp [x, rationalVectorFiniteAdele]
    rw [hxvec, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    change algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)⁻¹) *
      (((g.1⁻¹).1.mulVec (rationalVectorFiniteAdele s) i) w) = _
    rw [hbase']
  change ((g.1⁻¹).1.mulVec (rationalVectorFiniteAdele x) i) w ∈
    w.adicCompletionIntegers ℚ
  rw [hxval]
  by_cases hwv : w = v
  · subst w
    rw [mem_adicCompletionIntegers_iff_padic]
    obtain ⟨y, hy⟩ := hc_div i
    have huw :
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
            (uw : v.adicCompletion ℚ) =
          (p : ℚ_[p]) * (y : ℚ_[p]) := by
      simpa [uw, Uw] using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hy
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
      (algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) *
        (uw : v.adicCompletion ℚ)) ∈ PadicInt.subring p
    rw [map_mul, map_inv₀, map_natCast, huw]
    have hpmap :
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
          (((p : ℕ) : v.adicCompletion ℚ)⁻¹) =
            ((p : ℚ_[p])⁻¹) := by
      rw [map_inv₀]
      simp
    rw [hpmap]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    · exact y.property
    · exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero
  · exact Subring.mul_mem _
      (inv_heightOnePrime_mem_adicCompletionIntegers v w hwv)
      uw.property

/-- The primewise comparison from the completed attached lattice to the
standard completed coordinate lattice is invertible over the local integer
ring. -/
theorem concreteAttachedLocalComparisonMatrix_isUnit
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsUnit (L.concreteAttachedLocalComparisonMatrix g v) := by
  by_contra hU
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  obtain ⟨c, hc_not, hx⟩ :=
    L.concreteAttachedLocalComparisonMatrix_nonunit_dividedBasis_mem g v hU
  let P := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let x : Fin n → ℚ := (p : ℚ)⁻¹ • P.mulVec (fun j => (c j : ℚ))
  let M := L.concreteAttachedRationalLatticeSubmodule g
  let b := L.concreteAttachedRationalLatticeBasis g
  let xM : M := ⟨x, by
    change x ∈ L.concreteAttachedRationalLatticeSubmodule g
    simpa [x, P, p] using hx⟩
  have hpx : (p : ℤ) • xM = ∑ j, c j • b j := by
    apply Subtype.ext
    ext i
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (p : ℚ) * ((p : ℚ)⁻¹ * P.mulVec
        (fun j => (c j : ℚ)) i) =
      ∑ j, (c j : ℚ) * (b j).1 i
    rw [← mul_assoc, mul_inv_cancel₀]
    · rw [one_mul]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [mul_comm]
      congr 1
    · exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero
  have hcoords := congrArg b.equivFun hpx
  obtain ⟨i, hi⟩ := hc_not
  apply hi
  refine ⟨(b.equivFun xM) i, ?_⟩
  have hcoord_i := congr_fun hcoords i
  have hsum :
      (b.equivFun (∑ j, c j • b j)) i = c i := by
    calc
      (b.equivFun (∑ j, c j • b j)) i =
          (b.equivFun (b.equivFun.symm c)) i := by
        exact congr_fun (congrArg b.equivFun
          (Module.Basis.equivFun_symm_apply b c).symm) i
      _ = c i := congr_fun (b.equivFun.apply_symm_apply c) i
  rw [map_zsmul, hsum] at hcoord_i
  exact hcoord_i.symm

/-- The local comparison matrix carries the ambient form to the attached form
already over the local integer ring. -/
theorem concreteAttachedLocalComparisonMatrix_form_eq_integral
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let U := L.concreteAttachedLocalComparisonMatrix g v
    let F := L.pairingMatrix.map
      (algebraMap ℤ (v.adicCompletionIntegers ℚ))
    let Fg := (L.concreteAttachedIntegralLattice g).pairingMatrix.map
      (algebraMap ℤ (v.adicCompletionIntegers ℚ))
    U.transpose * F * U = Fg := by
  dsimp only
  ext i j
  have h := congr_fun (congr_fun
    (L.concreteAttachedLocalComparisonMatrix_form_eq g v) i) j
  simpa [Matrix.mul_apply] using h

/-- Every concrete attached integral lattice belongs to the genus of the
original lattice. -/
theorem concreteAttachedIntegralLattice_isSameGenus
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.IsSameGenus (L.concreteAttachedIntegralLattice g) := by
  apply isSameGenus_symm
  constructor
  · intro p hp
    let q : Nat.Primes := ⟨p, hp.out⟩
    let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
      Rat.HeightOneSpectrum.primesEquiv.symm q
    let pv := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
    letI : Fact (Nat.Prime pv) :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
    let e : v.adicCompletionIntegers ℚ ≃+* ℤ_[pv] := by
      letI : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
        Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
      exact
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
    let er : v.adicCompletionIntegers ℚ →+* ℤ_[pv] := e.toRingHom
    let Uv := L.concreteAttachedLocalComparisonMatrix g v
    let U : Matrix (Fin n) (Fin n) ℤ_[pv] := Uv.map er
    have hlocal :
        (L.concreteAttachedIntegralLattice g).IsLocallyIsometricAt L pv := by
      refine ⟨U, ?_, ?_⟩
      · have hunit := L.concreteAttachedLocalComparisonMatrix_isUnit g v
        exact hunit.map er.mapMatrix
      · have hv := L.concreteAttachedLocalComparisonMatrix_form_eq_integral g v
        have hmap := congrArg (fun M => M.map er) hv
        dsimp only at hmap
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
        have hmap_int (A : Matrix (Fin n) (Fin n) ℤ) :
            (A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map er =
              A.map (Int.castRingHom ℤ_[pv]) := by
          ext i j
          simp [er, e]
        change U.transpose * L.pairingMatrix.map (Int.castRingHom ℤ_[pv]) * U =
          (L.concreteAttachedIntegralLattice g).pairingMatrix.map
            (Int.castRingHom ℤ_[pv])
        rw [← hmap_int L.pairingMatrix,
          ← hmap_int (L.concreteAttachedIntegralLattice g).pairingMatrix]
        simpa [U, Uv] using hmap
    simpa [pv, v, q] using hlocal
  · let Pℚ := L.concreteAttachedRationalLatticeBasisMatrixRat g
    let Pℝ : Matrix (Fin n) (Fin n) ℝ := Pℚ.map (Rat.castHom ℝ)
    have hdetℚ : Pℚ.det ≠ 0 := by
      simpa [Pℚ] using
        L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g
    have hdetℝ : Pℝ.det ≠ 0 := by
      have hcast : (Pℚ.det : ℝ) = Pℝ.det := by
        simpa [Pℝ] using (RingHom.map_det (Rat.castHom ℝ) Pℚ)
      rw [← hcast]
      exact_mod_cast hdetℚ
    refine ⟨Pℝ, ?_, ?_⟩
    · rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdetℝ
    have hq := L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
    have hreal :
        (L.concreteAttachedIntegralLattice g).pairingMatrix_real =
          Pℝ.transpose * L.pairingMatrix_real * Pℝ := by
      ext i j
      have hij := congr_fun (congr_fun hq i) j
      have hijR := congrArg (fun z : ℚ => (z : ℝ)) hij
      simpa [concreteAttachedIntegralLattice, Pℚ, Pℝ, pairingMatrix_real,
        Matrix.mul_apply] using hijR
    change Pℝ.transpose * L.pairingMatrix_real * Pℝ =
      (L.concreteAttachedIntegralLattice g).pairingMatrix_real
    exact hreal.symm

/-- The integral basis transition underlying the attached lattice of the
conditional representative `diag(P) U`. -/
theorem exists_concreteAttachedIntegralLattice_representativeOfRationalComparison_basisChange
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (Ulocal : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hUlocal : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (Ulocal v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    ∃ T : Matrix (Fin n) (Fin n) ℤ,
      IsUnit T ∧
      P.1 * T.map (Int.castRingHom ℚ) =
        L.concreteAttachedRationalLatticeBasisMatrixRat
          (L.concreteFiniteAdelicRepresentativeOfRationalComparison
            M P hP Ulocal hUlocal) ∧
      Tᵀ * M.pairingMatrix * T =
        (L.concreteAttachedIntegralLattice
          (L.concreteFiniteAdelicRepresentativeOfRationalComparison
            M P hP Ulocal hUlocal)).pairingMatrix := by
  classical
  let g := L.concreteFiniteAdelicRepresentativeOfRationalComparison
    M P hP Ulocal hUlocal
  let S := L.concreteAttachedRationalLatticeSubmodule g
  have hS : P.1.mulVec '' (rationalIntegralCoordinateSubmodule n : Set (Fin n → ℚ)) =
      (S : Set (Fin n → ℚ)) := by
    exact L.concreteAttachedRationalLatticeSubmodule_representativeOfRationalComparison
      M P hP Ulocal hUlocal
  let f : (Fin n → ℤ) →ₗ[ℤ] S :=
    { toFun := fun z => ⟨P.1.mulVec (intVectorToRatLinear n z), by
          change P.1.mulVec (intVectorToRatLinear n z) ∈ (S : Set (Fin n → ℚ))
          rw [← hS]
          exact ⟨intVectorToRatLinear n z, ⟨z, rfl⟩, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change P.1.mulVec (intVectorToRatLinear n (a • x)) =
          a • P.1.mulVec (intVectorToRatLinear n x)
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply,
          intVectorToRatLinear_apply, smul_eq_mul]
        change (∑ k, P.1 i k * ((a * x k : ℤ) : ℚ)) =
          (a : ℚ) * ∑ k, P.1 i k * (x k : ℚ)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [Int.cast_mul]
        ring }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hval := congrArg Subtype.val hxy
    have hPinj : Function.Injective P.1.mulVec :=
      Matrix.mulVec_injective_of_isUnit P.isUnit
    exact intVectorToRatLinear_injective n (hPinj hval)
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : Fin n → ℚ) ∈
        P.1.mulVec '' (rationalIntegralCoordinateSubmodule n : Set (Fin n → ℚ)) := by
      rw [hS]
      exact y.property
    rcases hy with ⟨x, hx, hxy⟩
    rcases hx with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change P.1.mulVec (intVectorToRatLinear n z) = y
    rw [hz]
    exact hxy
  let e : (Fin n → ℤ) ≃ₗ[ℤ] S := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let bP : Module.Basis (Fin n) ℤ S := (Pi.basisFun ℤ (Fin n)).map e
  let b := L.concreteAttachedRationalLatticeBasis g
  have hbPval (j : Fin n) : ((bP j : S) : Fin n → ℚ) = P.1.col j := by
    change P.1.mulVec
      (intVectorToRatLinear n ((Pi.basisFun ℤ (Fin n)) j)) = P.1.col j
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply]
  let T : Matrix (Fin n) (Fin n) ℤ := bP.toMatrix b
  have hTunit : IsUnit T := by
    letI : Invertible T := bP.invertibleToMatrix b
    exact isUnit_of_invertible T
  let Tq := T.map (Int.castRingHom ℚ)
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  have hchange : P.1 * Tq = B := by
    ext i j
    have hsum : (∑ k, T k j • (bP k : S)) = b j := by
      simpa [T, Module.Basis.toMatrix_apply] using bP.sum_repr (b j)
    calc
      (P.1 * Tq) i j = ∑ k, P.1 i k * (T k j : ℚ) := by
        rw [Matrix.mul_apply]
        rfl
      _ = ∑ k, (T k j : ℚ) * ((bP k : S) : Fin n → ℚ) i := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [hbPval k]
        exact mul_comm _ _
      _ = ((∑ k, T k j • (bP k : S) : S) : Fin n → ℚ) i := by
        let ev : S →ₗ[ℤ] ℚ :=
          { toFun := fun x => (x : Fin n → ℚ) i
            map_add' := fun _ _ => rfl
            map_smul' := by
              intro a x
              change ((a : ℚ) * x.1 i) = (a : ℚ) * x.1 i
              rfl }
        change (∑ k, (T k j : ℚ) * ((bP k : S) : Fin n → ℚ) i) =
          ev (∑ k, T k j • (bP k : S))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [map_smul]
        rfl
      _ = ((b j : S) : Fin n → ℚ) i := by
        exact congrFun (congrArg Subtype.val hsum) i
      _ = B i j := by
        have hcol :=
          L.concreteAttachedRationalLatticeBasisMatrixRat_col g j
        exact (congrFun hcol i).symm
  have hformQ :
      Tqᵀ * M.rationalFormMatrix * Tq =
        (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) := by
    calc
      Tqᵀ * M.rationalFormMatrix * Tq =
          Tqᵀ * (P.1ᵀ * L.rationalFormMatrix * P.1) * Tq := by rw [hP]
      _ = (P.1 * Tq)ᵀ * L.rationalFormMatrix * (P.1 * Tq) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = Bᵀ * L.rationalFormMatrix * B := by rw [hchange]
      _ = (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) := by
        exact (L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g).symm
  refine ⟨T, hTunit, hchange, ?_⟩
  apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  change (Tᵀ * M.pairingMatrix * T).map (Int.castRingHom ℚ) =
    (L.concreteAttachedIntegralLattice g).pairingMatrix.map (Int.castRingHom ℚ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  exact hformQ

/-- The attached integral lattice of the conditional representative
`diag(P) U` is globally isometric to the target lattice. -/
theorem concreteAttachedIntegralLattice_representativeOfRationalComparison_isGlobalIsometry
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (Ulocal : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hUlocal : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (Ulocal v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    (L.concreteAttachedIntegralLattice
      (L.concreteFiniteAdelicRepresentativeOfRationalComparison
        M P hP Ulocal hUlocal)).IsGlobalIsometry M := by
  obtain ⟨T, hTunit, _hchange, hTform⟩ :=
    L.exists_concreteAttachedIntegralLattice_representativeOfRationalComparison_basisChange
      M P hP Ulocal hUlocal
  exact ⟨T, hTunit, hTform⟩

/-- The explicit integral basis change underlying invariance of the attached
lattice under left rational translation and right stabilizer translation. -/
theorem exists_concreteAttachedIntegralLattice_rational_mul_stabilizer_basisChange
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.rationalOrthogonalMatrixSubgroup)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (h : L.finiteLocalLatticeStabilizerSubgroup) :
    ∃ T : Matrix (Fin n) (Fin n) ℤ,
      IsUnit T ∧
      q.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g *
          T.map (Int.cast : ℤ → ℚ) =
        L.concreteAttachedRationalLatticeBasisMatrixRat
          (L.rationalOrthogonalDiagonalHom q * g *
            (h : L.ConcreteFiniteAdelicOrthogonalGroup)) ∧
      Tᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix * T =
        (L.concreteAttachedIntegralLattice
          (L.rationalOrthogonalDiagonalHom q * g *
            (h : L.ConcreteFiniteAdelicOrthogonalGroup))).pairingMatrix := by
  classical
  let g' := L.rationalOrthogonalDiagonalHom q * g *
    (h : L.ConcreteFiniteAdelicOrthogonalGroup)
  let S := L.concreteAttachedRationalLatticeSubmodule g
  let S' := L.concreteAttachedRationalLatticeSubmodule g'
  have hS : q.1.1.mulVec '' (S : Set (Fin n → ℚ)) =
      (S' : Set (Fin n → ℚ)) := by
    calc
      q.1.1.mulVec '' (S : Set (Fin n → ℚ)) =
          (L.concreteAttachedRationalLatticeSubmodule
            (L.rationalOrthogonalDiagonalHom q * g) : Set (Fin n → ℚ)) :=
        L.rational_mulVec_image_concreteAttachedRationalLatticeSubmodule q g
      _ = (S' : Set (Fin n → ℚ)) := by
        change
          (L.concreteAttachedRationalLatticeSubmodule
              (L.rationalOrthogonalDiagonalHom q * g) : Set (Fin n → ℚ)) =
            (L.concreteAttachedRationalLatticeSubmodule
              ((L.rationalOrthogonalDiagonalHom q * g) * h) : Set (Fin n → ℚ))
        rw [L.concreteAttachedRationalLatticeSubmodule_mul_finiteLocalStabilizer]
  let f : S →ₗ[ℤ] S' :=
    { toFun := fun x => ⟨q.1.1.mulVec x, by
          change q.1.1.mulVec (x : Fin n → ℚ) ∈ (S' : Set (Fin n → ℚ))
          rw [← hS]
          exact ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change q.1.1.mulVec (a • (x : Fin n → ℚ)) =
          a • q.1.1.mulVec (x : Fin n → ℚ)
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
        change (∑ k, q.1.1 i k * ((a : ℚ) * x.1 k)) =
          (a : ℚ) * ∑ k, q.1.1 i k * x.1 k
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact Matrix.mulVec_injective_of_isUnit q.1.isUnit hval
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : Fin n → ℚ) ∈
        q.1.1.mulVec '' (S : Set (Fin n → ℚ)) := by
      rw [hS]
      exact y.property
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let e : S ≃ₗ[ℤ] S' := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let b := L.concreteAttachedRationalLatticeBasis g
  let b' := L.concreteAttachedRationalLatticeBasis g'
  let bq : Module.Basis (Fin n) ℤ S' := b.map e
  have hbqval (j : Fin n) :
      ((bq j : S') : Fin n → ℚ) = q.1.1.mulVec (b j : Fin n → ℚ) := by
    rfl
  let T : Matrix (Fin n) (Fin n) ℤ := bq.toMatrix b'
  have hTunit : IsUnit T := by
    letI : Invertible T := bq.invertibleToMatrix b'
    exact isUnit_of_invertible T
  let Tq := T.map (Int.castRingHom ℚ)
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let B' := L.concreteAttachedRationalLatticeBasisMatrixRat g'
  have hbqcol (j : Fin n) :
      ((bq j : S') : Fin n → ℚ) = (q.1.1 * B).col j := by
    rw [hbqval, ← L.concreteAttachedRationalLatticeBasisMatrixRat_col g j]
    ext i
    change (∑ k, q.1.1 i k * B k j) = ∑ k, q.1.1 i k * B k j
    rfl
  have hchange : q.1.1 * B * Tq = B' := by
    ext i j
    have hsum : (∑ k, T k j • (bq k : S')) = b' j := by
      simpa [T, Module.Basis.toMatrix_apply] using bq.sum_repr (b' j)
    calc
      (q.1.1 * B * Tq) i j =
          ∑ k, (q.1.1 * B) i k * (T k j : ℚ) := by
        rw [Matrix.mul_apply]
        rfl
      _ = ∑ k, (T k j : ℚ) * ((bq k : S') : Fin n → ℚ) i := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [hbqcol k]
        exact mul_comm _ _
      _ = ((∑ k, T k j • (bq k : S') : S') : Fin n → ℚ) i := by
        let ev : S' →ₗ[ℤ] ℚ :=
          { toFun := fun x => (x : Fin n → ℚ) i
            map_add' := fun _ _ => rfl
            map_smul' := by
              intro a x
              change ((a : ℚ) * x.1 i) = (a : ℚ) * x.1 i
              rfl }
        change (∑ k, (T k j : ℚ) * ((bq k : S') : Fin n → ℚ) i) =
          ev (∑ k, T k j • (bq k : S'))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [map_smul]
        rfl
      _ = ((b' j : S') : Fin n → ℚ) i := by
        exact congrFun (congrArg Subtype.val hsum) i
      _ = B' i j := by
        have hcol :=
          L.concreteAttachedRationalLatticeBasisMatrixRat_col g' j
        exact (congrFun hcol i).symm
  have hq : q.1.1ᵀ * L.rationalFormMatrix * q.1.1 =
      L.rationalFormMatrix := q.property
  have hBg :
      (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) =
        Bᵀ * L.rationalFormMatrix * B := by
    simpa [concreteAttachedIntegralLattice, B, rationalFormMatrix] using
      L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
  have hBg' :
      (L.concreteAttachedIntegralLattice g').pairingMatrix.map
          (Int.castRingHom ℚ) =
        B'ᵀ * L.rationalFormMatrix * B' := by
    simpa [concreteAttachedIntegralLattice, B', rationalFormMatrix] using
      L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g'
  have hformQ :
      Tqᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) * Tq =
        (L.concreteAttachedIntegralLattice g').pairingMatrix.map
          (Int.castRingHom ℚ) := by
    calc
      Tqᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) * Tq =
          Tqᵀ * (Bᵀ * L.rationalFormMatrix * B) * Tq := by
        rw [hBg]
      _ = Tqᵀ * (Bᵀ * (q.1.1ᵀ * L.rationalFormMatrix * q.1.1) * B) *
          Tq := by rw [hq]
      _ = (q.1.1 * B * Tq)ᵀ * L.rationalFormMatrix *
          (q.1.1 * B * Tq) := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = B'ᵀ * L.rationalFormMatrix * B' := by rw [hchange]
      _ = (L.concreteAttachedIntegralLattice g').pairingMatrix.map
          (Int.castRingHom ℚ) := by
        exact hBg'.symm
  refine ⟨T, hTunit, hchange, ?_⟩
  apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  change (Tᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix * T).map
      (Int.castRingHom ℚ) =
    (L.concreteAttachedIntegralLattice g').pairingMatrix.map (Int.castRingHom ℚ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  exact hformQ

/-- Left rational translation and right translation by the finite local
stabilizer preserve the global class of the attached integral lattice. -/
theorem concreteAttachedIntegralLattice_rational_mul_stabilizer_isGlobalIsometry
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.rationalOrthogonalMatrixSubgroup)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (h : L.finiteLocalLatticeStabilizerSubgroup) :
    (L.concreteAttachedIntegralLattice
      (L.rationalOrthogonalDiagonalHom q * g *
        (h : L.ConcreteFiniteAdelicOrthogonalGroup))).IsGlobalIsometry
      (L.concreteAttachedIntegralLattice g) := by
  rcases
      L.exists_concreteAttachedIntegralLattice_rational_mul_stabilizer_basisChange
        q g h with ⟨T, hTunit, _hchange, hform⟩
  exact ⟨T, hTunit, hform⟩

/-- The concrete rational double quotient maps to the finite genus by taking
the global isometry class of the attached lattice of the chosen quotient
representative. -/
noncomputable def concreteDoubleCosetToGenus
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteRationalDoubleCosetSet → L.genus :=
  fun C =>
    let g := Quot.out C
    let M := L.concreteAttachedIntegralLattice g
    ⟨M.globalIsometryClass,
      ⟨M, L.concreteAttachedIntegralLattice_isSameGenus g, rfl⟩⟩

/-- Related concrete representatives have globally isometric attached
lattices. -/
theorem concreteRelated_attached_globalIsometryClass_eq
    (L : PositiveDefiniteIntegralLattice n)
    (g g' : L.ConcreteFiniteAdelicOrthogonalGroup)
    (hrel : IsLeftRightDoubleCosetRelated
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup g g') :
    (L.concreteAttachedIntegralLattice g).globalIsometryClass =
      (L.concreteAttachedIntegralLattice g').globalIsometryClass := by
  rcases hrel with ⟨gamma, h, rfl⟩
  rcases gamma.property with ⟨q, hq⟩
  have hiso :=
    L.concreteAttachedIntegralLattice_rational_mul_stabilizer_isGlobalIsometry
      q g h
  rw [hq] at hiso
  exact (globalIsometryClass_eq_of_isGlobalIsometry hiso).symm

/-- Evaluation of the attached-lattice genus map on an explicit concrete
double-coset representative. -/
theorem concreteDoubleCosetToGenus_mk
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteDoubleCosetToGenus
        (Quot.mk (leftRightDoubleCosetSetoid
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup) g) =
      ⟨(L.concreteAttachedIntegralLattice g).globalIsometryClass,
        ⟨L.concreteAttachedIntegralLattice g,
          L.concreteAttachedIntegralLattice_isSameGenus g, rfl⟩⟩ := by
  apply Subtype.ext
  change (L.concreteAttachedIntegralLattice
      (Quot.out (Quot.mk (leftRightDoubleCosetSetoid
        L.rationalOrthogonalDiagonalSubgroup
        L.finiteLocalLatticeStabilizerSubgroup) g))).globalIsometryClass = _
  apply L.concreteRelated_attached_globalIsometryClass_eq
  exact Quotient.exact (Quot.out_eq
    (Quot.mk (leftRightDoubleCosetSetoid
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup) g))

/-- To prove the concrete double-quotient-to-genus map injective, it suffices
to recover the raw left-right double-coset relation from equality of attached
global isometry classes. -/
theorem concreteDoubleCosetToGenus_injective_of_related
    (L : PositiveDefiniteIntegralLattice n)
    (hrelated : ∀ g g' : L.ConcreteFiniteAdelicOrthogonalGroup,
      (L.concreteAttachedIntegralLattice g).globalIsometryClass =
          (L.concreteAttachedIntegralLattice g').globalIsometryClass →
        IsLeftRightDoubleCosetRelated
          L.rationalOrthogonalDiagonalSubgroup
          L.finiteLocalLatticeStabilizerSubgroup g g') :
    Function.Injective L.concreteDoubleCosetToGenus := by
  intro C D hCD
  rw [← Quot.out_eq C, ← Quot.out_eq D]
  exact Quotient.sound
    (hrelated (Quot.out C) (Quot.out D) (Subtype.ext_iff.mp hCD))

/-- An explicit integral isometry matrix between two attached Gram matrices
determines a rational orthogonal change of ambient coordinates carrying the
chosen basis of the first attached lattice to the chosen basis of the second. -/
theorem exists_rationalOrthogonal_of_attached_isometryMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g g' : L.ConcreteFiniteAdelicOrthogonalGroup)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U)
    (hUform :
      U.transpose * (L.concreteAttachedIntegralLattice g').pairingMatrix * U =
        (L.concreteAttachedIntegralLattice g).pairingMatrix) :
    ∃ q : L.rationalOrthogonalMatrixSubgroup,
      q.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g =
        L.concreteAttachedRationalLatticeBasisMatrixRat g' *
          U.map (Int.castRingHom ℚ) := by
  let P := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let P' := L.concreteAttachedRationalLatticeBasisMatrixRat g'
  let Uq := U.map (Int.castRingHom ℚ)
  let F := L.rationalFormMatrix
  let Fg := (L.concreteAttachedIntegralLattice g).pairingMatrix.map
    (Int.castRingHom ℚ)
  let Fg' := (L.concreteAttachedIntegralLattice g').pairingMatrix.map
    (Int.castRingHom ℚ)
  let Q := P' * Uq * P⁻¹
  have hP : IsUnit P := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr
      (L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g)
  have hP' : IsUnit P' := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr
      (L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g')
  have hUq : IsUnit Uq := hU.map (Int.castRingHom ℚ).mapMatrix
  have hPinv : IsUnit P⁻¹ := by
    rwa [Matrix.isUnit_nonsing_inv_iff]
  have hQ : IsUnit Q := by
    simpa [Q] using (hP'.mul hUq).mul hPinv
  let qGL : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mk' Q
    ((Matrix.isUnit_iff_isUnit_det Q).mp hQ).invertible
  have hPg : Fg = P.transpose * F * P := by
    change (L.concreteAttachedRationalLatticeFormMatrix g).map
      (Int.castRingHom ℚ) = P.transpose * F * P
    simpa [P, F, rationalFormMatrix] using
      L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
  have hPg' : Fg' = P'.transpose * F * P' := by
    change (L.concreteAttachedRationalLatticeFormMatrix g').map
      (Int.castRingHom ℚ) = P'.transpose * F * P'
    simpa [P', F, rationalFormMatrix] using
      L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g'
  have hUformq : Uq.transpose * Fg' * Uq = Fg := by
    ext i j
    have hij := congr_fun (congr_fun hUform i) j
    have hijq := congrArg (fun z : ℤ => (z : ℚ)) hij
    simpa [Uq, Fg, Fg', Matrix.mul_apply] using hijq
  have hQform : Q.transpose * F * Q = F := by
    calc
      Q.transpose * F * Q =
          (P⁻¹).transpose *
            (Uq.transpose * (P'.transpose * F * P') * Uq) * P⁻¹ := by
        simp only [Q, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (P⁻¹).transpose * (Uq.transpose * Fg' * Uq) * P⁻¹ := by
        rw [hPg']
      _ = (P⁻¹).transpose * Fg * P⁻¹ := by rw [hUformq]
      _ = (P⁻¹).transpose * (P.transpose * F * P) * P⁻¹ := by rw [hPg]
      _ = F := by
        have hleft : (P⁻¹).transpose * P.transpose = 1 := by
          rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv P
            ((Matrix.isUnit_iff_isUnit_det P).mp hP), Matrix.transpose_one]
        have hright : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P
          ((Matrix.isUnit_iff_isUnit_det P).mp hP)
        calc
          (P⁻¹).transpose * (P.transpose * F * P) * P⁻¹ =
              ((P⁻¹).transpose * P.transpose) * F * (P * P⁻¹) := by
            noncomm_ring
          _ = F := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  let q : L.rationalOrthogonalMatrixSubgroup := ⟨qGL, by
    simpa [qGL] using hQform⟩
  refine ⟨q, ?_⟩
  have hQP : Q * P = P' * Uq := by
    change (P' * Uq * P⁻¹) * P = P' * Uq
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul P
      ((Matrix.isUnit_iff_isUnit_det P).mp hP), Matrix.mul_one]
  simpa [q, qGL] using hQP

/-- A global integral isometry between two attached Gram matrices determines
a rational orthogonal change of ambient coordinates carrying the chosen basis
of the first attached lattice to the chosen basis of the second. -/
theorem exists_rationalOrthogonal_of_attached_globalIsometry
    (L : PositiveDefiniteIntegralLattice n)
    (g g' : L.ConcreteFiniteAdelicOrthogonalGroup)
    (hiso : (L.concreteAttachedIntegralLattice g).IsGlobalIsometry
      (L.concreteAttachedIntegralLattice g')) :
    ∃ q : L.rationalOrthogonalMatrixSubgroup,
      ∃ U : Matrix (Fin n) (Fin n) ℤ,
        IsUnit U ∧
        U.transpose * (L.concreteAttachedIntegralLattice g').pairingMatrix * U =
          (L.concreteAttachedIntegralLattice g).pairingMatrix ∧
        q.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g =
          L.concreteAttachedRationalLatticeBasisMatrixRat g' *
            U.map (Int.castRingHom ℚ) := by
  obtain ⟨U, hU, hUform⟩ := hiso
  obtain ⟨q, hbasis⟩ :=
    L.exists_rationalOrthogonal_of_attached_isometryMatrix g g' U hU hUform
  exact ⟨q, U, hU, hUform, hbasis⟩

/-- The chosen rational basis matrix of an attached lattice, bundled as a
general linear matrix. -/
noncomputable def concreteAttachedRationalLatticeBasisGL
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) : GL (Fin n) ℚ :=
  (show IsUnit (L.concreteAttachedRationalLatticeBasisMatrixRat g) by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr
      (L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g)).unit

@[simp]
theorem concreteAttachedRationalLatticeBasisGL_val
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    (L.concreteAttachedRationalLatticeBasisGL g).1 =
      L.concreteAttachedRationalLatticeBasisMatrixRat g := by
  exact IsUnit.unit_spec _

/-- The finite-adelic comparison from the attached lattice basis to the
standard completed coordinate lattice. -/
noncomputable def concreteAttachedBasisComparisonGL
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    GL (Fin n) RationalFiniteAdele :=
  g.1⁻¹ * Matrix.GeneralLinearGroup.map
    (algebraMap ℚ RationalFiniteAdele)
      (L.concreteAttachedRationalLatticeBasisGL g)

/-- At each finite place, the global attached-basis comparison is the local
integral comparison unit constructed above. -/
theorem concreteAttachedBasisComparisonGL_map_eval
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ => w.adicCompletion ℚ) v
    Matrix.GeneralLinearGroup.map ev
        (L.concreteAttachedBasisComparisonGL g) =
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
          (L.concreteAttachedLocalComparisonMatrix_isUnit g v).unit := by
  dsimp only
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply]
  rw [IsUnit.unit_spec]
  simp only [concreteAttachedBasisComparisonGL, Units.val_mul]
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ => w.adicCompletion ℚ) v
  calc
    ev (((g.1⁻¹).1 *
        (Matrix.GeneralLinearGroup.map
          (algebraMap ℚ RationalFiniteAdele)
            (L.concreteAttachedRationalLatticeBasisGL g)).1) i j) =
        (((g.1⁻¹).1.map ev) *
          (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
            (algebraMap ℚ (v.adicCompletion ℚ))) i j := by
      simp [Matrix.mul_apply, ev]
    _ = (v.adicCompletionIntegers ℚ).subtype
        (L.concreteAttachedLocalComparisonMatrix g v i j) := by
      have h := congr_fun (congr_fun
        (L.concreteAttachedLocalComparisonMatrix_map_subtype_eq g v) i) j
      simpa [ev, Matrix.map_apply] using h.symm

/-- Both the attached-basis comparison and its inverse are everywhere
integral finite-adelic matrices. -/
theorem concreteAttachedBasisComparisonGL_mem_matrixUnitsOverSubring
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteAttachedBasisComparisonGL g ∈
      matrixUnitsOverSubring integralFiniteAdeleSubring := by
  rw [mem_matrixUnitsOverSubring_iff]
  constructor
  · intro i j v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ => w.adicCompletion ℚ) v
    let U := L.concreteAttachedLocalComparisonMatrix g v
    have hmap := congrArg (fun A : GL (Fin n) (v.adicCompletion ℚ) => A.1 i j)
      (L.concreteAttachedBasisComparisonGL_map_eval g v)
    change ((L.concreteAttachedBasisComparisonGL g).1 i j) v ∈
      v.adicCompletionIntegers ℚ
    change ev ((L.concreteAttachedBasisComparisonGL g).1 i j) ∈ _
    change ev ((L.concreteAttachedBasisComparisonGL g).1 i j) =
      (v.adicCompletionIntegers ℚ).subtype
        ((L.concreteAttachedLocalComparisonMatrix_isUnit g v).unit.1 i j) at hmap
    rw [hmap]
    exact ((L.concreteAttachedLocalComparisonMatrix_isUnit g v).unit.1 i j).property
  · intro i j v
    let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
      RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ => w.adicCompletion ℚ) v
    let U := L.concreteAttachedLocalComparisonMatrix g v
    have hmap := congrArg Inv.inv
      (L.concreteAttachedBasisComparisonGL_map_eval g v)
    have hentry := congrArg
      (fun A : GL (Fin n) (v.adicCompletion ℚ) => A.1 i j) hmap
    change (((L.concreteAttachedBasisComparisonGL g)⁻¹).1 i j) v ∈
      v.adicCompletionIntegers ℚ
    change ev (((L.concreteAttachedBasisComparisonGL g)⁻¹).1 i j) ∈ _
    have hentry' :
        ev (((L.concreteAttachedBasisComparisonGL g)⁻¹).1 i j) =
          (v.adicCompletionIntegers ℚ).subtype
            ((((L.concreteAttachedLocalComparisonMatrix_isUnit g v).unit)⁻¹).1 i j) := by
      simpa only [map_inv, Matrix.GeneralLinearGroup.map_apply] using hentry
    rw [hentry']
    exact
      (((L.concreteAttachedLocalComparisonMatrix_isUnit g v).unit)⁻¹.1 i j).property

/-- An integral matrix unit embedded diagonally in the finite-adelic general
linear group. -/
noncomputable def integralMatrixFiniteAdeleGL
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U) :
    GL (Fin n) RationalFiniteAdele :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ RationalFiniteAdele) hU.unit

theorem integralMatrixFiniteAdeleGL_mem_matrixUnitsOverSubring
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U) :
    integralMatrixFiniteAdeleGL U hU ∈
      matrixUnitsOverSubring integralFiniteAdeleSubring := by
  rw [mem_matrixUnitsOverSubring_iff]
  constructor
  · intro i j
    change (Matrix.GeneralLinearGroup.map
      (algebraMap ℤ RationalFiniteAdele) hU.unit).1 i j ∈ _
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact integer_mem_integralFiniteAdeleSubring (hU.unit.1 i j)
  · intro i j
    change ((Matrix.GeneralLinearGroup.map
      (algebraMap ℤ RationalFiniteAdele) hU.unit)⁻¹).1 i j ∈ _
    rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
    exact integer_mem_integralFiniteAdeleSubring ((hU.unit⁻¹).1 i j)

/-- The residual factor in the recovery of a double-coset relation is in the
finite local lattice stabilizer. -/
theorem concreteAttachedResidual_mem_finiteLocalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n)
    (g g' : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.rationalOrthogonalMatrixSubgroup)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U)
    (hbasis :
      q.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g =
        L.concreteAttachedRationalLatticeBasisMatrixRat g' *
          U.map (Int.castRingHom ℚ)) :
    g⁻¹ * (L.rationalOrthogonalDiagonalHom q)⁻¹ * g' ∈
      L.finiteLocalLatticeStabilizerSubgroup := by
  let P := Matrix.GeneralLinearGroup.map
    (algebraMap ℚ RationalFiniteAdele)
      (L.concreteAttachedRationalLatticeBasisGL g)
  let P' := Matrix.GeneralLinearGroup.map
    (algebraMap ℚ RationalFiniteAdele)
      (L.concreteAttachedRationalLatticeBasisGL g')
  let Ua := integralMatrixFiniteAdeleGL U hU
  let Q := (L.rationalOrthogonalDiagonalHom q).1
  let A := L.concreteAttachedBasisComparisonGL g
  let A' := L.concreteAttachedBasisComparisonGL g'
  have hrel : Q * P = P' * Ua := by
    apply Units.ext
    change q.1.1.map (algebraMap ℚ RationalFiniteAdele) *
        (L.concreteAttachedRationalLatticeBasisMatrixRat g).map
          (algebraMap ℚ RationalFiniteAdele) =
      (L.concreteAttachedRationalLatticeBasisMatrixRat g').map
          (algebraMap ℚ RationalFiniteAdele) *
        U.map (algebraMap ℤ RationalFiniteAdele)
    have hmap := congrArg
      (fun M : Matrix (Fin n) (Fin n) ℚ =>
        M.map (algebraMap ℚ RationalFiniteAdele)) hbasis
    change (q.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g).map
        (algebraMap ℚ RationalFiniteAdele) =
      (L.concreteAttachedRationalLatticeBasisMatrixRat g' *
        U.map (Int.castRingHom ℚ)).map
          (algebraMap ℚ RationalFiniteAdele) at hmap
    rw [Matrix.map_mul, Matrix.map_mul] at hmap
    have hUmap :
        (U.map (Int.castRingHom ℚ)).map
            (algebraMap ℚ RationalFiniteAdele) =
          U.map (algebraMap ℤ RationalFiniteAdele) := by
      ext i j
      rfl
    rw [hUmap] at hmap
    exact hmap
  have hmid : P * Ua⁻¹ * P'⁻¹ = Q⁻¹ := by
    calc
      P * Ua⁻¹ * P'⁻¹ =
          Q⁻¹ * (Q * P) * Ua⁻¹ * P'⁻¹ := by
        simp [mul_assoc]
      _ = Q⁻¹ * (P' * Ua) * Ua⁻¹ * P'⁻¹ := by rw [hrel]
      _ = Q⁻¹ := by simp [mul_assoc]
  have hfactor : A * Ua⁻¹ * A'⁻¹ = g.1⁻¹ * Q⁻¹ * g'.1 := by
    calc
      A * Ua⁻¹ * A'⁻¹ =
          g.1⁻¹ * (P * Ua⁻¹ * P'⁻¹) * g'.1 := by
        simp [A, A', P, P', concreteAttachedBasisComparisonGL, mul_assoc]
      _ = g.1⁻¹ * Q⁻¹ * g'.1 := by rw [hmid]
  change g.1⁻¹ * Q⁻¹ * g'.1 ∈
    matrixUnitsOverSubring integralFiniteAdeleSubring
  rw [← hfactor]
  exact (matrixUnitsOverSubring integralFiniteAdeleSubring).mul_mem
    ((matrixUnitsOverSubring integralFiniteAdeleSubring).mul_mem
      (L.concreteAttachedBasisComparisonGL_mem_matrixUnitsOverSubring g)
      ((matrixUnitsOverSubring integralFiniteAdeleSubring).inv_mem
        (integralMatrixFiniteAdeleGL_mem_matrixUnitsOverSubring U hU)))
    ((matrixUnitsOverSubring integralFiniteAdeleSubring).inv_mem
      (L.concreteAttachedBasisComparisonGL_mem_matrixUnitsOverSubring g'))

/-- Equal attached global isometry classes recover the raw concrete
left-right double-coset relation. -/
theorem concreteAttached_globalIsometryClass_eq_implies_related
    (L : PositiveDefiniteIntegralLattice n)
    (g g' : L.ConcreteFiniteAdelicOrthogonalGroup)
    (hclass :
      (L.concreteAttachedIntegralLattice g).globalIsometryClass =
        (L.concreteAttachedIntegralLattice g').globalIsometryClass) :
    IsLeftRightDoubleCosetRelated
      L.rationalOrthogonalDiagonalSubgroup
      L.finiteLocalLatticeStabilizerSubgroup g g' := by
  have hiso := isGlobalIsometry_of_globalIsometryClass_eq hclass
  obtain ⟨q, U, hU, _hUform, hbasis⟩ :=
    L.exists_rationalOrthogonal_of_attached_globalIsometry g g' hiso
  let gamma : L.rationalOrthogonalDiagonalSubgroup :=
    ⟨L.rationalOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩
  let hval := g⁻¹ * (L.rationalOrthogonalDiagonalHom q)⁻¹ * g'
  have hhval : hval ∈ L.finiteLocalLatticeStabilizerSubgroup := by
    exact L.concreteAttachedResidual_mem_finiteLocalLatticeStabilizerSubgroup
      g g' q U hU hbasis
  let h : L.finiteLocalLatticeStabilizerSubgroup := ⟨hval, hhval⟩
  refine ⟨gamma, h, ?_⟩
  simp [gamma, h, hval, mul_assoc]

/-- The attached-lattice map injects the concrete rational double quotient
into the finite genus. -/
theorem concreteDoubleCosetToGenus_injective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Injective L.concreteDoubleCosetToGenus :=
  L.concreteDoubleCosetToGenus_injective_of_related
    L.concreteAttached_globalIsometryClass_eq_implies_related

/-- Every class in the genus is represented by a concrete finite-adelic
double coset. -/
theorem concreteDoubleCosetToGenus_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective L.concreteDoubleCosetToGenus := by
  intro C
  rcases C.property with ⟨M, hsame, hC⟩
  obtain ⟨P, hP⟩ := L.exists_rationalComparison_of_isSameGenus M hsame
  obtain ⟨U, hU⟩ :=
    L.exists_heightOneLocalIntegralMatrixUnits_of_isSameGenus M hsame
  let g := L.concreteFiniteAdelicRepresentativeOfRationalComparison M P hP U hU
  refine ⟨Quot.mk (leftRightDoubleCosetSetoid
    L.rationalOrthogonalDiagonalSubgroup
    L.finiteLocalLatticeStabilizerSubgroup) g, ?_⟩
  rw [L.concreteDoubleCosetToGenus_mk]
  apply Subtype.ext
  change (L.concreteAttachedIntegralLattice g).globalIsometryClass = C.1
  rw [hC]
  exact globalIsometryClass_eq_of_isGlobalIsometry
    (L.concreteAttachedIntegralLattice_representativeOfRationalComparison_isGlobalIsometry
      M P hP U hU)

/-- The concrete Schulze--Pillot parametrization of the genus by rational
finite-adelic double cosets. -/
noncomputable def concreteAdelicGenusParametrization
    (L : PositiveDefiniteIntegralLattice n) :
    L.genus ≃ L.ConcreteRationalDoubleCosetSet :=
  (Equiv.ofBijective L.concreteDoubleCosetToGenus
    ⟨L.concreteDoubleCosetToGenus_injective,
      L.concreteDoubleCosetToGenus_surjective⟩).symm

/-- The concrete rational double quotient is finite, by injection into the
already finite genus of `L`. -/
noncomputable instance concreteRationalDoubleCosetSetFintype
    (L : PositiveDefiniteIntegralLattice n) : Fintype L.ConcreteRationalDoubleCosetSet :=
  Fintype.ofInjective L.concreteDoubleCosetToGenus
    L.concreteDoubleCosetToGenus_injective

/-- Rational multiplication by an arithmetic stabilizer element, restricted
to the attached rational lattice. -/
noncomputable def concreteRationalArithmeticStabilizerLinearEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g) :
    L.concreteAttachedRationalLatticeSubmodule g ≃ₗ[ℤ]
      L.concreteAttachedRationalLatticeSubmodule g := by
  let S := L.concreteAttachedRationalLatticeSubmodule g
  let h : L.finiteLocalLatticeStabilizerSubgroup := Classical.choose q.2
  have hq : L.rationalOrthogonalDiagonalHom q.1 = g * h * g⁻¹ :=
    Classical.choose_spec q.2
  have hmul : L.rationalOrthogonalDiagonalHom q.1 * g = g * h := by
    rw [hq]
    simp [mul_assoc]
  have hS : q.1.1.1.mulVec '' (S : Set (Fin n → ℚ)) =
      (S : Set (Fin n → ℚ)) := by
    calc
      q.1.1.1.mulVec '' (S : Set (Fin n → ℚ)) =
          (L.concreteAttachedRationalLatticeSubmodule
            (L.rationalOrthogonalDiagonalHom q.1 * g) : Set (Fin n → ℚ)) :=
        L.rational_mulVec_image_concreteAttachedRationalLatticeSubmodule q.1 g
      _ = (L.concreteAttachedRationalLatticeSubmodule (g * h) :
          Set (Fin n → ℚ)) := by rw [hmul]
      _ = (S : Set (Fin n → ℚ)) := by
        rw [L.concreteAttachedRationalLatticeSubmodule_mul_finiteLocalStabilizer]
  let f : S →ₗ[ℤ] S :=
    { toFun := fun x => ⟨q.1.1.1.mulVec x, by
          change q.1.1.1.mulVec (x : Fin n → ℚ) ∈ (S : Set (Fin n → ℚ))
          rw [← hS]
          exact ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change q.1.1.1.mulVec (a • (x : Fin n → ℚ)) =
          a • q.1.1.1.mulVec (x : Fin n → ℚ)
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
        change (∑ k, q.1.1.1 i k * ((a : ℚ) * x.1 k)) =
          (a : ℚ) * ∑ k, q.1.1.1 i k * x.1 k
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact Matrix.mulVec_injective_of_isUnit q.1.1.isUnit hval
  · intro y
    have hy : (y : Fin n → ℚ) ∈
        q.1.1.1.mulVec '' (S : Set (Fin n → ℚ)) := by
      rw [hS]
      exact y.property
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

@[simp]
theorem concreteRationalArithmeticStabilizerLinearEquiv_apply_val
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g)
    (x : L.concreteAttachedRationalLatticeSubmodule g) :
    ((L.concreteRationalArithmeticStabilizerLinearEquiv g q x :
        L.concreteAttachedRationalLatticeSubmodule g) : Fin n → ℚ) =
      q.1.1.1.mulVec (x : Fin n → ℚ) := by
  change q.1.1.1.mulVec (x : Fin n → ℚ) = _
  rfl

/-- The integral matrix of a rational arithmetic stabilizer element in the
chosen basis of the attached lattice. -/
noncomputable def concreteRationalArithmeticStabilizerActionMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g) :
    Matrix (Fin n) (Fin n) ℤ :=
  let b := L.concreteAttachedRationalLatticeBasis g
  b.toMatrix (b.map (L.concreteRationalArithmeticStabilizerLinearEquiv g q))

theorem concreteRationalArithmeticStabilizerActionMatrix_isUnit
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g) :
    IsUnit (L.concreteRationalArithmeticStabilizerActionMatrix g q) := by
  let b := L.concreteAttachedRationalLatticeBasis g
  let bq := b.map (L.concreteRationalArithmeticStabilizerLinearEquiv g q)
  let T := b.toMatrix bq
  letI : Invertible T := b.invertibleToMatrix bq
  exact isUnit_of_invertible T

theorem concreteRationalArithmeticStabilizer_basis_mul_actionMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g) :
    L.concreteAttachedRationalLatticeBasisMatrixRat g *
        (L.concreteRationalArithmeticStabilizerActionMatrix g q).map
          (Int.castRingHom ℚ) =
      q.1.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g := by
  let S := L.concreteAttachedRationalLatticeSubmodule g
  let b := L.concreteAttachedRationalLatticeBasis g
  let e := L.concreteRationalArithmeticStabilizerLinearEquiv g q
  let bq : Module.Basis (Fin n) ℤ S := b.map e
  let T : Matrix (Fin n) (Fin n) ℤ := b.toMatrix bq
  let Tq := T.map (Int.castRingHom ℚ)
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  have hbqval (j : Fin n) :
      ((bq j : S) : Fin n → ℚ) = q.1.1.1.mulVec (b j : Fin n → ℚ) := by
    exact L.concreteRationalArithmeticStabilizerLinearEquiv_apply_val g q (b j)
  have hbqcol (j : Fin n) :
      ((bq j : S) : Fin n → ℚ) = (q.1.1.1 * B).col j := by
    rw [hbqval, ← L.concreteAttachedRationalLatticeBasisMatrixRat_col g j]
    ext i
    change (∑ k, q.1.1.1 i k * B k j) = ∑ k, q.1.1.1 i k * B k j
    rfl
  change B * Tq = q.1.1.1 * B
  ext i j
  have hsum : (∑ k, T k j • (b k : S)) = bq j := by
    simpa [T, Module.Basis.toMatrix_apply] using b.sum_repr (bq j)
  calc
    (B * Tq) i j = ∑ k, B i k * (T k j : ℚ) := by
      rw [Matrix.mul_apply]
      rfl
    _ = ∑ k, (T k j : ℚ) * ((b k : S) : Fin n → ℚ) i := by
      apply Finset.sum_congr rfl
      intro k _hk
      have hcol := L.concreteAttachedRationalLatticeBasisMatrixRat_col g k
      rw [← congrFun hcol i]
      exact mul_comm _ _
    _ = ((∑ k, T k j • (b k : S) : S) : Fin n → ℚ) i := by
      let ev : S →ₗ[ℤ] ℚ :=
        { toFun := fun x => (x : Fin n → ℚ) i
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro a x
            change ((a : ℚ) * x.1 i) = (a : ℚ) * x.1 i
            rfl }
      change (∑ k, (T k j : ℚ) * ((b k : S) : Fin n → ℚ) i) =
        ev (∑ k, T k j • (b k : S))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [map_smul]
      rfl
    _ = ((bq j : S) : Fin n → ℚ) i := by
      exact congrFun (congrArg Subtype.val hsum) i
    _ = (q.1.1.1 * B) i j := by
      exact congrFun (hbqcol j) i

/-- The determinant of the integral attached-basis action is the determinant
of the corresponding rational arithmetic stabilizer matrix. -/
theorem concreteRationalArithmeticStabilizerActionMatrix_det_cast
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g) :
    ((L.concreteRationalArithmeticStabilizerActionMatrix g q).det : ℚ) =
      q.1.1.1.det := by
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let T := L.concreteRationalArithmeticStabilizerActionMatrix g q
  have hbasis :=
    L.concreteRationalArithmeticStabilizer_basis_mul_actionMatrix g q
  have hdet := congrArg Matrix.det hbasis
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hmapdet :
      ((L.concreteRationalArithmeticStabilizerActionMatrix g q).map
        (Int.castRingHom ℚ)).det =
        (L.concreteRationalArithmeticStabilizerActionMatrix g q).det := by
    exact (RingHom.map_det (Int.castRingHom ℚ) _).symm
  rw [hmapdet] at hdet
  have hBdet : B.det ≠ 0 :=
    L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g
  apply mul_left_cancel₀ hBdet
  calc
    B.det * (T.det : ℚ) = q.1.1.1.det * B.det := hdet
    _ = B.det * q.1.1.1.det := by ring

theorem concreteRationalArithmeticStabilizerActionMatrix_form
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g) :
    let T := L.concreteRationalArithmeticStabilizerActionMatrix g q
    T.transpose * (L.concreteAttachedIntegralLattice g).pairingMatrix * T =
      (L.concreteAttachedIntegralLattice g).pairingMatrix := by
  dsimp only
  let T := L.concreteRationalArithmeticStabilizerActionMatrix g q
  let Tq := T.map (Int.castRingHom ℚ)
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let F := L.rationalFormMatrix
  have hchange : B * Tq = q.1.1.1 * B := by
    exact L.concreteRationalArithmeticStabilizer_basis_mul_actionMatrix g q
  have hq : q.1.1.1ᵀ * F * q.1.1.1 = F := q.1.property
  have hBg :
      (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) = Bᵀ * F * B := by
    simpa [concreteAttachedIntegralLattice, B, F, rationalFormMatrix] using
      L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g
  have hformQ :
      Tqᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) * Tq =
        (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) := by
    calc
      Tqᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) * Tq =
          Tqᵀ * (Bᵀ * F * B) * Tq := by
        rw [hBg]
      _ = (B * Tq)ᵀ * F * (B * Tq) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = (q.1.1.1 * B)ᵀ * F * (q.1.1.1 * B) := by rw [hchange]
      _ = Bᵀ * (q.1.1.1ᵀ * F * q.1.1.1) * B := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = Bᵀ * F * B := by rw [hq]
      _ = (L.concreteAttachedIntegralLattice g).pairingMatrix.map
          (Int.castRingHom ℚ) := by
        exact (L.concreteAttachedRationalLatticeFormMatrix_cast_eq_conj g).symm
  apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  change (Tᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix * T).map
      (Int.castRingHom ℚ) =
    (L.concreteAttachedIntegralLattice g).pairingMatrix.map (Int.castRingHom ℚ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  exact hformQ

/-- The chosen-basis action of the rational arithmetic stabilizer on the
attached integral lattice. -/
noncomputable def concreteRationalArithmeticStabilizerToIsometryGroup
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteRationalArithmeticStabilizerSubgroup g →
      (L.concreteAttachedIntegralLattice g).IsometryGroup :=
  fun q => ⟨L.concreteRationalArithmeticStabilizerActionMatrix g q,
    L.concreteRationalArithmeticStabilizerActionMatrix_isUnit g q,
    L.concreteRationalArithmeticStabilizerActionMatrix_form g q⟩

theorem concreteRationalArithmeticStabilizerToIsometryGroup_injective
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Function.Injective
      (L.concreteRationalArithmeticStabilizerToIsometryGroup g) := by
  intro q r hqr
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let Tq := (L.concreteRationalArithmeticStabilizerActionMatrix g q).map
    (Int.castRingHom ℚ)
  let Tr := (L.concreteRationalArithmeticStabilizerActionMatrix g r).map
    (Int.castRingHom ℚ)
  have hT : Tq = Tr := by
    exact congrArg (fun U : Matrix (Fin n) (Fin n) ℤ =>
      U.map (Int.castRingHom ℚ)) (congrArg Subtype.val hqr)
  have hqB : B * Tq = q.1.1.1 * B :=
    L.concreteRationalArithmeticStabilizer_basis_mul_actionMatrix g q
  have hrB : B * Tr = r.1.1.1 * B :=
    L.concreteRationalArithmeticStabilizer_basis_mul_actionMatrix g r
  have hQB : q.1.1.1 * B = r.1.1.1 * B := by
    rw [← hqB, ← hrB, hT]
  have hBdet : B.det ≠ 0 :=
    L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g
  have hBdetUnit : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hmat : q.1.1.1 = r.1.1.1 := by
    calc
      q.1.1.1 = (q.1.1.1 * B) * B⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBdetUnit, Matrix.mul_one]
      _ = (r.1.1.1 * B) * B⁻¹ := by rw [hQB]
      _ = r.1.1.1 := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBdetUnit, Matrix.mul_one]
  apply Subtype.ext
  apply Subtype.ext
  exact Units.ext hmat

theorem concreteRationalArithmeticStabilizerToIsometryGroup_surjective
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Function.Surjective
      (L.concreteRationalArithmeticStabilizerToIsometryGroup g) := by
  intro V
  let U := V.1
  have hU : IsUnit U := V.2.1
  have hUform :
      U.transpose * (L.concreteAttachedIntegralLattice g).pairingMatrix * U =
        (L.concreteAttachedIntegralLattice g).pairingMatrix := V.2.2
  obtain ⟨q, hbasis⟩ :=
    L.exists_rationalOrthogonal_of_attached_isometryMatrix g g U hU hUform
  let residual := g⁻¹ * (L.rationalOrthogonalDiagonalHom q)⁻¹ * g
  have hresidual : residual ∈ L.finiteLocalLatticeStabilizerSubgroup :=
    L.concreteAttachedResidual_mem_finiteLocalLatticeStabilizerSubgroup
      g g q U hU hbasis
  have hqmem : L.rationalOrthogonalDiagonalHom q ∈
      conjugateSubgroupCore L.finiteLocalLatticeStabilizerSubgroup g := by
    refine ⟨⟨residual⁻¹,
      L.finiteLocalLatticeStabilizerSubgroup.inv_mem hresidual⟩, ?_⟩
    simp [residual, mul_assoc]
  let qa : L.concreteRationalArithmeticStabilizerSubgroup g := ⟨q, hqmem⟩
  refine ⟨qa, ?_⟩
  apply Subtype.ext
  apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  let T := L.concreteRationalArithmeticStabilizerActionMatrix g qa
  let Tq := T.map (Int.castRingHom ℚ)
  let Uq := U.map (Int.castRingHom ℚ)
  have hBdet : B.det ≠ 0 :=
    L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g
  have hBdetUnit : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hTbasis : B * Tq = q.1.1 * B :=
    L.concreteRationalArithmeticStabilizer_basis_mul_actionMatrix g qa
  have hBTU : B * Tq = B * Uq := by rw [hTbasis, hbasis]
  have hTU : Tq = Uq := by
    calc
      Tq = B⁻¹ * (B * Tq) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hBdetUnit,
          Matrix.one_mul]
      _ = B⁻¹ * (B * Uq) := by rw [hBTU]
      _ = Uq := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hBdetUnit,
          Matrix.one_mul]
  simpa [Tq, Uq, T] using hTU

/-- The rational arithmetic stabilizer is equivalent to the isometry group of
the attached integral lattice. -/
noncomputable def concreteRationalArithmeticStabilizerIsometryEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteRationalArithmeticStabilizerSubgroup g ≃
      (L.concreteAttachedIntegralLattice g).IsometryGroup :=
  Equiv.ofBijective
    (L.concreteRationalArithmeticStabilizerToIsometryGroup g)
    ⟨L.concreteRationalArithmeticStabilizerToIsometryGroup_injective g,
      L.concreteRationalArithmeticStabilizerToIsometryGroup_surjective g⟩

/-- The ambient arithmetic intersection is equivalent to the isometry group
of the attached integral lattice. -/
noncomputable def concreteArithmeticStabilizerIsometryEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    L.concreteArithmeticStabilizerSubgroup g ≃
      (L.concreteAttachedIntegralLattice g).IsometryGroup :=
  (L.concreteRationalArithmeticStabilizerEquiv g).symm.trans
    (L.concreteRationalArithmeticStabilizerIsometryEquiv g)

/-- The ambient arithmetic stabilizer has the attached isometry-group
cardinality. -/
theorem concreteArithmeticStabilizer_cardinality
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    Nat.card (L.concreteArithmeticStabilizerSubgroup g) =
      Fintype.card (L.concreteAttachedIntegralLattice g).IsometryGroup := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (L.concreteArithmeticStabilizerIsometryEquiv g)

/-- The attached lattice and the chosen representative of its genus class have
isometry groups of the same cardinality. -/
theorem concreteAttachedIntegralLattice_card_eq_genusRepresentative
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteRationalDoubleCosetSet) :
    Fintype.card
        (L.concreteAttachedIntegralLattice (Quot.out C)).IsometryGroup =
      Fintype.card
        (genusClassRepresentative L
          (L.concreteAdelicGenusParametrization.symm C)).IsometryGroup := by
  apply isometryGroup_card_eq_of_isGlobalIsometry
  apply isGlobalIsometry_of_globalIsometryClass_eq
  rw [← genusClassRepresentative_globalIsometryClass]
  rfl

/-- The concrete arithmetic stabilizer cardinality, indexed by the chosen
concrete adelic genus parametrization. -/
theorem concreteChosenArithmeticStabilizer_cardinality
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteRationalDoubleCosetSet) :
    Nat.card
        ((L.rationalOrthogonalDiagonalSubgroup ⊓
          conjugateSubgroupCore L.finiteLocalLatticeStabilizerSubgroup
            (Quot.out C)) :
          Subgroup L.ConcreteFiniteAdelicOrthogonalGroup) =
      Fintype.card
        (genusClassRepresentative L
          (L.concreteAdelicGenusParametrization.symm C)).IsometryGroup := by
  calc
    Nat.card
        ((L.rationalOrthogonalDiagonalSubgroup ⊓
          conjugateSubgroupCore L.finiteLocalLatticeStabilizerSubgroup
            (Quot.out C)) :
          Subgroup L.ConcreteFiniteAdelicOrthogonalGroup) =
        Fintype.card
          (L.concreteAttachedIntegralLattice (Quot.out C)).IsometryGroup :=
      L.concreteArithmeticStabilizer_cardinality (Quot.out C)
    _ = Fintype.card
        (genusClassRepresentative L
          (L.concreteAdelicGenusParametrization.symm C)).IsometryGroup :=
      L.concreteAttachedIntegralLattice_card_eq_genusRepresentative C


/-! ## Finite-adelic orthogonal presentation -/

/-- The finite-adelic orthogonal group together with the two subgroups that
occur in Schulze--Pillot's genus parametrization:

* `rationalOrthogonal`: the diagonal image of `O(V)(Q)`;
* `finiteLocalLatticeStabilizer`: the finite local stabilizer
  `H_f = prod_p O(V_p; L_p)`.

The quotient and measure fields remain abstract.  The concrete ambient
carrier, diagonal rational subgroup, and finite local lattice stabilizer are
defined above; a future constructor should connect those definitions to this
downstream presentation. -/
structure FiniteAdelicOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) where
  carrier : Type u
  [instGroup : Group carrier]
  rationalOrthogonal : Subgroup carrier
  finiteLocalLatticeStabilizer : Subgroup carrier
  /-- The finite adelic quotient volume after the rational and local
  stabilizer quotient has been formed, before separating the real and finite
  local stabilizer volumes. -/
  finiteAdelicQuotientVolume : ℝ
  /-- The quotient-volume contribution of the right `H_f`-orbit over one raw
  finite-adelic representative.  In the eventual Haar-measure implementation
  this is the volume of the piece `{O(V)(ℚ) g h | h ∈ H_f}` inside
  `O(V)(ℚ) \ O(V)(A_f)`, normalized by `vol(H_f)=1`. -/
  doubleCosetPieceQuotientVolume : carrier → ℝ
  /-- The Haar volume of `H_f` in the quotient-measure normalization used for
  the finite double-coset pieces.  The intended Schulze--Pillot normalization
  sets this value to `1`; keeping it as a separate field lets the one-piece
  Weil source retain the factor `μ(H_f)` before normalization. -/
  finiteLocalLatticeStabilizerQuotientHaarVolume : ℝ
  /-- The Schulze--Pillot normalization for the compact-open stabilizer volume.
  This is presentation data rather than a separate theorem about an arbitrary
  Haar normalization. -/
  finiteLocalLatticeStabilizerQuotientHaarVolume_eq_one :
    finiteLocalLatticeStabilizerQuotientHaarVolume = 1
  /-- Schulze--Pillot's adelic genus parametrization for this finite-adelic
  presentation: ordinary genus classes of `L` are parametrized by
  `O(V)(Q) \ O(V)(A_f) / H_f`. -/
  adelicGenusParametrization :
    Equiv L.genus
      (leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer)
  /-- Chosen-representative stabilizer cardinality for the adelic mass sum.
  This is the only stabilizer-cardinality comparison needed by the final
  finite double-coset reindexing.  A concrete finite-adelic implementation may
  prove this field directly, or derive it from a broader stabilizer
  equivalence for arbitrary attached lattice representatives. -/
  chosenArithmeticStabilizer_cardinality :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      Nat.card
          ((rationalOrthogonal ⊓
            conjugateSubgroupCore finiteLocalLatticeStabilizer (Quot.out C)) :
              Subgroup carrier) =
        Fintype.card
          (genusClassRepresentative L
            (adelicGenusParametrization.symm C)).IsometryGroup
  /-- Finite additivity of the quotient volume over the double-coset pieces.
  A concrete finite-adelic presentation should supply this from the quotient
  Haar measure and the fiber decomposition
  `Gamma \ G ≃ Sigma C, X_C`.  It is a field of the presentation data, so each
  concrete presentation must prove it from its measure-theoretic
  construction. -/
  finiteAdelicQuotientVolume_eq_doubleCosetPieceQuotientVolumeSum :
    ∀ inst : Fintype
        (leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer),
      finiteAdelicQuotientVolume =
        @Finset.sum
          (leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer)
          ℝ _ (@Finset.univ
            (leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer) inst)
          (fun C => doubleCosetPieceQuotientVolume (Quot.out C))
  /-- The measurable structure on a selected quotient-side double-coset piece.
  A concrete finite-adelic presentation should take this from the Weil
  quotient measure on `Gamma \ G` restricted to the fiber over `Gamma \ G / H`.
  Keeping it as presentation data narrows the remaining source theorem to the
  actual periodization identity. -/
  doubleCosetPieceMeasurableSpace :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      MeasurableSpace
        (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)
  /-- The quotient measure on a selected double-coset piece. -/
  doubleCosetPieceQuotientMeasure :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      @Measure
        (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)
        (doubleCosetPieceMeasurableSpace C)
  /-- Nonnegativity of the real volume assigned to each selected quotient
  piece. -/
  doubleCosetPieceQuotientVolume_nonneg :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      0 ≤ doubleCosetPieceQuotientVolume (Quot.out C)
  /-- The total mass of the selected quotient-piece measure is the
  presentation's real quotient-piece volume, stated in `ℝ≥0∞`. -/
  doubleCosetPieceQuotientMeasure_univ_eq_ofReal :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      doubleCosetPieceQuotientMeasure C Set.univ =
        ENNReal.ofReal (doubleCosetPieceQuotientVolume (Quot.out C))
  /-- The measurable structure on the compact-open stabilizer factor `H_f`
  used by the selected-piece quotient map.  A concrete finite-adelic
  presentation should take this from the subspace measurable structure on the
  compact open subgroup. -/
  finiteLocalLatticeStabilizerMeasurableSpace :
    MeasurableSpace finiteLocalLatticeStabilizer
  /-- The Haar slice measure on `H_f` used before quotienting by the finite
  right stabilizer.  Its total mass is recorded below as the compact-open Haar
  volume in the chosen Schulze--Pillot normalization. -/
  finiteLocalLatticeStabilizerHaarMeasure :
    @Measure finiteLocalLatticeStabilizer
      finiteLocalLatticeStabilizerMeasurableSpace
  /-- Measurability of the selected right-`H_f` orbit map
  `h ↦ Γ * Quot.out C * h` into the quotient-side piece. -/
  rightOrbitToDoubleCosetPiece_measurable :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      @Measurable finiteLocalLatticeStabilizer
        (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)
        finiteLocalLatticeStabilizerMeasurableSpace
        (doubleCosetPieceMeasurableSpace C)
        (rightOrbitToLeftRightDoubleCosetPiece rationalOrthogonal
          finiteLocalLatticeStabilizer C)
  /-- The translated `H_f`-slice periodization function used before taking the
  quotient integral.  A concrete finite-adelic presentation should instantiate
  this as the periodized indicator of the orbit-map preimage inside the
  compact-open slice. -/
  doubleCosetPieceTranslatedSlicePeriodize :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      Set finiteLocalLatticeStabilizer →
        leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C →
          ℝ≥0∞
  /-- Representative-slice periodization rewrite on translated orbit-map
  preimages.

  The chosen-representative slice count is the correct quotient-side
  simplification on saturated sets of the form `orbit_g ⁻¹' B`.  For arbitrary
  measurable `A ⊆ H_f`, the standard Weil periodization count instead sees the
  whole finite stabilizer orbit.  Keeping only the orbit-preimage field avoids
  imposing that stronger, generally false arbitrary-`A` representative-count
  statement on concrete presentations. -/
  doubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice_orbitPreimage :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      ∀ ⦃B :
          Set (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)⦄,
        @MeasurableSet
          (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)
          (doubleCosetPieceMeasurableSpace C) B →
        doubleCosetPieceTranslatedSlicePeriodize C
            ((rightOrbitToLeftRightDoubleCosetPiece rationalOrthogonal
              finiteLocalLatticeStabilizer C) ⁻¹' B) =ᵐ[
          doubleCosetPieceQuotientMeasure C]
          doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore
            rationalOrthogonal finiteLocalLatticeStabilizer C
            ((rightOrbitToLeftRightDoubleCosetPiece rationalOrthogonal
              finiteLocalLatticeStabilizer C) ⁻¹' B)
  /-- Weil quotient-integration formula on translated orbit-map preimages. -/
  doubleCosetPieceTranslatedSlicePeriodize_lintegral_eq_orbitPreimage :
    ∀ C : leftRightDoubleCosetSet rationalOrthogonal finiteLocalLatticeStabilizer,
      ∀ ⦃B :
          Set (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)⦄,
        @MeasurableSet
          (leftRightDoubleCosetPiece rationalOrthogonal finiteLocalLatticeStabilizer C)
          (doubleCosetPieceMeasurableSpace C) B →
        ∫⁻ X,
          doubleCosetPieceTranslatedSlicePeriodize C
              ((rightOrbitToLeftRightDoubleCosetPiece rationalOrthogonal
                finiteLocalLatticeStabilizer C) ⁻¹' B) X
            ∂doubleCosetPieceQuotientMeasure C =
          finiteLocalLatticeStabilizerHaarMeasure
            ((rightOrbitToLeftRightDoubleCosetPiece rationalOrthogonal
              finiteLocalLatticeStabilizer C) ⁻¹' B)
  /-- The selected Haar slice on `H_f` has total mass equal to the
  compact-open stabilizer volume field. -/
  finiteLocalLatticeStabilizerHaarMeasure_univ_eq :
    finiteLocalLatticeStabilizerHaarMeasure Set.univ =
      ENNReal.ofReal finiteLocalLatticeStabilizerQuotientHaarVolume
  /-- The inverse finite Haar volume of the local lattice stabilizer `H_f`. -/
  finiteLocalStabilizerInverseHaarVolume : ℝ
  /-- The finite adelic quotient-volume computation in the normalization used
  for the mass formula: the quotient volume is the archimedean factor times
  the inverse finite Haar volume of `H_f`.  Below this is restated using the
  reciprocal real orthogonal volume. -/
  finiteAdelicQuotientVolume_eq_archimedeanFactor_mul_finiteLocalStabilizerVolume :
    finiteAdelicQuotientVolume =
      archimedeanMassFactor n * finiteLocalStabilizerInverseHaarVolume
  /-- The inverse Haar volume of the local lattice stabilizer at one finite prime. -/
  localStabilizerInverseHaarVolumeAtPrime : {p : ℕ // Nat.Prime p} → ℝ
  /-- Bad-prime local Haar normalization, pointwise.  The final product route
  mainly uses the finite bad-prime prefix field below, while this pointwise
  field keeps compatibility statements for arbitrary finite prime sets
  for concrete presentations. -/
  localStabilizerInverseHaarVolumeAtBadPrime_eq_massLocalInverseFactor :
    ∀ p : {p : ℕ // Nat.Prime p}, p ∈ massBadPrimeSet L →
      localStabilizerInverseHaarVolumeAtPrime p =
        massLocalInverseFactorAtPrime L p
  /-- The finite bad-prime local Haar prefix agrees with the product-facing
  bad-prime inverse factor.  This is the local normalization actually needed
  by the canonical bad-prime final assembly route. -/
  finiteLocalStabilizerInverseHaarVolumeProduct_badPrime_eq_massBadPrimeInverseProduct :
    (massBadPrimeSet L).prod
        (fun p => localStabilizerInverseHaarVolumeAtPrime p) =
      massBadPrimeInverseProduct L
  /-- Good-prime unramified local Haar normalization, pointwise away from the
  finite bad-prime set. -/
  localStabilizerInverseHaarVolumeAtGoodPrime_eq_massLocalInverseFactor :
    ∀ p : {p : ℕ // Nat.Prime p}, p ∉ massBadPrimeSet L →
      localStabilizerInverseHaarVolumeAtPrime p =
        massLocalInverseFactorAtPrime L p
  /-- Restricted-product volume normalization for the finite stabilizer `H_f`:
  the cutoff products of inverse local Haar volumes converge to the chosen
  inverse Haar volume of the full finite stabilizer. -/
  finiteLocalStabilizerInverseHaarVolumeProductTendsTo_volume :
    Filter.Tendsto
      (fun N : ℕ =>
        (rationalPrimesUpTo N).prod
          (fun p => localStabilizerInverseHaarVolumeAtPrime p))
      Filter.atTop (nhds finiteLocalStabilizerInverseHaarVolume)

attribute [instance] FiniteAdelicOrthogonalGroup.instGroup

/-- The concrete finite-adelic orthogonal presentation, parameterized only by
the separate local Haar product data. -/
noncomputable def concreteFiniteAdelicOrthogonalPresentation
    (L : PositiveDefiniteIntegralLattice n)
    (finiteLocalStabilizerInverseHaarVolume : ℝ)
    (finiteAdelicQuotientVolume_eq_archimedeanFactor_mul :
      L.concreteFiniteAdelicQuotientVolume
          L.concreteFiniteTransversalFundamentalDomain =
        archimedeanMassFactor n *
          finiteLocalStabilizerInverseHaarVolume)
    (localStabilizerInverseHaarVolumeAtPrime :
      {p : ℕ // Nat.Prime p} → ℝ)
    (localStabilizerInverseHaarVolumeAtBadPrime_eq_massLocalInverseFactor :
      ∀ p : {p : ℕ // Nat.Prime p}, p ∈ massBadPrimeSet L →
        localStabilizerInverseHaarVolumeAtPrime p =
          massLocalInverseFactorAtPrime L p)
    (finiteLocalStabilizerInverseHaarVolumeProduct_badPrime_eq_massBadPrimeInverseProduct :
      (massBadPrimeSet L).prod
          (fun p => localStabilizerInverseHaarVolumeAtPrime p) =
        massBadPrimeInverseProduct L)
    (localStabilizerInverseHaarVolumeAtGoodPrime_eq_massLocalInverseFactor :
      ∀ p : {p : ℕ // Nat.Prime p}, p ∉ massBadPrimeSet L →
        localStabilizerInverseHaarVolumeAtPrime p =
          massLocalInverseFactorAtPrime L p)
    (finiteLocalStabilizerInverseHaarVolumeProductTendsTo_volume :
      Filter.Tendsto
        (fun N : ℕ =>
          (rationalPrimesUpTo N).prod
            (fun p => localStabilizerInverseHaarVolumeAtPrime p))
        Filter.atTop (nhds finiteLocalStabilizerInverseHaarVolume)) :
    FiniteAdelicOrthogonalGroup L where
  carrier := L.ConcreteFiniteAdelicOrthogonalGroup
  rationalOrthogonal := L.rationalOrthogonalDiagonalSubgroup
  finiteLocalLatticeStabilizer := L.finiteLocalLatticeStabilizerSubgroup
  finiteAdelicQuotientVolume :=
    L.concreteFiniteAdelicQuotientVolume
      L.concreteFiniteTransversalFundamentalDomain
  doubleCosetPieceQuotientVolume :=
    L.concreteDoubleCosetPieceQuotientVolume
      L.concreteFiniteTransversalFundamentalDomain
  finiteLocalLatticeStabilizerQuotientHaarVolume := 1
  finiteLocalLatticeStabilizerQuotientHaarVolume_eq_one := rfl
  adelicGenusParametrization := L.concreteAdelicGenusParametrization
  chosenArithmeticStabilizer_cardinality :=
    L.concreteChosenArithmeticStabilizer_cardinality
  finiteAdelicQuotientVolume_eq_doubleCosetPieceQuotientVolumeSum := by
    intro inst
    exact L.concreteFiniteAdelicQuotientVolume_eq_doubleCosetPieceQuotientVolumeSum
      L.concreteFiniteTransversalFundamentalDomain
      (L.concreteFiniteTransversalFundamentalDomain_measure_ne_top inst) inst
  doubleCosetPieceMeasurableSpace := fun _ => inferInstance
  doubleCosetPieceQuotientMeasure :=
    L.concreteRationalDoubleCosetPieceQuotientMeasure
      L.concreteFiniteTransversalFundamentalDomain
  doubleCosetPieceQuotientVolume_nonneg := by
    intro C
    exact L.concreteDoubleCosetPieceQuotientVolume_nonneg
      L.concreteFiniteTransversalFundamentalDomain (Quot.out C)
  doubleCosetPieceQuotientMeasure_univ_eq_ofReal := by
    intro C
    exact L.concreteDoubleCosetPieceQuotientMeasure_univ_eq_ofReal
      L.concreteFiniteTransversalFundamentalDomain
      (L.concreteFiniteTransversalFundamentalDomain_measure_ne_top inferInstance) C
  finiteLocalLatticeStabilizerMeasurableSpace := inferInstance
  finiteLocalLatticeStabilizerHaarMeasure :=
    L.concreteFiniteLocalLatticeStabilizerHaarMeasure
  rightOrbitToDoubleCosetPiece_measurable :=
    L.concreteRationalRightOrbitToDoubleCosetPiece_measurable
  doubleCosetPieceTranslatedSlicePeriodize :=
    L.concreteDoubleCosetPieceTranslatedSlicePeriodize
  doubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice_orbitPreimage := by
    intro C B _hB
    exact L.concreteDoubleCosetPieceTranslatedSlicePeriodize_ae_eq_representativeSlice_orbitPreimage
      L.concreteFiniteTransversalFundamentalDomain C B
  doubleCosetPieceTranslatedSlicePeriodize_lintegral_eq_orbitPreimage := by
    intro C B hB
    exact L.concreteDoubleCosetPieceTranslatedSlicePeriodize_lintegral_eq_orbitPreimage
      inferInstance C hB
  finiteLocalLatticeStabilizerHaarMeasure_univ_eq := by
    simpa only [ENNReal.ofReal_one] using
      L.concreteFiniteLocalLatticeStabilizerHaarMeasure_univ
  finiteLocalStabilizerInverseHaarVolume :=
    finiteLocalStabilizerInverseHaarVolume
  finiteAdelicQuotientVolume_eq_archimedeanFactor_mul_finiteLocalStabilizerVolume :=
    finiteAdelicQuotientVolume_eq_archimedeanFactor_mul
  localStabilizerInverseHaarVolumeAtPrime :=
    localStabilizerInverseHaarVolumeAtPrime
  localStabilizerInverseHaarVolumeAtBadPrime_eq_massLocalInverseFactor :=
    localStabilizerInverseHaarVolumeAtBadPrime_eq_massLocalInverseFactor
  finiteLocalStabilizerInverseHaarVolumeProduct_badPrime_eq_massBadPrimeInverseProduct :=
    finiteLocalStabilizerInverseHaarVolumeProduct_badPrime_eq_massBadPrimeInverseProduct
  localStabilizerInverseHaarVolumeAtGoodPrime_eq_massLocalInverseFactor :=
    localStabilizerInverseHaarVolumeAtGoodPrime_eq_massLocalInverseFactor
  finiteLocalStabilizerInverseHaarVolumeProductTendsTo_volume :=
    finiteLocalStabilizerInverseHaarVolumeProductTendsTo_volume

namespace FiniteAdelicOrthogonalGroup

/-- The double-coset set
`O(V)(Q) \ O(V)(A_f) / H_f` attached to a finite-adelic orthogonal group
presentation. -/
def doubleCosetSet {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) : Type u :=
  leftRightDoubleCosetSet Gf.rationalOrthogonal
    Gf.finiteLocalLatticeStabilizer

/-- The left quotient `O(V)(Q) \ O(V)(A_f)` attached to the finite-adelic
presentation. -/
def rationalLeftCosetSet {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) : Type u :=
  leftCosetSet Gf.rationalOrthogonal

/-- The canonical projection
`O(V)(Q) \ O(V)(A_f) → O(V)(Q) \ O(V)(A_f) / H_f`. -/
def rationalLeftCosetToDoubleCoset {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) :
    Gf.rationalLeftCosetSet → Gf.doubleCosetSet :=
  leftCosetToLeftRightDoubleCoset Gf.rationalOrthogonal
    Gf.finiteLocalLatticeStabilizer

/-- The quotient-side piece of `O(V)(Q) \ O(V)(A_f)` lying over one adelic
double coset.  The quotient-volume additivity source should eventually become
finite additivity over these fibers. -/
def doubleCosetQuotientPiece {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (C : Gf.doubleCosetSet) : Type u :=
  leftRightDoubleCosetPiece Gf.rationalOrthogonal
    Gf.finiteLocalLatticeStabilizer C

/-- The finite-adelic specialization of the fiber decomposition
`O(V)(Q) \ O(V)(A_f) ≃ Σ C, X_C`.

This partition lets the finite quotient-volume additivity be derived
from measure additivity over the named double-coset quotient pieces. -/
def rationalLeftCosetSigmaDoubleCosetQuotientPieceEquiv {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) :
    Gf.rationalLeftCosetSet ≃
      Σ C : Gf.doubleCosetSet, Gf.doubleCosetQuotientPiece C :=
  leftCosetSigmaLeftRightDoubleCosetPieceEquiv Gf.rationalOrthogonal
    Gf.finiteLocalLatticeStabilizer

/-- The finite-adelic double-coset fibers cover the rational left quotient.

This is the set-theoretic cover underlying finite additivity of the quotient
measure over the selected pieces `X_C`. -/
theorem doubleCosetPieceSet_iUnion {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) :
    (⋃ C : Gf.doubleCosetSet,
        leftRightDoubleCosetPieceSet Gf.rationalOrthogonal
          Gf.finiteLocalLatticeStabilizer C) = Set.univ := by
  exact
    leftRightDoubleCosetPieceSet_iUnion Gf.rationalOrthogonal
      Gf.finiteLocalLatticeStabilizer

/-- Distinct finite-adelic double-coset fibers are disjoint in the rational
left quotient. -/
theorem doubleCosetPieceSet_disjoint {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) {C D : Gf.doubleCosetSet}
    (hCD : C ≠ D) :
    Disjoint
      (leftRightDoubleCosetPieceSet Gf.rationalOrthogonal
        Gf.finiteLocalLatticeStabilizer C)
      (leftRightDoubleCosetPieceSet Gf.rationalOrthogonal
        Gf.finiteLocalLatticeStabilizer D) := by
  exact
    leftRightDoubleCosetPieceSet_disjoint Gf.rationalOrthogonal
      Gf.finiteLocalLatticeStabilizer hCD

/-- The value map from the selected finite-adelic quotient piece has range the
corresponding double-coset fiber in the rational left quotient. -/
theorem doubleCosetQuotientPiece_val_range {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (C : Gf.doubleCosetSet) :
    Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1) =
      leftRightDoubleCosetPieceSet Gf.rationalOrthogonal
        Gf.finiteLocalLatticeStabilizer C :=
  leftRightDoubleCosetPiece_val_range Gf.rationalOrthogonal
    Gf.finiteLocalLatticeStabilizer C

/-- Finite measure additivity over the selected finite-adelic quotient-piece
ranges.

This is the measure-theoretic part of the finite-additivity source after the
set-theoretic fiber decomposition has been made formal.  A concrete
finite-adelic quotient presentation still has to identify the ambient quotient
measure on these ranges with the selected piece volumes. -/
theorem doubleCosetQuotientPiece_range_measure_univ_eq_sum
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [Fintype Gf.doubleCosetSet]
    (mX : MeasurableSpace Gf.rationalLeftCosetSet)
    (μ : @Measure Gf.rationalLeftCosetSet mX)
    (hmeas : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.rationalLeftCosetSet mX
        (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1))) :
    μ Set.univ =
      ∑ C : Gf.doubleCosetSet,
        μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) := by
  letI : MeasurableSpace Gf.rationalLeftCosetSet := mX
  exact
    measure_univ_eq_sum_of_fintype_iUnion_disjoint μ
      (fun C : Gf.doubleCosetSet =>
        Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1))
      (by
        calc
          (⋃ C : Gf.doubleCosetSet,
              Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) =
              (⋃ C : Gf.doubleCosetSet,
                leftRightDoubleCosetPieceSet Gf.rationalOrthogonal
                  Gf.finiteLocalLatticeStabilizer C) := by
            apply Set.iUnion_congr
            intro C
            exact doubleCosetQuotientPiece_val_range Gf C
          _ = Set.univ := doubleCosetPieceSet_iUnion Gf)
      (by
        intro C D hCD
        change
          Disjoint
            (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1))
            (Set.range (fun X : Gf.doubleCosetQuotientPiece D => X.1))
        rw [doubleCosetQuotientPiece_val_range Gf C,
          doubleCosetQuotientPiece_val_range Gf D]
        exact
          doubleCosetPieceSet_disjoint Gf hCD)
      hmeas

/-- Real finite-additivity of quotient volumes from an ambient quotient
measure.

This is the bookkeeping step left after the set-theoretic double-coset fiber
decomposition and finite measure additivity: a concrete finite-adelic
presentation only has to identify the ambient quotient measure's total mass
and the masses of the selected double-coset ranges with the stored real
volume fields. -/
theorem finiteAdelicQuotientVolume_eq_doubleCosetPieceQuotientVolumeSum_of_ambientMeasure
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [Fintype Gf.doubleCosetSet]
    (mX : MeasurableSpace Gf.rationalLeftCosetSet)
    (μ : @Measure Gf.rationalLeftCosetSet mX)
    (hvol_nonneg : 0 ≤ Gf.finiteAdelicQuotientVolume)
    (hmeas : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.rationalLeftCosetSet mX
        (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)))
    (huniv :
      μ Set.univ = ENNReal.ofReal Gf.finiteAdelicQuotientVolume)
    (hpiece : ∀ C : Gf.doubleCosetSet,
      μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) =
        ENNReal.ofReal (Gf.doubleCosetPieceQuotientVolume (Quot.out C))) :
    Gf.finiteAdelicQuotientVolume =
      ∑ C : Gf.doubleCosetSet,
        Gf.doubleCosetPieceQuotientVolume (Quot.out C) := by
  have hadd :
      μ Set.univ =
        ∑ C : Gf.doubleCosetSet,
          μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) :=
    doubleCosetQuotientPiece_range_measure_univ_eq_sum Gf mX μ hmeas
  have hENN :
      ENNReal.ofReal Gf.finiteAdelicQuotientVolume =
        ∑ C : Gf.doubleCosetSet,
          ENNReal.ofReal (Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
    calc
      ENNReal.ofReal Gf.finiteAdelicQuotientVolume = μ Set.univ := huniv.symm
      _ =
          ∑ C : Gf.doubleCosetSet,
            μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) :=
        hadd
      _ =
          ∑ C : Gf.doubleCosetSet,
            ENNReal.ofReal
              (Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
        exact Finset.sum_congr rfl fun C _ => hpiece C
  have hsum_nonneg :
      0 ≤
        ∑ C : Gf.doubleCosetSet,
          Gf.doubleCosetPieceQuotientVolume (Quot.out C) := by
    exact Finset.sum_nonneg fun C _ =>
      Gf.doubleCosetPieceQuotientVolume_nonneg C
  have hsum_ofReal :
      ENNReal.ofReal
          (∑ C : Gf.doubleCosetSet,
            Gf.doubleCosetPieceQuotientVolume (Quot.out C)) =
        ∑ C : Gf.doubleCosetSet,
          ENNReal.ofReal (Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
    exact
      ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ)
        (f := fun C : Gf.doubleCosetSet =>
          Gf.doubleCosetPieceQuotientVolume (Quot.out C))
        (by
          intro C _
          exact Gf.doubleCosetPieceQuotientVolume_nonneg C)
  have hENN' :
      ENNReal.ofReal Gf.finiteAdelicQuotientVolume =
        ENNReal.ofReal
          (∑ C : Gf.doubleCosetSet,
            Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
    simpa [hsum_ofReal] using hENN
  exact (ENNReal.ofReal_eq_ofReal_iff hvol_nonneg hsum_nonneg).1 hENN'

/-- Real finite-additivity from an ambient quotient measure using a real
total-mass normalization.

This variant avoids asking a concrete presentation to prove a separate
nonnegativity statement for the stored total quotient volume or an `ofReal`
identity for the ambient total mass.  It is enough to identify the real volume
with `(μ univ).toReal`; finite additivity and the selected range `ofReal`
identities force the ambient total measure to be the finite sum of the
selected real piece volumes. -/
theorem finiteAdelicQuotientVolume_eq_doubleCosetPieceQuotientVolumeSum_of_ambientMeasure_toReal
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [Fintype Gf.doubleCosetSet]
    (mX : MeasurableSpace Gf.rationalLeftCosetSet)
    (μ : @Measure Gf.rationalLeftCosetSet mX)
    (hmeas : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.rationalLeftCosetSet mX
        (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)))
    (huniv_toReal :
      (μ Set.univ).toReal = Gf.finiteAdelicQuotientVolume)
    (hpiece : ∀ C : Gf.doubleCosetSet,
      μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) =
        ENNReal.ofReal (Gf.doubleCosetPieceQuotientVolume (Quot.out C))) :
    Gf.finiteAdelicQuotientVolume =
      ∑ C : Gf.doubleCosetSet,
        Gf.doubleCosetPieceQuotientVolume (Quot.out C) := by
  have hadd :
      μ Set.univ =
        ∑ C : Gf.doubleCosetSet,
          μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) :=
    doubleCosetQuotientPiece_range_measure_univ_eq_sum Gf mX μ hmeas
  have hENN :
      μ Set.univ =
        ∑ C : Gf.doubleCosetSet,
          ENNReal.ofReal (Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
    calc
      μ Set.univ =
          ∑ C : Gf.doubleCosetSet,
            μ (Set.range (fun X : Gf.doubleCosetQuotientPiece C => X.1)) :=
        hadd
      _ =
          ∑ C : Gf.doubleCosetSet,
            ENNReal.ofReal
              (Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
        exact Finset.sum_congr rfl fun C _ => hpiece C
  have hsum_nonneg :
      0 ≤
        ∑ C : Gf.doubleCosetSet,
          Gf.doubleCosetPieceQuotientVolume (Quot.out C) := by
    exact Finset.sum_nonneg fun C _ =>
      Gf.doubleCosetPieceQuotientVolume_nonneg C
  have hsum_ofReal :
      ENNReal.ofReal
          (∑ C : Gf.doubleCosetSet,
            Gf.doubleCosetPieceQuotientVolume (Quot.out C)) =
        ∑ C : Gf.doubleCosetSet,
          ENNReal.ofReal (Gf.doubleCosetPieceQuotientVolume (Quot.out C)) := by
    exact
      ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ)
        (f := fun C : Gf.doubleCosetSet =>
          Gf.doubleCosetPieceQuotientVolume (Quot.out C))
        (by
          intro C _
          exact Gf.doubleCosetPieceQuotientVolume_nonneg C)
  have htoReal :
      (μ Set.univ).toReal =
        ∑ C : Gf.doubleCosetSet,
          Gf.doubleCosetPieceQuotientVolume (Quot.out C) := by
    calc
      (μ Set.univ).toReal =
          (∑ C : Gf.doubleCosetSet,
            ENNReal.ofReal
              (Gf.doubleCosetPieceQuotientVolume (Quot.out C))).toReal := by
        rw [hENN]
      _ =
          (ENNReal.ofReal
            (∑ C : Gf.doubleCosetSet,
              Gf.doubleCosetPieceQuotientVolume (Quot.out C))).toReal := by
        rw [← hsum_ofReal]
      _ =
          ∑ C : Gf.doubleCosetSet,
            Gf.doubleCosetPieceQuotientVolume (Quot.out C) := by
        exact ENNReal.toReal_ofReal hsum_nonneg
  exact huniv_toReal.symm.trans htoReal

/-- The finite type structure on the abstract double-coset set induced by an
adelic genus parametrization. -/
noncomputable def doubleCosetFintype {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (param : L.genus ≃ Gf.doubleCosetSet) :
    Fintype Gf.doubleCosetSet :=
  Fintype.ofEquiv L.genus param

/-- A chosen raw finite-adelic representative of an abstract double coset. -/
noncomputable def doubleCosetRepresentative {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) : Gf.carrier :=
  Quot.out C

/-- The finite-adelic fundamental-domain candidate
`⋃ C, g_C C_C` built from local transversals in `H_f`.

Here `g_C` is the chosen raw representative `Quot.out C`; the source theorem
for the concrete finite-adelic model should prove that suitable local
transversals make this set a Mathlib `IsFundamentalDomain`. -/
noncomputable def finiteTransversalFundamentalDomain {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer) :
    Set Gf.carrier :=
  finiteRightTransversalFundamentalDomain
    Gf.finiteLocalLatticeStabilizer Gf.doubleCosetRepresentative slice

/-- Membership in the finite-adelic fundamental-domain candidate built from
local transversals. -/
theorem mem_finiteTransversalFundamentalDomain {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer)
    (x : Gf.carrier) :
    x ∈ Gf.finiteTransversalFundamentalDomain slice ↔
      ∃ C : Gf.doubleCosetSet, ∃ h : Gf.finiteLocalLatticeStabilizer,
        h ∈ slice C ∧ x = Gf.doubleCosetRepresentative C * (h : Gf.carrier) := by
  simp [finiteTransversalFundamentalDomain,
    mem_finiteRightTransversalFundamentalDomain]

/-- The translated slices making up the finite-adelic finite-transversal
candidate are pairwise disjoint for distinct double-coset indices. -/
theorem finiteTransversalFundamentalDomain_translatedSlices_pairwiseDisjoint
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer) :
    Pairwise fun C D =>
      Disjoint
        (rightTranslateSliceSet Gf.finiteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C) (slice C))
        (rightTranslateSliceSet Gf.finiteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative D) (slice D)) := by
  exact
    rightTranslateSliceSet_pairwiseDisjoint_of_leftRightDoubleCosetRepresentatives
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer
      Gf.doubleCosetRepresentative (fun C => Quot.out_eq C) slice

/-- Measurability of the finite-adelic fundamental-domain candidate follows
from measurable local transversals and the standard measurable-subgroup
structure on `H_f`. -/
theorem finiteTransversalFundamentalDomain_measurableSet {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    {slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace (slice C)) :
    @MeasurableSet Gf.carrier mG
      (Gf.finiteTransversalFundamentalDomain slice) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  exact
    finiteRightTransversalFundamentalDomain_measurableSet_of_subgroup_comap
      Gf.finiteLocalLatticeStabilizer Gf.doubleCosetRepresentative slice
      hsub_comap hsub_meas hslice

/-- Haar-volume computation for the finite-adelic finite-transversal
fundamental-domain candidate.

This is the finite-adelic specialization of the generic finite-additivity
lemma for `⋃_C g_C C_C`: once the translated local slices are disjoint and the
compact-open Haar measure is the ambient restriction to `H_f`, the ambient
volume of the explicit candidate is the finite sum of local slice volumes. -/
theorem finiteTransversalFundamentalDomain_measure_eq_sum_subgroupHaar
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    {μG : Measure Gf.carrier} [Measure.IsMulLeftInvariant μG]
    {slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hsub_haar :
      @Measure.map Gf.finiteLocalLatticeStabilizer Gf.carrier
          Gf.finiteLocalLatticeStabilizerMeasurableSpace mG
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          Gf.finiteLocalLatticeStabilizerHaarMeasure =
        μG.restrict (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace (slice C))
    (hdisj : Pairwise fun C D =>
      Disjoint
        (rightTranslateSliceSet Gf.finiteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C) (slice C))
        (rightTranslateSliceSet Gf.finiteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative D) (slice D))) :
    μG (Gf.finiteTransversalFundamentalDomain slice) =
      ∑ C : Gf.doubleCosetSet,
        Gf.finiteLocalLatticeStabilizerHaarMeasure (slice C) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  exact
    finiteRightTransversalFundamentalDomain_measure_eq_sum_subgroupHaar
      Gf.finiteLocalLatticeStabilizer Gf.doubleCosetRepresentative slice
      hsub_comap hsub_meas hsub_haar hslice hdisj

/-- Exact left-translate uniqueness for the finite-adelic finite-transversal
candidate gives the concrete `IsFundamentalDomain` field required by the
standard quotient package. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_unique
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    {slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer}
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace (slice C))
    (hunique : ∀ x : Gf.carrier, ∃! gamma : Gf.rationalOrthogonal,
      (gamma : Gf.carrier) * x ∈ Gf.finiteTransversalFundamentalDomain slice) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain slice) μG := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  exact
    finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_unique
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer
      Gf.doubleCosetRepresentative slice hsub_comap hsub_meas hslice hunique

/-- Local-witness form of the finite-adelic finite-transversal
fundamental-domain constructor.

The future concrete presentation can prove this from finite double-coset
representatives and local transversals: every point admits a witness
`γ*x = g_C*h`, and any two such witnesses have the same rational factor
`γ`. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_cover_unique_witness
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    {slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer}
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace (slice C))
    (hcover : ∀ x : Gf.carrier,
      ∃ gamma : Gf.rationalOrthogonal, ∃ C : Gf.doubleCosetSet,
        ∃ h : Gf.finiteLocalLatticeStabilizer,
          h ∈ slice C ∧
            (gamma : Gf.carrier) * x =
              Gf.doubleCosetRepresentative C * (h : Gf.carrier))
    (hgamma_unique : ∀ (x : Gf.carrier)
        (gamma₁ gamma₂ : Gf.rationalOrthogonal)
        (C₁ C₂ : Gf.doubleCosetSet)
        (h₁ h₂ : Gf.finiteLocalLatticeStabilizer),
      h₁ ∈ slice C₁ →
      h₂ ∈ slice C₂ →
      (gamma₁ : Gf.carrier) * x =
        Gf.doubleCosetRepresentative C₁ * (h₁ : Gf.carrier) →
      (gamma₂ : Gf.carrier) * x =
        Gf.doubleCosetRepresentative C₂ * (h₂ : Gf.carrier) →
      gamma₁ = gamma₂) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain slice) μG := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  exact
    finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_cover_unique_witness
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer
      Gf.doubleCosetRepresentative slice hsub_comap hsub_meas hslice
      hcover hgamma_unique

/-- Finite-adelic coverage of the finite-transversal domain from local
right-transversal coverage in `H_f`.

The double-coset representatives already cover the ambient finite-adelic
carrier up to `O(V)(Q)` on the left and `H_f` on the right.  Therefore the
remaining coverage input is only the local statement that each right `H_f`
factor can be moved into the selected slice after adjusting the rational
left factor. -/
theorem finiteTransversalFundamentalDomain_cover_of_local_right_cover
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer)
    (hlocal : ∀ C : Gf.doubleCosetSet,
      ∀ h : Gf.finiteLocalLatticeStabilizer,
        ∃ gamma : Gf.rationalOrthogonal,
          ∃ c : Gf.finiteLocalLatticeStabilizer,
            c ∈ slice C ∧
              (gamma : Gf.carrier) *
                  (Gf.doubleCosetRepresentative C * (h : Gf.carrier)) =
                Gf.doubleCosetRepresentative C * (c : Gf.carrier)) :
    ∀ x : Gf.carrier,
      ∃ gamma : Gf.rationalOrthogonal, ∃ C : Gf.doubleCosetSet,
        ∃ c : Gf.finiteLocalLatticeStabilizer,
          c ∈ slice C ∧
            (gamma : Gf.carrier) * x =
              Gf.doubleCosetRepresentative C * (c : Gf.carrier) := by
  exact
    finiteRightTransversalFundamentalDomain_cover_of_local_right_cover
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer
      Gf.doubleCosetRepresentative
      (fun C => Quot.out_eq C)
      slice hlocal

lemma mk_doubleCosetRepresentative_eq {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) :
    Quot.mk (leftRightDoubleCosetSetoid Gf.rationalOrthogonal
      Gf.finiteLocalLatticeStabilizer) (Gf.doubleCosetRepresentative C) = C := by
  exact Quot.out_eq C

lemma rationalLeftCosetToDoubleCoset_eq_mk_doubleCosetRepresentative_iff
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (X : Gf.rationalLeftCosetSet) :
    Gf.rationalLeftCosetToDoubleCoset X = C ↔
      ∃ h : Gf.finiteLocalLatticeStabilizer,
        X = Quot.mk (leftCosetSetoid Gf.rationalOrthogonal)
          (Gf.doubleCosetRepresentative C * (h : Gf.carrier)) := by
  constructor
  · intro hX
    have hXrep :
        Gf.rationalLeftCosetToDoubleCoset X =
          Quot.mk (leftRightDoubleCosetSetoid Gf.rationalOrthogonal
            Gf.finiteLocalLatticeStabilizer) (Gf.doubleCosetRepresentative C) :=
      hX.trans (Gf.mk_doubleCosetRepresentative_eq C).symm
    exact (leftCosetToLeftRightDoubleCoset_eq_mk_iff
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer X
      (Gf.doubleCosetRepresentative C)).mp hXrep
  · rintro ⟨h, hX⟩
    have hXrep := (leftCosetToLeftRightDoubleCoset_eq_mk_iff
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer X
      (Gf.doubleCosetRepresentative C)).mpr ⟨h, hX⟩
    exact hXrep.trans (Gf.mk_doubleCosetRepresentative_eq C)

/-- The map from the local right stabilizer orbit `H_f` to the quotient-side
piece over a selected double coset.  Its fibers are the local right stabilizer
cosets; this is the group-theoretic core used before the quotient-measure
periodized-indicator computation. -/
def rightStabilizerOrbitToDoubleCosetQuotientPiece {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (C : Gf.doubleCosetSet)
    (h : Gf.finiteLocalLatticeStabilizer) : Gf.doubleCosetQuotientPiece C :=
  rightOrbitToLeftRightDoubleCosetPiece Gf.rationalOrthogonal
    Gf.finiteLocalLatticeStabilizer C h

theorem rightStabilizerOrbitToDoubleCosetQuotientPiece_surjective
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) :
    Function.Surjective (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) := by
  intro X
  rcases X with ⟨X, hX⟩
  rcases (Gf.rationalLeftCosetToDoubleCoset_eq_mk_doubleCosetRepresentative_iff C X).mp
      hX with ⟨h, hXeq⟩
  refine ⟨h, ?_⟩
  apply Subtype.ext
  exact hXeq.symm

/-- The finite-adelic right-orbit map is measurable from the standard
subtype/comap presentation.

This supplies the presentation field
`rightOrbitToDoubleCosetPiece_measurable` from the inherited subtype
measurable space on `H_f`, the map measurable space on `Γ \ G`, and the
subtype measurable spaces on the selected double-coset pieces. -/
theorem rightOrbitToDoubleCosetPiece_measurable_of_subtype_comapPieces
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    {mX : MeasurableSpace (leftCosetSet Gf.rationalOrthogonal)}
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hsub_mspace_default :
      Gf.finiteLocalLatticeStabilizerMeasurableSpace =
        (@Subtype.instMeasurableSpace Gf.carrier
          (fun x : Gf.carrier =>
            x ∈ (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier)) mG))
    (hleft_mspace :
      mX =
        MeasurableSpace.map (leftCosetMap Gf.rationalOrthogonal) mG)
    (hpiece_mspace_default : ∀ C : Gf.doubleCosetSet,
      Gf.doubleCosetPieceMeasurableSpace C =
        (@Subtype.instMeasurableSpace (leftCosetSet Gf.rationalOrthogonal)
          (fun X =>
            leftCosetToLeftRightDoubleCoset Gf.rationalOrthogonal
              Gf.finiteLocalLatticeStabilizer X = C)
          mX)) :
    ∀ C : Gf.doubleCosetSet,
      @Measurable Gf.finiteLocalLatticeStabilizer
        (leftRightDoubleCosetPiece Gf.rationalOrthogonal
          Gf.finiteLocalLatticeStabilizer C)
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.doubleCosetPieceMeasurableSpace C)
        (rightOrbitToLeftRightDoubleCosetPiece Gf.rationalOrthogonal
          Gf.finiteLocalLatticeStabilizer C) := by
  intro C
  exact
    rightOrbitToLeftRightDoubleCosetPiece_measurable_of_map_subtype_mspace
      (mH := Gf.finiteLocalLatticeStabilizerMeasurableSpace)
      (mX := mX)
      (mP := Gf.doubleCosetPieceMeasurableSpace C)
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C
      hsub_meas hsub_mspace_default hleft_mspace (hpiece_mspace_default C)

/-- The lattice representative of the genus class corresponding to an abstract
double coset under a chosen adelic genus parametrization. -/
noncomputable def doubleCosetLatticeRepresentative {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (param : L.genus ≃ Gf.doubleCosetSet)
    (C : Gf.doubleCosetSet) : PositiveDefiniteIntegralLattice n :=
  genusClassRepresentative L (param.symm C)

lemma doubleCosetLatticeRepresentative_isSameGenus {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (param : L.genus ≃ Gf.doubleCosetSet)
    (C : Gf.doubleCosetSet) :
    L.IsSameGenus (Gf.doubleCosetLatticeRepresentative param C) := by
  exact genusClassRepresentative_isSameGenus L (param.symm C)

/-- Conjugation of a subgroup by an element of the ambient group. -/
def conjugateSubgroup {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (H : Subgroup Gf.carrier) (g : Gf.carrier) : Subgroup Gf.carrier :=
  conjugateSubgroupCore H g

lemma mem_conjugateSubgroup_iff {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (H : Subgroup Gf.carrier) (g x : Gf.carrier) :
    x ∈ Gf.conjugateSubgroup H g ↔
      ∃ h : H, x = g * (h : Gf.carrier) * g⁻¹ := by
  rfl

/-- The arithmetic stabilizer attached to a finite-adelic representative `g`:
`O(V)(Q) ∩ g H_f g⁻¹`. -/
def arithmeticStabilizerSubgroup {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g : Gf.carrier) :
    Subgroup Gf.carrier :=
  Gf.rationalOrthogonal ⊓
    Gf.conjugateSubgroup Gf.finiteLocalLatticeStabilizer g

lemma mem_arithmeticStabilizerSubgroup_iff {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g x : Gf.carrier) :
    x ∈ Gf.arithmeticStabilizerSubgroup g ↔
      x ∈ Gf.rationalOrthogonal ∧
        ∃ h : Gf.finiteLocalLatticeStabilizer,
          x = g * (h : Gf.carrier) * g⁻¹ := by
  rfl

/-- The arithmetic stabilizer type attached to a representative `g`; this is
the abstract Lean version of `O(V)(Q) ∩ g H_f g⁻¹`. -/
def arithmeticStabilizer {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g : Gf.carrier) : Type u :=
  Gf.arithmeticStabilizerSubgroup g

/-- The stabilizer of the right `H_f`-orbit representative `g` inside the
local stabilizer `H_f`: `H_f ∩ g⁻¹ O(V)(Q) g`.  This is the subgroup that
appears directly in the quotient of the right `H_f`-piece before conjugating it
to the arithmetic stabilizer. -/
def localRightStabilizerSubgroup {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g : Gf.carrier) :
    Subgroup Gf.carrier :=
  Gf.finiteLocalLatticeStabilizer ⊓
    Gf.conjugateSubgroup Gf.rationalOrthogonal g⁻¹

lemma mem_localRightStabilizerSubgroup_iff {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g x : Gf.carrier) :
    x ∈ Gf.localRightStabilizerSubgroup g ↔
      x ∈ Gf.finiteLocalLatticeStabilizer ∧
        ∃ gamma : Gf.rationalOrthogonal,
          x = g⁻¹ * (gamma : Gf.carrier) * g := by
  constructor
  · intro hx
    rcases hx with ⟨hxH, gamma, hxgamma⟩
    refine ⟨hxH, gamma, ?_⟩
    simpa using hxgamma
  · rintro ⟨hxH, gamma, hxgamma⟩
    refine ⟨hxH, gamma, ?_⟩
    simpa using hxgamma

/-- The right-piece stabilizer type attached to `g`;
abstractly this is `H_f ∩ g⁻¹ O(V)(Q) g`. -/
def localRightStabilizer {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g : Gf.carrier) : Type u :=
  Gf.localRightStabilizerSubgroup g

/-- The right-piece stabilizer as a subgroup of the compact open subgroup
`H_f` itself.  This is the subgroup whose left-coset quotient maps to the
selected quotient-side piece. -/
def localRightStabilizerInFiniteLocalLatticeStabilizer {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (g : Gf.carrier) :
    Subgroup Gf.finiteLocalLatticeStabilizer where
  carrier := { h | (h : Gf.carrier) ∈ Gf.localRightStabilizerSubgroup g }
  one_mem' := by
    exact (Gf.localRightStabilizerSubgroup g).one_mem
  mul_mem' := by
    intro h₁ h₂ hh₁ hh₂
    exact (Gf.localRightStabilizerSubgroup g).mul_mem hh₁ hh₂
  inv_mem' := by
    intro h hh
    exact (Gf.localRightStabilizerSubgroup g).inv_mem hh

@[simp] lemma mem_localRightStabilizerInFiniteLocalLatticeStabilizer_iff
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) (h : Gf.finiteLocalLatticeStabilizer) :
    h ∈ Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g ↔
      (h : Gf.carrier) ∈ Gf.localRightStabilizerSubgroup g := by
  rfl

/-- The ordinary finite selected local stabilizer gives the `Fintype` instance
needed by finite-subgroup selector constructions for a fixed adelic point. -/
noncomputable def localRightStabilizerInFiniteLocalLatticeStabilizerFintype
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)] :
    Fintype (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :=
  Fintype.ofFinite
    (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- The ordinary finite selected local-stabilizer family supplies the
`Fintype` family needed by finite-subgroup selector constructions. -/
noncomputable def localRightStabilizerInFiniteLocalLatticeStabilizerFintypeFamily
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C))) :
    ∀ C : Gf.doubleCosetSet,
      Fintype
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)) := by
  intro C
  haveI : Finite
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) := hfinite C
  exact
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizerFintype
      (Gf.doubleCosetRepresentative C)

/-- Local right-factor normalization from a transversal for the selected local
right stabilizer.

For a fixed double-coset representative `g_C`, if every `h ∈ H_f` decomposes
as `s*c` with `s ∈ H_f ∩ g_C⁻¹Γg_C` and `c` in the selected local slice, then
the stabilizer conjugation supplies a rational element `γ` with
`γ*(g_C*h)=g_C*c`. -/
theorem local_right_cover_of_localRightStabilizer_transversal
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) (slice : Set Gf.finiteLocalLatticeStabilizer)
    (hcover : ∀ h : Gf.finiteLocalLatticeStabilizer,
      ∃ s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g,
        ∃ c : Gf.finiteLocalLatticeStabilizer,
          c ∈ slice ∧
            h = (s : Gf.finiteLocalLatticeStabilizer) * c) :
    ∀ h : Gf.finiteLocalLatticeStabilizer,
      ∃ gamma : Gf.rationalOrthogonal,
        ∃ c : Gf.finiteLocalLatticeStabilizer,
          c ∈ slice ∧
            (gamma : Gf.carrier) * (g * (h : Gf.carrier)) =
              g * (c : Gf.carrier) := by
  refine
    local_right_cover_of_stabilizer_transversal
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer g
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) slice
      ?_ hcover
  intro s
  have hs :
      (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
          Gf.finiteLocalLatticeStabilizer) : Gf.carrier) ∈
        Gf.localRightStabilizerSubgroup g := by
    exact s.2
  rcases
      (Gf.mem_localRightStabilizerSubgroup_iff g
        (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
          Gf.finiteLocalLatticeStabilizer) : Gf.carrier)).mp hs with
    ⟨_hsH, gamma, hs_eq⟩
  refine ⟨gamma, ?_⟩
  calc
    (gamma : Gf.carrier) * g =
        g * (g⁻¹ * (gamma : Gf.carrier) * g) := by
          simp [mul_assoc]
    _ = g *
        (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
          Gf.finiteLocalLatticeStabilizer) : Gf.carrier) := by
          rw [← hs_eq]

/-- Same-`γ` uniqueness from local slice uniqueness modulo the selected local
right stabilizer.

This is the finite-adelic form of the remaining local-transversal uniqueness
input: inside each double-coset piece, two slice representatives differing by
`H_f ∩ g_C⁻¹Γg_C` must be equal.  Lean then derives the same rational factor
for any two local witnesses of the same ambient point. -/
theorem finiteTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer)
    (hlocal_unique : ∀ (C : Gf.doubleCosetSet)
        (h₁ h₂ : Gf.finiteLocalLatticeStabilizer),
      h₁ ∈ slice C →
      h₂ ∈ slice C →
      (h₂ * h₁⁻¹ : Gf.finiteLocalLatticeStabilizer) ∈
        Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C) →
      h₂ = h₁) :
    ∀ (x : Gf.carrier) (gamma₁ gamma₂ : Gf.rationalOrthogonal)
        (C₁ C₂ : Gf.doubleCosetSet)
        (h₁ h₂ : Gf.finiteLocalLatticeStabilizer),
      h₁ ∈ slice C₁ →
      h₂ ∈ slice C₂ →
      (gamma₁ : Gf.carrier) * x =
        Gf.doubleCosetRepresentative C₁ * (h₁ : Gf.carrier) →
      (gamma₂ : Gf.carrier) * x =
        Gf.doubleCosetRepresentative C₂ * (h₂ : Gf.carrier) →
      gamma₁ = gamma₂ := by
  refine
    finiteRightTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer
      Gf.doubleCosetRepresentative (fun C => Quot.out_eq C) slice ?_
  intro C h₁ h₂ hh₁ hh₂ hstab
  apply hlocal_unique C h₁ h₂ hh₁ hh₂
  rw [Gf.mem_localRightStabilizerInFiniteLocalLatticeStabilizer_iff,
    Gf.mem_localRightStabilizerSubgroup_iff]
  rcases hstab with ⟨gamma, hgamma⟩
  exact ⟨(h₂ * h₁⁻¹).2, gamma, hgamma⟩

/-- A selected local stabilizer transversal supplies the finite-transversal
fundamental-domain field.

For every double-coset representative `g_C`, it is enough to give the usual
right-transversal data in `H_f`: every `h` decomposes as `s*c` with
`s ∈ H_f ∩ g_C⁻¹Γg_C` and `c ∈ C_C`, and two elements of `C_C` differing by
that stabilizer are equal.  The ambient double-coset coverage, local
right-factor normalization, same-`γ` uniqueness, measurability packaging, and
Mathlib `IsFundamentalDomain` constructor are then formal. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_local_stabilizer_transversals
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    {slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer}
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace (slice C))
    (hdecomp : ∀ C : Gf.doubleCosetSet,
      ∀ h : Gf.finiteLocalLatticeStabilizer,
        ∃ s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C),
          ∃ c : Gf.finiteLocalLatticeStabilizer,
            c ∈ slice C ∧
              h = (s : Gf.finiteLocalLatticeStabilizer) * c)
    (hlocal_unique : ∀ (C : Gf.doubleCosetSet)
        (h₁ h₂ : Gf.finiteLocalLatticeStabilizer),
      h₁ ∈ slice C →
      h₂ ∈ slice C →
      (h₂ * h₁⁻¹ : Gf.finiteLocalLatticeStabilizer) ∈
        Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C) →
      h₂ = h₁) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain slice) μG := by
  have hlocal : ∀ C : Gf.doubleCosetSet,
      ∀ h : Gf.finiteLocalLatticeStabilizer,
        ∃ gamma : Gf.rationalOrthogonal,
          ∃ c : Gf.finiteLocalLatticeStabilizer,
            c ∈ slice C ∧
              (gamma : Gf.carrier) *
                  (Gf.doubleCosetRepresentative C * (h : Gf.carrier)) =
                Gf.doubleCosetRepresentative C * (c : Gf.carrier) := by
    intro C
    exact
      Gf.local_right_cover_of_localRightStabilizer_transversal
        (Gf.doubleCosetRepresentative C) (slice C) (hdecomp C)
  have hcover :
      ∀ x : Gf.carrier,
        ∃ gamma : Gf.rationalOrthogonal, ∃ C : Gf.doubleCosetSet,
          ∃ c : Gf.finiteLocalLatticeStabilizer,
            c ∈ slice C ∧
              (gamma : Gf.carrier) * x =
                Gf.doubleCosetRepresentative C * (c : Gf.carrier) :=
    Gf.finiteTransversalFundamentalDomain_cover_of_local_right_cover slice hlocal
  have hgamma_unique :
      ∀ (x : Gf.carrier) (gamma₁ gamma₂ : Gf.rationalOrthogonal)
          (C₁ C₂ : Gf.doubleCosetSet)
          (h₁ h₂ : Gf.finiteLocalLatticeStabilizer),
        h₁ ∈ slice C₁ →
        h₂ ∈ slice C₂ →
        (gamma₁ : Gf.carrier) * x =
          Gf.doubleCosetRepresentative C₁ * (h₁ : Gf.carrier) →
        (gamma₂ : Gf.carrier) * x =
          Gf.doubleCosetRepresentative C₂ * (h₂ : Gf.carrier) →
        gamma₁ = gamma₂ :=
    Gf.finiteTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
      slice hlocal_unique
  exact
    Gf.finiteTransversalFundamentalDomain_isFundamentalDomain_of_cover_unique_witness
      hsub_comap hsub_meas hslice hcover hgamma_unique

/-- The canonical chosen slice for the local right stabilizer
`H_f ∩ g⁻¹Γg` acting on `H_f` by left multiplication. -/
noncomputable def localRightStabilizerTransversalSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) : Set Gf.finiteLocalLatticeStabilizer :=
  leftCosetRepresentativeSlice
    (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- The canonical local right-stabilizer slice is measurable when the local
quotient is countable and singleton sets in `H_f` are measurable. -/
theorem localRightStabilizerTransversalSlice_measurableSet_of_countable
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [@MeasurableSingletonClass Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Countable
      (leftCosetSet
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g))] :
    @MeasurableSet Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace
      (Gf.localRightStabilizerTransversalSlice g) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  exact
    leftCosetRepresentativeSlice_measurableSet_of_countable
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- Pointwise Haar measure of the canonical local right-stabilizer
representative slice under the standard normalized finite-subgroup
fundamental-domain hypotheses.

This specializes the abstract `Quot.out` left-coset representative-slice
volume computation to the local subgroup
`H_f ∩ g⁻¹Γg ⊆ H_f`.  A concrete finite-adelic presentation can use it to
discharge the pointwise slice-measure input once it has supplied the
measurable slice, left invariance of the Haar measure on `H_f`, and the
normalization `μ_H(H_f) = 1`. -/
theorem localRightStabilizerTransversalSlice_measure_eq_inv_natCard_of_normalized
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)]
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer)
    (hleft :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      Measure.IsMulLeftInvariant Gf.finiteLocalLatticeStabilizerHaarMeasure)
    (hmeas :
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.localRightStabilizerTransversalSlice g))
    (hμ_univ :
      Gf.finiteLocalLatticeStabilizerHaarMeasure Set.univ =
        ENNReal.ofReal 1) :
    Gf.finiteLocalLatticeStabilizerHaarMeasure
        (Gf.localRightStabilizerTransversalSlice g) =
      ENNReal.ofReal
        (1 /
          (Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
            ℝ)) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  letI : MeasurableMul Gf.finiteLocalLatticeStabilizer := hmul
  letI :
      Measure.IsMulLeftInvariant Gf.finiteLocalLatticeStabilizerHaarMeasure :=
    hleft
  letI : Fintype (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizerFintype g
  simpa [FiniteAdelicOrthogonalGroup.localRightStabilizerTransversalSlice] using
    leftCosetRepresentativeSlice_measure_eq_inv_natCard
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)
      (μ := Gf.finiteLocalLatticeStabilizerHaarMeasure)
      hmeas hμ_univ

/-- The concrete `embeddingReal` local slice for
`H_f ∩ g⁻¹Γg` acting on `H_f` by left multiplication.

This is the noncanonical standard-Borel selector route used for compact-open
local slices, avoiding the false local quotient-countability assumption. -/
noncomputable def localRightStabilizerEmbeddingRealSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    (g : Gf.carrier) : Set Gf.finiteLocalLatticeStabilizer :=
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  finiteSubgroupEmbeddingRealSlice
    (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- Measurability of the concrete `embeddingReal` local slice. -/
theorem localRightStabilizerEmbeddingRealSlice_measurableSet
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)]
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer) :
    @MeasurableSet Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace
      (Gf.localRightStabilizerEmbeddingRealSlice g) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  letI : MeasurableMul Gf.finiteLocalLatticeStabilizer := hmul
  letI : Fintype (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizerFintype g
  simpa [FiniteAdelicOrthogonalGroup.localRightStabilizerEmbeddingRealSlice] using
    finiteSubgroupEmbeddingRealSlice_measurableSet
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)
      (fun gamma => measurable_const_mul
        (gamma : Gf.finiteLocalLatticeStabilizer))

/-- The concrete `embeddingReal` local slice is a local left-coset
transversal. -/
theorem localRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)] :
    IsLeftCosetTransversal
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)
      (Gf.localRightStabilizerEmbeddingRealSlice g) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  letI : Fintype (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizerFintype g
  simpa [FiniteAdelicOrthogonalGroup.localRightStabilizerEmbeddingRealSlice] using
    finiteSubgroupEmbeddingRealSlice_isLeftCosetTransversal
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- Bundled local-slice fields for the concrete `embeddingReal` selector:
measurability in `H_f` and the local left-coset transversal property. -/
theorem localRightStabilizerEmbeddingRealSlice_measurableSet_and_isLeftCosetTransversal
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)]
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer) :
    @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.localRightStabilizerEmbeddingRealSlice g) ∧
      IsLeftCosetTransversal
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)
        (Gf.localRightStabilizerEmbeddingRealSlice g) :=
  ⟨Gf.localRightStabilizerEmbeddingRealSlice_measurableSet g hmul,
    Gf.localRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal g⟩

/-- Pointwise Haar measure of the concrete `embeddingReal` local slice under
normalized finite-subgroup hypotheses. -/
theorem localRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard_of_normalized
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)]
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer)
    (hleft :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      Measure.IsMulLeftInvariant Gf.finiteLocalLatticeStabilizerHaarMeasure)
    (hμ_univ :
      Gf.finiteLocalLatticeStabilizerHaarMeasure Set.univ =
        ENNReal.ofReal 1) :
    Gf.finiteLocalLatticeStabilizerHaarMeasure
        (Gf.localRightStabilizerEmbeddingRealSlice g) =
      ENNReal.ofReal
        (1 /
          (Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
            ℝ)) := by
  letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
    Gf.finiteLocalLatticeStabilizerMeasurableSpace
  letI : MeasurableMul Gf.finiteLocalLatticeStabilizer := hmul
  letI :
      Measure.IsMulLeftInvariant Gf.finiteLocalLatticeStabilizerHaarMeasure :=
    hleft
  letI : Fintype (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :=
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizerFintype g
  simpa [FiniteAdelicOrthogonalGroup.localRightStabilizerEmbeddingRealSlice] using
    finiteSubgroupEmbeddingRealSlice_measure_eq_inv_natCard
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)
      (μ := Gf.finiteLocalLatticeStabilizerHaarMeasure)
      hμ_univ

/-- Measurability of all concrete `embeddingReal` local slices over selected
double-coset representatives. -/
theorem localRightStabilizerEmbeddingRealSlice_measurableSet_representatives
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)))
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer) :
    ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.localRightStabilizerEmbeddingRealSlice
          (Gf.doubleCosetRepresentative C)) := by
  intro C
  haveI : Finite
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) := hfinite C
  exact
    Gf.localRightStabilizerEmbeddingRealSlice_measurableSet
      (Gf.doubleCosetRepresentative C) hmul

/-- Bundled measurability and transversal fields for all concrete
`embeddingReal` local slices over selected double-coset representatives. -/
theorem localRightStabilizerEmbeddingRealSlice_measurableSet_and_isLeftCosetTransversal_representatives
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)))
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer) :
    ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
          Gf.finiteLocalLatticeStabilizerMeasurableSpace
          (Gf.localRightStabilizerEmbeddingRealSlice
            (Gf.doubleCosetRepresentative C)) ∧
        IsLeftCosetTransversal
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C))
          (Gf.localRightStabilizerEmbeddingRealSlice
            (Gf.doubleCosetRepresentative C)) := by
  intro C
  haveI : Finite
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) := hfinite C
  exact
    Gf.localRightStabilizerEmbeddingRealSlice_measurableSet_and_isLeftCosetTransversal
      (Gf.doubleCosetRepresentative C) hmul

/-- Pointwise Haar measurements of all concrete `embeddingReal` local slices
over selected double-coset representatives. -/
theorem localRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard_representatives
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)))
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer)
    (hleft :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      Measure.IsMulLeftInvariant Gf.finiteLocalLatticeStabilizerHaarMeasure)
    (hμ_univ :
      Gf.finiteLocalLatticeStabilizerHaarMeasure Set.univ =
        ENNReal.ofReal 1) :
    ∀ C : Gf.doubleCosetSet,
      Gf.finiteLocalLatticeStabilizerHaarMeasure
          (Gf.localRightStabilizerEmbeddingRealSlice
            (Gf.doubleCosetRepresentative C)) =
        ENNReal.ofReal
          (1 /
            (Nat.card
              (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
                (Gf.doubleCosetRepresentative C)) : ℝ)) := by
  intro C
  haveI : Finite
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) := hfinite C
  exact
    Gf.localRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard_of_normalized
      (Gf.doubleCosetRepresentative C) hmul hleft hμ_univ

/-- The concrete `embeddingReal` local slices assemble into the standard
finite-transversal fundamental domain.

This is the compact-open replacement for the countability-based
`Quot.out` local-slice route: finite selected local stabilizers plus the
standard-Borel structure on `H_f` supply measurable local transversals. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_localRightStabilizerEmbeddingRealSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Fintype Gf.doubleCosetSet]
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)))
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain
        (fun C : Gf.doubleCosetSet =>
          Gf.localRightStabilizerEmbeddingRealSlice
            (Gf.doubleCosetRepresentative C))) μG := by
  let slice : Gf.doubleCosetSet → Set Gf.finiteLocalLatticeStabilizer :=
    fun C => Gf.localRightStabilizerEmbeddingRealSlice
      (Gf.doubleCosetRepresentative C)
  have hslice_transversal :=
    Gf.localRightStabilizerEmbeddingRealSlice_measurableSet_and_isLeftCosetTransversal_representatives
      hfinite hmul
  have hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace (slice C) := by
    intro C
    exact (hslice_transversal C).1
  have hdecomp : ∀ C : Gf.doubleCosetSet,
      ∀ h : Gf.finiteLocalLatticeStabilizer,
        ∃ s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C),
          ∃ c : Gf.finiteLocalLatticeStabilizer,
            c ∈ slice C ∧
              h = (s : Gf.finiteLocalLatticeStabilizer) * c := by
    intro C
    exact (hslice_transversal C).2.decomp
  have hlocal_unique : ∀ (C : Gf.doubleCosetSet)
        (h₁ h₂ : Gf.finiteLocalLatticeStabilizer),
      h₁ ∈ slice C →
      h₂ ∈ slice C →
      (h₂ * h₁⁻¹ : Gf.finiteLocalLatticeStabilizer) ∈
        Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C) →
      h₂ = h₁ := by
    intro C h₁ h₂ hh₁ hh₂ hmem
    exact (hslice_transversal C).2.unique h₁ h₂ hh₁ hh₂ hmem
  exact
    Gf.finiteTransversalFundamentalDomain_isFundamentalDomain_of_local_stabilizer_transversals
      hsub_comap hsub_meas hslice hdecomp hlocal_unique

/-- Ambient Haar volume of the finite-transversal domain built from the
concrete `embeddingReal` local slices.

This is the raw map/restrict finite-additivity route for the standard-Borel selector:
the only local-slice inputs are standard Borel `H_f`, finite selected local
stabilizers, and measurable multiplication on `H_f`. -/
theorem finiteTransversalFundamentalDomain_measure_eq_sum_localRightStabilizerEmbeddingRealSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Fintype Gf.doubleCosetSet]
    {μG : Measure Gf.carrier} [Measure.IsMulLeftInvariant μG]
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hsub_haar :
      @Measure.map Gf.finiteLocalLatticeStabilizer Gf.carrier
          Gf.finiteLocalLatticeStabilizerMeasurableSpace mG
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          Gf.finiteLocalLatticeStabilizerHaarMeasure =
        μG.restrict (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)))
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer) :
    μG
        (Gf.finiteTransversalFundamentalDomain
          (fun C : Gf.doubleCosetSet =>
            Gf.localRightStabilizerEmbeddingRealSlice
              (Gf.doubleCosetRepresentative C))) =
      ∑ C : Gf.doubleCosetSet,
        Gf.finiteLocalLatticeStabilizerHaarMeasure
          (Gf.localRightStabilizerEmbeddingRealSlice
            (Gf.doubleCosetRepresentative C)) := by
  have hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.localRightStabilizerEmbeddingRealSlice
          (Gf.doubleCosetRepresentative C)) :=
    Gf.localRightStabilizerEmbeddingRealSlice_measurableSet_representatives
      hfinite hmul
  exact
    Gf.finiteTransversalFundamentalDomain_measure_eq_sum_subgroupHaar
      hsub_comap hsub_meas hsub_haar hslice
      (Gf.finiteTransversalFundamentalDomain_translatedSlices_pairwiseDisjoint
        (fun C : Gf.doubleCosetSet =>
          Gf.localRightStabilizerEmbeddingRealSlice
            (Gf.doubleCosetRepresentative C)))

/-- Real-valued reciprocal-cardinality ambient-volume evaluation for the
finite-transversal domain built from the concrete `embeddingReal` local
slices. -/
theorem finiteTransversalFundamentalDomain_toReal_eq_sum_inv_localRightStabilizerEmbeddingRealSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [@StandardBorelSpace Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    [Fintype Gf.doubleCosetSet]
    {μG : Measure Gf.carrier} [Measure.IsMulLeftInvariant μG]
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hsub_haar :
      @Measure.map Gf.finiteLocalLatticeStabilizer Gf.carrier
          Gf.finiteLocalLatticeStabilizerMeasurableSpace mG
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          Gf.finiteLocalLatticeStabilizerHaarMeasure =
        μG.restrict (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hfinite : ∀ C : Gf.doubleCosetSet,
      Finite
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)))
    (hmul :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      MeasurableMul Gf.finiteLocalLatticeStabilizer)
    (hleft :
      letI : MeasurableSpace Gf.finiteLocalLatticeStabilizer :=
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
      Measure.IsMulLeftInvariant Gf.finiteLocalLatticeStabilizerHaarMeasure)
    (hμ_univ :
      Gf.finiteLocalLatticeStabilizerHaarMeasure Set.univ =
        ENNReal.ofReal 1) :
    (μG
        (Gf.finiteTransversalFundamentalDomain
          (fun C : Gf.doubleCosetSet =>
            Gf.localRightStabilizerEmbeddingRealSlice
              (Gf.doubleCosetRepresentative C)))).toReal =
      ∑ C : Gf.doubleCosetSet,
        1 /
          (Nat.card
            (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
              (Gf.doubleCosetRepresentative C)) : ℝ) := by
  let f : Gf.doubleCosetSet → ℝ := fun C =>
    1 /
      (Nat.card
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)) : ℝ)
  have hf_nonneg : ∀ C, 0 ≤ f C := by
    intro C
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hmeasure_sum :
      μG
          (Gf.finiteTransversalFundamentalDomain
            (fun C : Gf.doubleCosetSet =>
              Gf.localRightStabilizerEmbeddingRealSlice
                (Gf.doubleCosetRepresentative C))) =
        ∑ C : Gf.doubleCosetSet,
          Gf.finiteLocalLatticeStabilizerHaarMeasure
            (Gf.localRightStabilizerEmbeddingRealSlice
              (Gf.doubleCosetRepresentative C)) :=
    Gf.finiteTransversalFundamentalDomain_measure_eq_sum_localRightStabilizerEmbeddingRealSlice
      hsub_comap hsub_meas hsub_haar hfinite hmul
  have hslice_measure :
      ∀ C : Gf.doubleCosetSet,
        Gf.finiteLocalLatticeStabilizerHaarMeasure
            (Gf.localRightStabilizerEmbeddingRealSlice
              (Gf.doubleCosetRepresentative C)) =
          ENNReal.ofReal (f C) := by
    intro C
    simpa [f] using
      Gf.localRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard_representatives
        hfinite hmul hleft hμ_univ C
  have hsum :
      (∑ C : Gf.doubleCosetSet,
          Gf.finiteLocalLatticeStabilizerHaarMeasure
            (Gf.localRightStabilizerEmbeddingRealSlice
              (Gf.doubleCosetRepresentative C))) =
        ENNReal.ofReal (∑ C : Gf.doubleCosetSet, f C) := by
    calc
      (∑ C : Gf.doubleCosetSet,
          Gf.finiteLocalLatticeStabilizerHaarMeasure
            (Gf.localRightStabilizerEmbeddingRealSlice
              (Gf.doubleCosetRepresentative C))) =
          ∑ C : Gf.doubleCosetSet, ENNReal.ofReal (f C) := by
            exact Finset.sum_congr rfl fun C _ => hslice_measure C
      _ = ENNReal.ofReal (∑ C : Gf.doubleCosetSet, f C) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro C _
            exact hf_nonneg C
  rw [hmeasure_sum, hsum]
  exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun C _ => hf_nonneg C)

/-- Measurability of all canonical local right-stabilizer slices over selected
double-coset representatives follows from countability of the corresponding
local quotients and measurable singletons in `H_f`. -/
theorem localRightStabilizerTransversalSlice_measurableSet_of_countable_representatives
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [@MeasurableSingletonClass Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    (hcount : ∀ C : Gf.doubleCosetSet,
      Countable
        (leftCosetSet
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C)))) :
    ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.localRightStabilizerTransversalSlice
          (Gf.doubleCosetRepresentative C)) := by
  intro C
  haveI :
      Countable
        (leftCosetSet
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C))) :=
    hcount C
  exact
    Gf.localRightStabilizerTransversalSlice_measurableSet_of_countable
      (Gf.doubleCosetRepresentative C)

/-- The canonical local right-stabilizer slice covers `H_f` by left translates
of the selected local right stabilizer. -/
theorem localRightStabilizerTransversalSlice_decomp
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) :
    ∀ h : Gf.finiteLocalLatticeStabilizer,
      ∃ s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g,
        ∃ c : Gf.finiteLocalLatticeStabilizer,
          c ∈ Gf.localRightStabilizerTransversalSlice g ∧
            h = (s : Gf.finiteLocalLatticeStabilizer) * c := by
  exact
    leftCosetRepresentativeSlice_decomp
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- The canonical local right-stabilizer slice has unique representatives
modulo `H_f ∩ g⁻¹Γg`. -/
theorem localRightStabilizerTransversalSlice_unique
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) :
    ∀ h₁ h₂ : Gf.finiteLocalLatticeStabilizer,
      h₁ ∈ Gf.localRightStabilizerTransversalSlice g →
      h₂ ∈ Gf.localRightStabilizerTransversalSlice g →
      (h₂ * h₁⁻¹ : Gf.finiteLocalLatticeStabilizer) ∈
        Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g →
      h₂ = h₁ := by
  exact
    leftCosetRepresentativeSlice_unique
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)

/-- For the canonical choice of local right-stabilizer representatives, the
finite-transversal domain is a fundamental domain once those chosen slices are
measurable.

This removes the set-theoretic local-transversal source input: the remaining
extra hypothesis for this canonical slice is measurability in `H_f`. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_localRightStabilizerTransversalSlice_measurable
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hslice : ∀ C : Gf.doubleCosetSet,
      @MeasurableSet Gf.finiteLocalLatticeStabilizer
        Gf.finiteLocalLatticeStabilizerMeasurableSpace
        (Gf.localRightStabilizerTransversalSlice
          (Gf.doubleCosetRepresentative C))) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain
        (fun C : Gf.doubleCosetSet =>
          Gf.localRightStabilizerTransversalSlice
            (Gf.doubleCosetRepresentative C))) μG := by
  exact
    Gf.finiteTransversalFundamentalDomain_isFundamentalDomain_of_local_stabilizer_transversals
      hsub_comap hsub_meas hslice
      (fun C =>
        Gf.localRightStabilizerTransversalSlice_decomp
          (Gf.doubleCosetRepresentative C))
      (fun C =>
        Gf.localRightStabilizerTransversalSlice_unique
          (Gf.doubleCosetRepresentative C))

/-- The canonical finite-transversal domain is a fundamental domain when the
selected local right-stabilizer quotients are countable.

This combines the countability-based measurability of the canonical
`Quot.out` local stabilizer slices with the canonical local-transversal
fundamental-domain theorem, so no separate slice-measurability family is
needed. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_countable_localRightStabilizerQuotients
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    [@MeasurableSingletonClass Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace]
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hcount : ∀ C : Gf.doubleCosetSet,
      Countable
        (leftCosetSet
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C)))) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain
        (fun C : Gf.doubleCosetSet =>
          Gf.localRightStabilizerTransversalSlice
            (Gf.doubleCosetRepresentative C))) μG := by
  exact
    Gf.finiteTransversalFundamentalDomain_isFundamentalDomain_of_localRightStabilizerTransversalSlice_measurable
      hsub_comap hsub_meas
      (Gf.localRightStabilizerTransversalSlice_measurableSet_of_countable_representatives
        hcount)

/-- Natural subgroup-comap version of the canonical finite-transversal
fundamental-domain constructor.

For compact-open presentations that already identify `H_f` by the subgroup
comap measurable-space field, measurable singletons on `H_f` are inherited
from ambient measurable singletons.  Thus this theorem only asks for the
ambient measurability of `H_f` and countability of the selected local
stabilizer quotients. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_countable_localRightStabilizerQuotients_comap
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    [@MeasurableSingletonClass Gf.carrier mG]
    {μG : Measure Gf.carrier}
    (hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace)
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hcount : ∀ C : Gf.doubleCosetSet,
      Countable
        (leftCosetSet
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C)))) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain
        (fun C : Gf.doubleCosetSet =>
          Gf.localRightStabilizerTransversalSlice
            (Gf.doubleCosetRepresentative C))) μG := by
  letI : @MeasurableSingletonClass Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace :=
    @subgroup_measurableSingletonClass_of_comap
      Gf.carrier _ mG inferInstance Gf.finiteLocalLatticeStabilizer
      Gf.finiteLocalLatticeStabilizerMeasurableSpace hsub_comap
  exact
    Gf.finiteTransversalFundamentalDomain_isFundamentalDomain_of_countable_localRightStabilizerQuotients
      hsub_comap hsub_meas hcount

/-- Default subtype/comap version of the canonical finite-transversal
fundamental-domain constructor.

For the ordinary subtype measurable-space choice on `H_f`, the subgroup comap
field is formal.  Thus the remaining concrete inputs are measurability of
`H_f` in the ambient finite-adelic group and countability of the selected
local stabilizer quotients. -/
theorem finiteTransversalFundamentalDomain_isFundamentalDomain_of_countable_localRightStabilizerQuotients_subtypeComap
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    [mG : MeasurableSpace Gf.carrier] [MeasurableMul Gf.carrier]
    [Fintype Gf.doubleCosetSet]
    [@MeasurableSingletonClass Gf.carrier mG]
    {μG : Measure Gf.carrier}
    (hsub_meas :
      @MeasurableSet Gf.carrier mG
        (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier))
    (hsub_mspace_default :
      Gf.finiteLocalLatticeStabilizerMeasurableSpace =
        (@Subtype.instMeasurableSpace Gf.carrier
          (fun x : Gf.carrier =>
            x ∈ (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier)) mG))
    (hcount : ∀ C : Gf.doubleCosetSet,
      Countable
        (leftCosetSet
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C)))) :
    IsFundamentalDomain Gf.rationalOrthogonal
      (Gf.finiteTransversalFundamentalDomain
        (fun C : Gf.doubleCosetSet =>
          Gf.localRightStabilizerTransversalSlice
            (Gf.doubleCosetRepresentative C))) μG := by
  have hsub_comap :
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
        Gf.finiteLocalLatticeStabilizerMeasurableSpace := by
    calc
      MeasurableSpace.comap
          (fun h : Gf.finiteLocalLatticeStabilizer => (h : Gf.carrier))
          mG =
          (@Subtype.instMeasurableSpace Gf.carrier
            (fun x : Gf.carrier =>
              x ∈ (Gf.finiteLocalLatticeStabilizer : Set Gf.carrier)) mG) := rfl
      _ = Gf.finiteLocalLatticeStabilizerMeasurableSpace :=
        hsub_mspace_default.symm
  exact
    Gf.finiteTransversalFundamentalDomain_isFundamentalDomain_of_countable_localRightStabilizerQuotients_comap
      hsub_comap hsub_meas hcount

/-- The presentation-data version of the right-piece stabilizer is the same
subgroup of `H_f` as `localRightStabilizerInFiniteLocalLatticeStabilizer`.
This repackages the raw predicate used in the `FiniteAdelicOrthogonalGroup`
fields into the namespace-local subgroup API. -/
noncomputable def localRightStabilizerInFiniteLocalLatticeStabilizerEquivSliceSubtype
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) :
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g ≃
      { h : Gf.finiteLocalLatticeStabilizer //
        ∃ gamma : Gf.rationalOrthogonal,
          (h : Gf.carrier) = g⁻¹ * (gamma : Gf.carrier) * g } where
  toFun h := by
    refine ⟨h.1, ?_⟩
    exact (Gf.mem_localRightStabilizerSubgroup_iff g (h.1 : Gf.carrier)).mp h.2 |>.2
  invFun h := by
    refine ⟨h.1, ?_⟩
    exact (Gf.mem_localRightStabilizerSubgroup_iff g (h.1 : Gf.carrier)).mpr
      ⟨h.1.2, h.2⟩
  left_inv h := by
    apply Subtype.ext
    rfl
  right_inv h := by
    apply Subtype.ext
    rfl

/-- Viewing the right-piece stabilizer as a subgroup of `H_f` does not change
the underlying stabilizer type used in the denominator.  This is the
bookkeeping bridge between the quotient `S \ H_f` and the ambient subgroup
`H_f ∩ g⁻¹Γg`. -/
noncomputable def localRightStabilizerInFiniteLocalLatticeStabilizerEquiv
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) :
    Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g ≃
      Gf.localRightStabilizer g where
  toFun h := ⟨((h : Gf.finiteLocalLatticeStabilizer) : Gf.carrier), h.2⟩
  invFun h := by
    refine ⟨⟨h.1, ?_⟩, h.2⟩
    exact (Gf.mem_localRightStabilizerSubgroup_iff g h.1).mp h.2 |>.1
  left_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv h := by
    apply Subtype.ext
    rfl

/-- The stabilizer denominator is unchanged when the right-piece stabilizer is
regarded as a subgroup of the compact open subgroup `H_f`. -/
theorem localRightStabilizerInFiniteLocalLatticeStabilizer_nat_card_eq
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) :
    Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) =
      Nat.card (Gf.localRightStabilizer g) :=
  Nat.card_congr
    (Gf.localRightStabilizerInFiniteLocalLatticeStabilizerEquiv g)

/-- Once the local right stabilizer is known to be finite, its cardinality is
positive.  The nonemptiness is formal: the identity element lies in every
subgroup.  Thus future Weil quotient-measure inputs only need the standard
finite-stabilizer hypothesis, not a separate positivity source. -/
theorem localRightStabilizerInFiniteLocalLatticeStabilizer_nat_card_pos_of_finite
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier)
    [Finite (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g)] :
    0 < Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) := by
  haveI : Nonempty (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) := ⟨1⟩
  exact Nat.card_pos

/-- The canonical measurable structure on a selected double-coset piece
induced by the right-`H_f` orbit map.

This is the direct selected-piece analogue of the quotient-map-induced
measurable structure on `(H_f ∩ g⁻¹Γg) \ H_f`: if a concrete Weil quotient
presentation chooses this measurable structure, measurability of the orbit map
is automatic and need not be supplied separately. -/
def doubleCosetQuotientPieceOrbitMeasurableSpace {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer) :
    MeasurableSpace (Gf.doubleCosetQuotientPiece C) :=
  MeasurableSpace.map (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) mH

/-- The selected right-`H_f` orbit map is measurable for the canonical
orbit-induced measurable structure on the selected double-coset piece. -/
theorem rightStabilizerOrbitToDoubleCosetQuotientPiece_measurable_canonical
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer) :
    @Measurable Gf.finiteLocalLatticeStabilizer (Gf.doubleCosetQuotientPiece C)
      mH (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH)
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) := by
  rw [measurable_iff_comap_le]
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact ht

/-- The direct orbit-scaled measure on a selected double-coset piece.

It is the pushforward of Haar measure on `H_f` along the selected orbit map,
scaled by the finite right-stabilizer denominator.  A concrete Weil quotient
presentation can compare its restricted quotient-piece measure with this
canonical measure; the finite-stabilizer slice identities below then hold
without further hypotheses. -/
noncomputable def doubleCosetPieceOrbitScaledMeasure {L : PositiveDefiniteIntegralLattice n}
    (Gf : FiniteAdelicOrthogonalGroup.{u} L) (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer)
    (μH : @Measure Gf.finiteLocalLatticeStabilizer mH) :
    @Measure (Gf.doubleCosetQuotientPiece C)
      (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH) :=
  ((Nat.card
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) : ℝ≥0∞)⁻¹ •
    @Measure.map Gf.finiteLocalLatticeStabilizer
      (Gf.doubleCosetQuotientPiece C) mH
      (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH)
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) μH)

/-- Finite-slice identity for the canonical orbit-scaled measure on a selected
double-coset piece.

For every measurable subset `B` of the selected piece, multiplying its
canonical orbit-scaled measure by `|H_f ∩ g⁻¹Γg|` recovers the Haar measure of
the preimage in `H_f`.  Thus this part of the quotient-volume comparison is
formal once the selected quotient-piece measure is identified with the
canonical orbit-scaled measure. -/
theorem doubleCosetPieceOrbitScaledMeasure_slice_eq
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer)
    (μH : @Measure Gf.finiteLocalLatticeStabilizer mH)
    (hcard_pos :
      0 < Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)))
    {B : Set (Gf.doubleCosetQuotientPiece C)}
    (hB :
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH) B) :
    (Nat.card
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) : ℝ≥0∞) *
      (Gf.doubleCosetPieceOrbitScaledMeasure C mH μH) B =
        μH ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) := by
  letI := mH
  letI := Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH
  let c : ℝ≥0∞ :=
    (Nat.card
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    change
      (Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) : ℝ≥0∞) ≠ 0
    exact_mod_cast Nat.ne_of_gt hcard_pos
  have hctop : c ≠ ∞ := by
    simp [c]
  simpa [FiniteAdelicOrthogonalGroup.doubleCosetPieceOrbitScaledMeasure, c] using
    @const_mul_scaled_pushforward_measure_apply_eq_preimage
      Gf.finiteLocalLatticeStabilizer (Gf.doubleCosetQuotientPiece C)
      mH (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH) μH
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C)
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece_measurable_canonical C mH)
      c hc0 hctop B hB

/-- Total-piece specialization of the finite-slice identity for the canonical
orbit-scaled measure on a selected double-coset piece. -/
theorem doubleCosetPieceOrbitScaledMeasure_univ_slice_eq
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer)
    (μH : @Measure Gf.finiteLocalLatticeStabilizer mH)
    (hcard_pos :
      0 < Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C))) :
    (Nat.card
      (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)) : ℝ≥0∞) *
      (Gf.doubleCosetPieceOrbitScaledMeasure C mH μH) Set.univ =
        μH Set.univ := by
  simpa using
    Gf.doubleCosetPieceOrbitScaledMeasure_slice_eq C mH μH hcard_pos
      (B := Set.univ) MeasurableSet.univ

/-- Total mass of the canonical orbit-scaled measure on a selected
double-coset piece.

This is the canonical-measure version of the one-piece quotient-volume
calculation: after choosing the orbit-induced measurable structure and the
finite-stabilizer-scaled pushforward of Haar measure on `H_f`, the total mass
is the Haar mass of `H_f` divided by `|H_f ∩ g⁻¹Γg|`. -/
theorem doubleCosetPieceOrbitScaledMeasure_univ_eq_ofReal_div_nat
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer)
    (μH : @Measure Gf.finiteLocalLatticeStabilizer mH)
    (hcard_pos :
      0 < Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)))
    {M : ℝ} (hμH : μH Set.univ = ENNReal.ofReal M) :
    (Gf.doubleCosetPieceOrbitScaledMeasure C mH μH) Set.univ =
      ENNReal.ofReal
        (M / (Nat.card
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C)) : ℝ)) := by
  simpa [FiniteAdelicOrthogonalGroup.doubleCosetPieceOrbitScaledMeasure] using
    @scaled_pushforward_measure_univ_eq_ofReal_div_nat
      Gf.finiteLocalLatticeStabilizer (Gf.doubleCosetQuotientPiece C)
      mH (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH) μH
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C)
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece_measurable_canonical C mH)
      (Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)))
      hcard_pos M hμH

/-- Normalized total-mass formula for the canonical orbit-scaled measure:
when the Haar slice has mass `1`, the selected piece has mass
`1 / |H_f ∩ g⁻¹Γg|`. -/
theorem doubleCosetPieceOrbitScaledMeasure_univ_eq_ofReal_inv_nat
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (mH : MeasurableSpace Gf.finiteLocalLatticeStabilizer)
    (μH : @Measure Gf.finiteLocalLatticeStabilizer mH)
    (hcard_pos :
      0 < Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)))
    (hμH : μH Set.univ = ENNReal.ofReal 1) :
    (Gf.doubleCosetPieceOrbitScaledMeasure C mH μH) Set.univ =
      ENNReal.ofReal
        ((Nat.card
          (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
            (Gf.doubleCosetRepresentative C)) : ℝ)⁻¹) := by
  simpa [FiniteAdelicOrthogonalGroup.doubleCosetPieceOrbitScaledMeasure] using
    @scaled_pushforward_measure_univ_eq_ofReal_inv_nat
      Gf.finiteLocalLatticeStabilizer (Gf.doubleCosetQuotientPiece C)
      mH (Gf.doubleCosetQuotientPieceOrbitMeasurableSpace C mH) μH
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C)
      (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece_measurable_canonical C mH)
      (Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
        (Gf.doubleCosetRepresentative C)))
      hcard_pos hμH

/-- The finite periodized-indicator count behind the one-piece quotient-volume
calculation, before introducing measures.

For a point `g h₀` in the right `H_f`-orbit, rational elements `γ` with
`γ g h₀ ∈ gH_f` are in bijection with the local right stabilizer
`H_f ∩ g⁻¹Γg`, viewed as a subgroup of `H_f`.  The later measure argument
uses this to show that the periodized indicator of `gH_f` is constant with
value `|H_f ∩ g⁻¹Γg|` on the corresponding quotient piece. -/
noncomputable def rationalElementsSendingRightTranslateEquivLocalRightStabilizerInFiniteLocalLatticeStabilizer
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) (h₀ : Gf.finiteLocalLatticeStabilizer) :
    { gamma : Gf.rationalOrthogonal //
        ∃ h : Gf.finiteLocalLatticeStabilizer,
          (gamma : Gf.carrier) * g * (h₀ : Gf.carrier) =
            g * (h : Gf.carrier) } ≃
      Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g :=
  Equiv.ofBijective
    (fun gamma => by
      let h : Gf.finiteLocalLatticeStabilizer := Classical.choose gamma.2
      have hgamma :
          (gamma.1 : Gf.carrier) * g * (h₀ : Gf.carrier) =
            g * (h : Gf.carrier) :=
        Classical.choose_spec gamma.2
      let x : Gf.carrier := g⁻¹ * (gamma.1 : Gf.carrier) * g
      have hx_eq : x = (h : Gf.carrier) * (h₀ : Gf.carrier)⁻¹ := by
        calc
          x = g⁻¹ * ((gamma.1 : Gf.carrier) * g * (h₀ : Gf.carrier)) *
                (h₀ : Gf.carrier)⁻¹ := by
              simp [x, mul_assoc]
          _ = g⁻¹ * (g * (h : Gf.carrier)) * (h₀ : Gf.carrier)⁻¹ := by
              rw [hgamma]
          _ = (h : Gf.carrier) * (h₀ : Gf.carrier)⁻¹ := by
              simp
      have hxH : x ∈ Gf.finiteLocalLatticeStabilizer := by
        rw [hx_eq]
        exact Gf.finiteLocalLatticeStabilizer.mul_mem h.2
          (Gf.finiteLocalLatticeStabilizer.inv_mem h₀.2)
      refine ⟨⟨x, hxH⟩, ?_⟩
      rw [Gf.mem_localRightStabilizerInFiniteLocalLatticeStabilizer_iff,
        Gf.mem_localRightStabilizerSubgroup_iff]
      exact ⟨hxH, gamma.1, rfl⟩)
    (by
      constructor
      · intro gamma₁ gamma₂ hEq
        apply Subtype.ext
        apply Subtype.ext
        have hcarrier :
            g⁻¹ * (gamma₁.1 : Gf.carrier) * g =
              g⁻¹ * (gamma₂.1 : Gf.carrier) * g := by
          exact congrArg (fun s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g =>
            ((s : Gf.finiteLocalLatticeStabilizer) : Gf.carrier)) hEq
        calc
          (gamma₁.1 : Gf.carrier) =
              g * (g⁻¹ * (gamma₁.1 : Gf.carrier) * g) * g⁻¹ := by
                simp [mul_assoc]
          _ = g * (g⁻¹ * (gamma₂.1 : Gf.carrier) * g) * g⁻¹ := by
                rw [hcarrier]
          _ = (gamma₂.1 : Gf.carrier) := by
                simp [mul_assoc]
      · intro s
        rcases (Gf.mem_localRightStabilizerSubgroup_iff g
            (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
              Gf.finiteLocalLatticeStabilizer) : Gf.carrier)).mp s.2 with
          ⟨_hsH, gamma, hs_eq⟩
        let gammaWitness :
            { gamma : Gf.rationalOrthogonal //
              ∃ h : Gf.finiteLocalLatticeStabilizer,
                (gamma : Gf.carrier) * g * (h₀ : Gf.carrier) =
                  g * (h : Gf.carrier) } := by
          refine ⟨gamma, ?_⟩
          refine ⟨(s : Gf.finiteLocalLatticeStabilizer) * h₀, ?_⟩
          have hgamma_mul :
              (gamma : Gf.carrier) * g =
                g * (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
                  Gf.finiteLocalLatticeStabilizer) : Gf.carrier) := by
            calc
              (gamma : Gf.carrier) * g =
                  g * (g⁻¹ * (gamma : Gf.carrier) * g) := by
                    simp [mul_assoc]
              _ = g * (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
                    Gf.finiteLocalLatticeStabilizer) : Gf.carrier) := by
                    rw [← hs_eq]
          calc
            (gamma : Gf.carrier) * g * (h₀ : Gf.carrier) =
                (g * (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
                  Gf.finiteLocalLatticeStabilizer) : Gf.carrier)) *
                  (h₀ : Gf.carrier) := by
                    rw [hgamma_mul]
            _ = g * (((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
                  Gf.finiteLocalLatticeStabilizer) : Gf.carrier) *
                  (h₀ : Gf.carrier) := by
                    simp [mul_assoc]
            _ = g * ((((s : Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :
                  Gf.finiteLocalLatticeStabilizer) * h₀ :
                  Gf.finiteLocalLatticeStabilizer) : Gf.carrier) := by
                    simp [mul_assoc]
        refine ⟨gammaWitness, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hs_eq.symm)

theorem rationalElementsSendingRightTranslate_nat_card_eq_localRightStabilizerInFiniteLocalLatticeStabilizer
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (g : Gf.carrier) (h₀ : Gf.finiteLocalLatticeStabilizer) :
    Nat.card
        { gamma : Gf.rationalOrthogonal //
          ∃ h : Gf.finiteLocalLatticeStabilizer,
            (gamma : Gf.carrier) * g * (h₀ : Gf.carrier) =
              g * (h : Gf.carrier) } =
      Nat.card (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer g) :=
  Nat.card_congr
    (Gf.rationalElementsSendingRightTranslateEquivLocalRightStabilizerInFiniteLocalLatticeStabilizer
      g h₀)

/-- A chosen right-`H_f` coordinate for a point in the selected quotient-side
double-coset piece.  This turns the orbit-surjectivity statement
into data that can be fed to the periodized-indicator count. -/
noncomputable def doubleCosetQuotientPieceRightTranslateRepresentative
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (X : Gf.doubleCosetQuotientPiece C) :
    Gf.finiteLocalLatticeStabilizer :=
  Classical.choose (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece_surjective C X)

lemma rightStabilizerOrbitToDoubleCosetQuotientPiece_rightTranslateRepresentative
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (X : Gf.doubleCosetQuotientPiece C) :
    Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C
        (Gf.doubleCosetQuotientPieceRightTranslateRepresentative C X) = X :=
  Classical.choose_spec (Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece_surjective C X)

/-- The periodized-indicator count on one selected double-coset piece, written
as a function on the quotient-side piece.  At the point represented by
`g h₀`, it counts rational elements carrying `g h₀` into the right translate
`gH_f`.  The next quotient-measure theorem should integrate this function and
use the constant-value lemma below. -/
noncomputable def doubleCosetPiecePeriodizedIndicatorCount
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (X : Gf.doubleCosetQuotientPiece C) : ℝ≥0∞ :=
  let g := Gf.doubleCosetRepresentative C
  let h₀ := Gf.doubleCosetQuotientPieceRightTranslateRepresentative C X
  (Nat.card
      { gamma : Gf.rationalOrthogonal //
        ∃ h : Gf.finiteLocalLatticeStabilizer,
          (gamma : Gf.carrier) * g * (h₀ : Gf.carrier) =
            g * (h : Gf.carrier) } : ℝ≥0∞)

/-- The selected-piece periodized-indicator count is constant:
on the whole piece over `g`, the number of rational elements carrying a
representative point into `gH_f` is `|H_f ∩ g⁻¹Γg|`.

The Weil periodization/integration identity for this named function is not
proved here. -/
theorem doubleCosetPiecePeriodizedIndicatorCount_eq
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (X : Gf.doubleCosetQuotientPiece C) :
    Gf.doubleCosetPiecePeriodizedIndicatorCount C X =
      (Nat.card
        (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
          (Gf.doubleCosetRepresentative C)) : ℝ≥0∞) := by
  simp only [doubleCosetPiecePeriodizedIndicatorCount]
  exact_mod_cast
    Gf.rationalElementsSendingRightTranslate_nat_card_eq_localRightStabilizerInFiniteLocalLatticeStabilizer
      (Gf.doubleCosetRepresentative C)
      (Gf.doubleCosetQuotientPieceRightTranslateRepresentative C X)

/-- Canonical representative-slice periodization on the translated `H_f`
slice.

For a subset `A ⊆ H_f`, evaluate membership at the chosen right-translate
representative of the selected quotient point and, if it lies in `A`, attach
the already formal finite stabilizer count.  The lemma below proves that for
`A = orbit ⁻¹' B` this is exactly the selected-piece indicator
`B.indicator (doubleCosetPiecePeriodizedIndicatorCount C)`. -/
noncomputable def doubleCosetPieceRepresentativeSlicePeriodizedIndicator
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (A : Set Gf.finiteLocalLatticeStabilizer)
    (X : Gf.doubleCosetQuotientPiece C) : ℝ≥0∞ :=
  A.indicator (fun _ => Gf.doubleCosetPiecePeriodizedIndicatorCount C X)
    (Gf.doubleCosetQuotientPieceRightTranslateRepresentative C X)

/-- Periodization rewrite for translated slice preimages.

Once the ambient analytic periodization is compared with the canonical
representative-slice count above, Lean rewrites the preimage condition
`h₀ ∈ orbit ⁻¹' B` to the selected-piece condition `X ∈ B` using the chosen
right-translate representative of `X`. -/
theorem doubleCosetPieceRepresentativeSlicePeriodizedIndicator_preimage_eq_indicator
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (B : Set (Gf.doubleCosetQuotientPiece C)) :
    Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator C
        ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =
      B.indicator (Gf.doubleCosetPiecePeriodizedIndicatorCount C) := by
  funext X
  have hrep :
      Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C
          (Gf.doubleCosetQuotientPieceRightTranslateRepresentative C X) = X :=
    Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece_rightTranslateRepresentative C X
  by_cases hX : X ∈ B
  · simp [doubleCosetPieceRepresentativeSlicePeriodizedIndicator, hrep, hX]
  · simp [doubleCosetPieceRepresentativeSlicePeriodizedIndicator, hrep, hX]

/-- Almost-everywhere form of
`doubleCosetPieceRepresentativeSlicePeriodizedIndicator_preimage_eq_indicator`.

This is the exact rewrite used by the translated-slice quotient-measure route:
the remaining source input may compare the actual periodized function with the
canonical representative-slice count, and this theorem converts that count to
the selected-piece indicator. -/
theorem doubleCosetPieceRepresentativeSlicePeriodizedIndicator_preimage_ae_eq_indicator
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) (B : Set (Gf.doubleCosetQuotientPiece C))
    (mX : MeasurableSpace (Gf.doubleCosetQuotientPiece C))
    (μ : @Measure (Gf.doubleCosetQuotientPiece C) mX) :
    Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator C
        ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[μ]
      B.indicator (Gf.doubleCosetPiecePeriodizedIndicatorCount C) :=
  Filter.Eventually.of_forall (by
    intro X
    exact congrFun
      (Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator_preimage_eq_indicator
        C B) X)

/-- Convert the sharper representative-slice periodization comparison into
the indicator-form comparison currently stored in a finite-adelic
presentation.

Concrete Weil quotient constructions can prove the actual translated
periodization agrees with the canonical representative-slice count on
`orbit^{-1}(B)`.  This lemma then supplies the older
indicator-form field by rewriting the chosen representative back to the
selected quotient point. -/
theorem doubleCosetPieceTranslatedSlicePeriodize_eq_indicator_of_representativeSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (Periodize :
      Set Gf.finiteLocalLatticeStabilizer →
        Gf.doubleCosetQuotientPiece C → ℝ≥0∞)
    (hperiodize :
      ∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
        @MeasurableSet (Gf.doubleCosetQuotientPiece C)
          (Gf.doubleCosetPieceMeasurableSpace C) B →
        Periodize ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[
          Gf.doubleCosetPieceQuotientMeasure C]
          Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator C
            ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B)) :
    ∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetPieceMeasurableSpace C) B →
      Periodize ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[
        Gf.doubleCosetPieceQuotientMeasure C]
        B.indicator (Gf.doubleCosetPiecePeriodizedIndicatorCount C) := by
  intro B hB
  exact (hperiodize hB).trans
    (Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator_preimage_ae_eq_indicator
      C B (Gf.doubleCosetPieceMeasurableSpace C)
      (Gf.doubleCosetPieceQuotientMeasure C))

/-- Representative-slice periodization rewrite on orbit-map preimages.

The finite-adelic presentation stores this saturated-preimage form directly.
This is the only chosen-representative slice comparison used by the selected
quotient-piece volume route; arbitrary translated-slice subsets require the
stabilizer-orbit count instead. -/
theorem doubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) :
    ∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetPieceMeasurableSpace C) B →
      Gf.doubleCosetPieceTranslatedSlicePeriodize C
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[
        Gf.doubleCosetPieceQuotientMeasure C]
        Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator C
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) := by
  intro B hB
  exact
    Gf.doubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice_orbitPreimage
      C hB

/-- Translated quotient-integration formula on orbit-map preimages, projected
from the finite-adelic presentation field. -/
theorem doubleCosetPieceTranslatedSlicePeriodize_lintegral_eq_preimage_measure
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) :
    ∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetPieceMeasurableSpace C) B →
      ∫⁻ X,
          Gf.doubleCosetPieceTranslatedSlicePeriodize C
            ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) X
          ∂Gf.doubleCosetPieceQuotientMeasure C =
        Gf.finiteLocalLatticeStabilizerHaarMeasure
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) := by
  intro B hB
  exact
    Gf.doubleCosetPieceTranslatedSlicePeriodize_lintegral_eq_orbitPreimage
      C hB

set_option backward.isDefEq.respectTransparency false in
/-- Derived indicator-form periodization field.

The finite-adelic presentation now stores the sharper comparison with the
canonical representative-slice count.  This theorem recovers the previous
indicator-form interface by the representative-preimage rewrite
and the finite stabilizer cardinality comparison for any chosen right
translate representative. -/
theorem doubleCosetPieceTranslatedSlicePeriodize_eq_indicator
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet) :
    ∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetPieceMeasurableSpace C) B →
      Gf.doubleCosetPieceTranslatedSlicePeriodize C
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[
        Gf.doubleCosetPieceQuotientMeasure C]
        B.indicator
          (fun _ =>
            (Nat.card
              { h : Gf.finiteLocalLatticeStabilizer //
                ∃ gamma : Gf.rationalOrthogonal,
                  (h : Gf.carrier) =
                    (Gf.doubleCosetRepresentative C)⁻¹ *
                      (gamma : Gf.carrier) * Gf.doubleCosetRepresentative C } :
              ℝ≥0∞)) := by
  intro B hB
  have hgeneric :
      Gf.doubleCosetPieceTranslatedSlicePeriodize C
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[
        Gf.doubleCosetPieceQuotientMeasure C]
        B.indicator
          (leftRightDoubleCosetPiecePeriodizedIndicatorCount
            Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C) := by
    exact (Gf.doubleCosetPieceTranslatedSlicePeriodize_eq_representativeSlice C hB).trans
      (doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore_preimage_ae_eq_indicator
        Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C B
        (Gf.doubleCosetPieceMeasurableSpace C)
        (Gf.doubleCosetPieceQuotientMeasure C))
  refine hgeneric.trans ?_
  exact Filter.Eventually.of_forall (by
    intro X
    have hcount :
        Nat.card
            { gamma : Gf.rationalOrthogonal //
              ∃ h : Gf.finiteLocalLatticeStabilizer,
                (gamma : Gf.carrier) * Quot.out C *
                    (leftRightDoubleCosetPieceRightTranslateRepresentative
                      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C X :
                      Gf.carrier) =
                  Quot.out C * (h : Gf.carrier) } =
          Nat.card
            { h : Gf.finiteLocalLatticeStabilizer //
              ∃ gamma : Gf.rationalOrthogonal,
                (h : Gf.carrier) =
                  (Quot.out C)⁻¹ * (gamma : Gf.carrier) * Quot.out C } := by
      calc
        Nat.card
            { gamma : Gf.rationalOrthogonal //
              ∃ h : Gf.finiteLocalLatticeStabilizer,
                (gamma : Gf.carrier) * Quot.out C *
                    (leftRightDoubleCosetPieceRightTranslateRepresentative
                      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C X :
                      Gf.carrier) =
                  Quot.out C * (h : Gf.carrier) } =
            Nat.card
              (Gf.localRightStabilizerInFiniteLocalLatticeStabilizer
                (Quot.out C)) := by
          exact
            Gf.rationalElementsSendingRightTranslate_nat_card_eq_localRightStabilizerInFiniteLocalLatticeStabilizer
              (Quot.out C)
              (leftRightDoubleCosetPieceRightTranslateRepresentative
                Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C X)
        _ =
          Nat.card
            { h : Gf.finiteLocalLatticeStabilizer //
              ∃ gamma : Gf.rationalOrthogonal,
                (h : Gf.carrier) =
                  (Quot.out C)⁻¹ * (gamma : Gf.carrier) * Quot.out C } := by
          exact Nat.card_congr
            (Gf.localRightStabilizerInFiniteLocalLatticeStabilizerEquivSliceSubtype
              (Quot.out C))
    by_cases hX : X ∈ B
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
      change
        (Nat.card
            { gamma : Gf.rationalOrthogonal //
              ∃ h : Gf.finiteLocalLatticeStabilizer,
                (gamma : Gf.carrier) * Quot.out C *
                    (leftRightDoubleCosetPieceRightTranslateRepresentative
                      Gf.rationalOrthogonal Gf.finiteLocalLatticeStabilizer C X :
                      Gf.carrier) =
                  Quot.out C * (h : Gf.carrier) } : ℝ≥0∞) =
          (Nat.card
            { h : Gf.finiteLocalLatticeStabilizer //
              ∃ gamma : Gf.rationalOrthogonal,
                (h : Gf.carrier) =
                  (Quot.out C)⁻¹ * (gamma : Gf.carrier) * Quot.out C } :
            ℝ≥0∞)
      exact_mod_cast hcount
    · simp [hX])

/-- Compact-slice Weil source specialized to the current translated-slice
presentation fields.

The standard fixed-`g`, fixed-`H_f` quotient-integral theorem is naturally
stated for every measurable subset `A ⊆ H_f`: the actual translated
periodization of `A` agrees with the representative-slice count, and its
lintegral is the Haar measure of `A`.  This lemma specializes that standard
all-subsets input to the orbit-map preimages used by
`FiniteAdelicOrthogonalGroup`, proving exactly the two remaining
translated-slice fields. -/
theorem doubleCosetPieceTranslatedSlice_weilFields_of_compactSlice
    {L : PositiveDefiniteIntegralLattice n} (Gf : FiniteAdelicOrthogonalGroup.{u} L)
    (C : Gf.doubleCosetSet)
    (Periodize :
      Set Gf.finiteLocalLatticeStabilizer →
        Gf.doubleCosetQuotientPiece C → ℝ≥0∞)
    (hperiodize :
      ∀ ⦃A : Set Gf.finiteLocalLatticeStabilizer⦄,
        @MeasurableSet Gf.finiteLocalLatticeStabilizer
          Gf.finiteLocalLatticeStabilizerMeasurableSpace A →
        Periodize A =ᵐ[Gf.doubleCosetPieceQuotientMeasure C]
          Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator C A)
    (hWeil :
      ∀ ⦃A : Set Gf.finiteLocalLatticeStabilizer⦄,
        @MeasurableSet Gf.finiteLocalLatticeStabilizer
          Gf.finiteLocalLatticeStabilizerMeasurableSpace A →
        ∫⁻ X, Periodize A X ∂Gf.doubleCosetPieceQuotientMeasure C =
          Gf.finiteLocalLatticeStabilizerHaarMeasure A) :
    (∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetPieceMeasurableSpace C) B →
      Periodize ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) =ᵐ[
        Gf.doubleCosetPieceQuotientMeasure C]
        Gf.doubleCosetPieceRepresentativeSlicePeriodizedIndicator C
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B)) ∧
    (∀ ⦃B : Set (Gf.doubleCosetQuotientPiece C)⦄,
      @MeasurableSet (Gf.doubleCosetQuotientPiece C)
        (Gf.doubleCosetPieceMeasurableSpace C) B →
      ∫⁻ X, Periodize ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B) X
          ∂Gf.doubleCosetPieceQuotientMeasure C =
        Gf.finiteLocalLatticeStabilizerHaarMeasure
          ((Gf.rightStabilizerOrbitToDoubleCosetQuotientPiece C) ⁻¹' B)) := by
  constructor
  · intro B hB
    exact hperiodize ((Gf.rightOrbitToDoubleCosetPiece_measurable C) hB)
  · intro B hB
    exact hWeil ((Gf.rightOrbitToDoubleCosetPiece_measurable C) hB)

end FiniteAdelicOrthogonalGroup

end PositiveDefiniteIntegralLattice

end
