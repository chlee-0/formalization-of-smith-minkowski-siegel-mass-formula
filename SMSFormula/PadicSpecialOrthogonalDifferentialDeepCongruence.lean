import SMSFormula.PadicSpecialOrthogonalDifferentialCongruence
import SMSFormula.PadicCayleyTranslatedChartRecovery

/-!
# Deep corrected p-adic special congruence subgroups

The determinant-one congruence kernels form a neighborhood basis at the
identity.  The proof uses compactness of the integral stabilizer: the kernels
are decreasing, open-and-closed, and their intersection is the identity
because all p-power reductions separate p-adic integers.

Transporting this basis through the common-matrix continuous multiplicative
equivalence places one sufficiently deep direct kernel inside the
identity-centered Cayley target.  Its inverse Cayley image is then packaged as
a compact-open measurable source set.  Its coordinate mass is not evaluated
here.
-/

noncomputable section

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialDeepCongruenceSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDeepCongruenceSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance
    localPadicSpecialOrthogonalDifferentialDeepCongruenceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDeepCongruenceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The original determinant-one depth-`k` principal congruence subgroup. -/
def localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) :=
  (L.localPadicSpecialOrthogonalLatticeStabilizerReduction p k).ker

/-- Original special principal-congruence membership is entrywise
congruence to the identity. -/
@[simp]
theorem mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) :
    g ∈ L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup p k ↔
      ∀ i j, PadicInt.toZModPow k
        (L.localPadicLatticeStabilizerIntegralGL p g.1 i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
  change
    L.localPadicSpecialOrthogonalLatticeStabilizerReduction p k g = 1 ↔ _
  rw [← L.mem_localPadicPrincipalCongruenceSubgroup_iff p k g.1]
  constructor
  · intro h
    exact congrArg (fun u ↦ u.1.1) h
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact h

/-- Deeper original special congruence subgroups are smaller. -/
theorem
    antitone_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Antitone
      (fun k ↦
        (L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
          p k :
          Set
            (L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p))) := by
  intro k l hkl g hg
  change
    g ∈ L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
      p l at hg
  change
    g ∈ L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
      p k
  rw [L.mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
    p l g] at hg
  rw [L.mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
    p k g]
  intro i j
  rw [← PadicInt.cast_toZModPow k l hkl]
  rw [hg i j]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply, if_pos]
    exact ZMod.cast_one (pow_dvd_pow p hkl)
  · simp [hij]

/-- An element lying in every original special congruence kernel is the
identity. -/
theorem
    eq_one_of_mem_all_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p)
    (hg : ∀ k,
      g ∈ L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
        p k) :
    g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  let a : ℤ_[p] :=
    L.localPadicLatticeStabilizerIntegralGL p g.1 i j
  let b : ℤ_[p] := if i = j then 1 else 0
  have hab : a = b := PadicInt.ext_of_toZModPow.mp fun k ↦ by
    have hk :=
      (L.mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
        p k g).mp (hg k) i j
    rw [hk]
    by_cases hij : i = j
    · subst j
      simp [b]
    · simp [b, hij]
  calc
    g.1.1.1.1 i j =
        ((L.localPadicLatticeStabilizerIntegralGL p g.1 i j : ℤ_[p]) :
          ℚ_[p]) := by
      symm
      exact L.localPadicLatticeStabilizerIntegralGL_apply p g.1 i j
    _ = (b : ℚ_[p]) := congrArg Subtype.val hab
    _ = (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j := by
      by_cases hij : i = j
      · subst j
        simp [b]
      · simp [b, hij]

/-- Original special principal-congruence subgroups are open. -/
theorem
    isOpen_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup p k :
        Set
          (L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p)) := by
  change IsOpen
    ((L.localPadicSpecialOrthogonalLatticeStabilizerReduction p k) ⁻¹'
      ({1} : Set
        (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
          p k)))
  exact
    (isOpen_discrete
      ({1} : Set
        (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
          p k))).preimage
      (L.continuous_localPadicSpecialOrthogonalLatticeStabilizerReduction
        p k)

/-- Original special principal-congruence subgroups form a neighborhood
basis at the identity. -/
theorem
    exists_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_subset
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    {U : Set (L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p)}
    (hU : IsOpen U) (hone : (1 :
      L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) ∈ U) :
    ∃ k,
      (L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup p k :
        Set
          (L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p)) ⊆ U := by
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let H :=
    L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p
  let e :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv p
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp
      (L.isCompact_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
  letI : CompactSpace H := e.toHomeomorph.compactSpace
  by_contra hex
  have hnone : ∀ k, ¬
      (L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup p k :
        Set H) ⊆ U := by
    simpa only [not_exists] using hex
  let t : ℕ → Set H := fun k ↦
    (L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup p k :
      Set H) ∩ Uᶜ
  have htanti : ∀ k, t (k + 1) ⊆ t k := by
    intro k g hg
    exact
      ⟨L.antitone_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
          p (Nat.le_succ k) hg.1,
        hg.2⟩
  have htnonempty : ∀ k, (t k).Nonempty := by
    intro k
    rcases Set.not_subset.mp (hnone k) with ⟨g, hgk, hgU⟩
    exact ⟨g, hgk, hgU⟩
  have htclosed : ∀ k, IsClosed (t k) := by
    intro k
    exact
      (L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup p k)
        |>.isClosed_of_isOpen
          (L.isOpen_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
            p k)
        |>.inter hU.isClosed_compl
  have htcompact : IsCompact (t 0) := (htclosed 0).isCompact
  rcases
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        t htanti htnonempty htcompact htclosed with
    ⟨g, hg⟩
  have hgall : ∀ k,
      g ∈ L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
        p k := by
    intro k
    exact (Set.mem_iInter.mp hg k).1
  have hgnot : g ∈ Uᶜ := (Set.mem_iInter.mp hg 0).2
  rw [
    L.eq_one_of_mem_all_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
      p g hgall] at hgnot
  exact hgnot hone

/-- Direct corrected principal-congruence membership is exactly original
principal-congruence membership after the common-matrix equivalence. -/
@[simp]
theorem
    mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :
    g ∈
        L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p k ↔
      L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
          p g ∈
        L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
          p k :=
  Iff.rfl

/-- Direct corrected principal-congruence subgroups form a neighborhood basis
at the identity. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    {U : Set
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)}
    (hU : IsOpen U) (hone : (1 :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) ∈ U) :
    ∃ k,
      (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p k :
        Set
          (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) ⊆
        U := by
  let e :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv p
  let V : Set
      (L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) :=
    e.toHomeomorph.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage e.toHomeomorph.symm.continuous
  have honeV : (1 :
      L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) ∈ V := by
    change e.toHomeomorph.symm 1 ∈ U
    simpa only [map_one] using hone
  rcases
      L.exists_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_subset
        p hV honeV with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro g hg
  have hegi :
      e g ∈
        L.localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
          p k :=
    (L.mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
      p k g).mp hg
  have heU := hk hegi
  change e.toHomeomorph.symm (e g) ∈ U at heU
  simpa using heU

/-- Some sufficiently deep direct principal-congruence kernel lies in the
identity-centered exact translated Cayley target. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_identityCayleyTarget
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ k, ∀
      g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p,
      g ∈
          L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p k →
        (g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
          padicCayleySpecialOrthogonalTranslatedTarget
            L.rationalFormMatrix p 1 := by
  let U : Set
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :=
    {g |
      (g :
        specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
        padicCayleySpecialOrthogonalTranslatedTarget
          L.rationalFormMatrix p 1}
  have hU : IsOpen U :=
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1).preimage continuous_subtype_val
  have hone : (1 :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) ∈ U := by
    exact self_mem_padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1
  rcases
      L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset
        p hU hone with
    ⟨k, hk⟩
  exact ⟨k, fun g hg ↦ hk hg⟩

/-- A chosen depth whose direct special principal-congruence kernel lies in
the identity-centered Cayley target. -/
def localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Classical.choose
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_identityCayleyTarget
      p)

/-- The chosen deep direct kernel lies in the identity-centered Cayley
target. -/
theorem
    localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth_spec
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p)) :
    (g :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1 :=
  Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_identityCayleyTarget
      p) g hg

/-- The chosen deep principal-congruence kernel as a literal subset of the
ambient p-adic special-orthogonal group. -/
def localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Subtype.val ''
    (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p) :
      Set
        (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p))

/-- The chosen deep kernel is open in the ambient p-adic special-orthogonal
group. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet p) := by
  exact
    (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      |>.isOpenEmbedding_subtypeVal.isOpenMap
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p))
        (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p))

/-- The chosen deep kernel is compact in the ambient p-adic
special-orthogonal group. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet p) := by
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let K :=
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
      p (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p)
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp
      (L.isCompact_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
  have hKclosed : IsClosed (K : Set D) :=
    K.isClosed_of_isOpen
      (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p))
  exact hKclosed.isCompact.image continuous_subtype_val

/-- The chosen ambient deep kernel is contained in the identity-centered
Cayley target. -/
theorem
    localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet_subset_target
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet p ⊆
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1 := by
  rintro g ⟨h, hh, rfl⟩
  exact
    L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth_spec
      p h hh

/-- The chosen deep kernel represented inside the exact identity-centered
translated target subtype. -/
def localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1) :=
  Subtype.val ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet p

/-- Including the exact-target representation of the chosen kernel recovers
its literal ambient representation. -/
theorem
    image_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subtype.val ''
        L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p =
      L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet p := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hg
    exact
      ⟨⟨g,
          L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet_subset_target
            p hg⟩,
        hg, rfl⟩

/-- The chosen deep kernel is open inside the exact identity-centered
translated target. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
    p).preimage continuous_subtype_val

/-- The chosen deep kernel is measurable inside the exact identity-centered
translated target. -/
theorem
    measurableSet_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSet
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p)
    |>.measurableSet

/-- The chosen deep kernel pulled back through the exact identity-centered
Cayley chart. -/
def localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p

/-- The chosen source-side deep congruence set is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p) :=
  ((L.isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
      p).preimage continuous_subtype_val).preimage
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).continuous

/-- The chosen source-side deep congruence set is compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p) := by
  have htarget :
      IsCompact
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
          p) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
      L.image_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
        p]
    exact
      L.isCompact_localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
        p
  exact
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1)
      |>.isCompact_preimage.mpr htarget

/-- The chosen source-side deep congruence set is measurable. -/
theorem
    measurableSet_localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSet
      (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p)
    |>.measurableSet

/-! ## Literal corrected differential mass transport -/

/-- The exact identity-centered target differential assigns the chosen target
set the global corrected differential mass of the literal ambient kernel. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_cayleyCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero 1
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p) =
      padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
          p) := by
  have hFsymm : L.rationalFormMatrix.IsSymm := L.form_symm.map _
  rw [←
    comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
      p n L.rationalFormMatrix hFsymm
        L.rationalFormMatrix_det_ne_zero 1]
  rw [comap_subtype_coe_apply
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1).measurableSet]
  rw [
    L.image_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet p]

/-- The source differential mass of the inverse-Cayley kernel equals the
corrected differential mass of its exact target representation. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_cayleyCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p) =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero 1
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
          p) := by
  rw [padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure,
    Measure.map_apply
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).measurable
      (L.measurableSet_localPadicSpecialOrthogonalDifferentialCayleyCongruenceTargetSet
        p)]
  rfl

/-- The corrected stabilizer measure of the chosen principal kernel is the
global corrected differential mass of its literal ambient representation. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerMeasure_cayleyCongruenceKernel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p
            (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth
              p) :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) =
      padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
          p) := by
  let G :=
    specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let K :=
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
      p (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth p)
  let μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure
      p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
  let ν := L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
  let A :=
    L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet p
  have hmap : Measure.map (fun g : D ↦ (g : G)) ν =
      μ.restrict (D : Set G) := by
    change
      Measure.map (fun g : D ↦ (g : G))
          (Measure.comap (fun g : D ↦ (g : G)) μ) =
        μ.restrict (D : Set G)
    exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace D
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasurableSpace_eq p)
      (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
        p).measurableSet
  have hAmeas : MeasurableSet A :=
    (L.isOpen_localPadicSpecialOrthogonalDifferentialCayleyCongruenceAmbientSet
      p).measurableSet
  have hpre : (fun g : D ↦ (g : G)) ⁻¹' A = (K : Set D) := by
    ext g
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨h, hh, heq⟩
      have hhg : h = g := Subtype.ext heq
      exact hhg ▸ hh
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hAsub : A ⊆ (D : Set G) := by
    rintro g ⟨h, hh, rfl⟩
    exact h.property
  change ν (K : Set D) = μ A
  calc
    ν (K : Set D) =
        Measure.map (fun g : D ↦ (g : G)) ν A := by
      rw [Measure.map_apply continuous_subtype_val.measurable hAmeas, hpre]
    _ = μ.restrict (D : Set G) A :=
      congrArg (fun ρ : Measure G ↦ ρ A) hmap
    _ = μ A := by
      rw [Measure.restrict_apply hAmeas, Set.inter_eq_left.mpr hAsub]

/-- The chosen inverse-Cayley source set has exactly the corrected
differential mass of the chosen direct principal-congruence kernel. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_cayleyCongruenceSourceSet_eq_stabilizerMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p
            (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth
              p) :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) := by
  rw [
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_cayleyCongruenceSourceSet
      p,
    L.padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_cayleyCongruenceTargetSet
      p,
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure_cayleyCongruenceKernel
      p]

/-- Combining literal chart transport with finite-index Haar algebra expresses
the chosen inverse-Cayley source mass through the actual finite reduction
image.  No coordinate mass is evaluated here. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_cayleyCongruenceSourceSet_eq_volume_mul_inv_natCard_range
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceSourceSet p) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (Nat.card
          (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
            p
            (L.localPadicSpecialOrthogonalDifferentialCayleyCongruenceDepth
              p)).range : ℝ≥0∞)⁻¹ := by
  rw [
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_cayleyCongruenceSourceSet_eq_stabilizerMeasure
      p,
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_measure
      p]

end PositiveDefiniteIntegralLattice
