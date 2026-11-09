import SMSFormula.CompactOrbitContinuousTests
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# The orbit hypotheses become subgroup hypotheses

The assembled comparison holds from structural data alone, but two of those data are properties of
the orbit `U = K . x_0`: that it is compact and that it is open.  Neither is a thing one exhibits.
What one can exhibit is a compact open subgroup of the acting group, and the adelic
candidate is presented as a subgroup, not as an orbit.  This file closes that mismatch: both orbit
hypotheses are derived from the corresponding properties of the subgroup.

Compactness is immediate -- the orbit is the continuous image of the subgroup's carrier.  Openness
is the content: the orbit is the orbit-map image of an open set, and the orbit map is open by the
Baire argument already located in mathlib (`isOpenMap_smul_of_sigmaCompact`), whose pretransitivity
hypothesis is the transitivity the comparison already assumes.  So openness of the orbit needs
nothing more.

The auxiliary probability Haar is also not a hypothesis.  A compact subgroup is a compact group, and
mathlib's `haarMeasure` at the top positive-compact set is left invariant with total mass one, so the
averaging measure the chain consumes exists and is not an extra thing to supply.  Likewise the
auxiliary invariance: a measure invariant under the whole acting group is invariant under any
subgroup of it, so the chain's two invariance hypotheses collapse to one.

The resulting comparison reads: for a `sigma`-compact acting group acting continuously and
transitively on a Baire second-countable locally compact `T2` space, and a compact open subgroup `K`,
any two nonzero regular invariant measures satisfy `nu(K . x_0) * mu = mu(K . x_0) * nu`.  Every
hypothesis is about `G`, `X` or `K` -- nothing about the orbit, and nothing about any test.

Scope.  The conclusion is cross-multiplied, satisfied by a measure and its
double, so it gives no equality and the scalar remains a ratio.  Nothing here is adelic: no compact
open subgroup of an adelic acting group is constructed and the abstract hypotheses -- `sigma`-
compactness, Baire, `T2`, second countability, local compactness -- are not verified.  The numerical
identity `Lambda(1_U) = mu_nat(U)` is not proved here, and normalising the auxiliary Haar is not
normalising the unknown Spin volume.
-/

namespace SMSFormula.CompactOrbit

open MeasureTheory Set Pointwise MulAction TopologicalSpace
open scoped ENNReal

/-! ## The orbit of a subgroup -/

section Carrier

variable {G X : Type*} [Group G] [TopologicalSpace G] [MulAction G X] [TopologicalSpace X]

omit [TopologicalSpace G] [TopologicalSpace X] in
/-- The chain's orbit -- a range over the subgroup's coercion to a type -- is the image of the
subgroup's carrier under the orbit map.  This is the bridge between the form the comparison is
stated in and the form a subgroup is exhibited in. -/
theorem range_subtype_smul_eq_image (K : Subgroup G) (x₀ : X) :
    (Set.range fun l : K ↦ l • x₀) = (fun g : G ↦ g • x₀) '' (K : Set G) := by
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨(l : G), l.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- Compactness of the orbit from compactness of the subgroup: the orbit is the continuous image of
the carrier. -/
theorem isCompact_subgroupSmulOrbit [ContinuousSMul G X] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (x₀ : X) : IsCompact (Set.range fun l : K ↦ l • x₀) := by
  rw [range_subtype_smul_eq_image]
  exact hK.image (continuous_id.smul continuous_const)

end Carrier

section Openness

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MulAction G X]
  [TopologicalSpace X] [SigmaCompactSpace G] [BaireSpace X] [T2Space X] [ContinuousSMul G X]

/-- Openness of the orbit from openness of the subgroup.  The orbit map is open by mathlib's Baire
argument, whose transitivity hypothesis is already assumed, so the image of the open
carrier is open. -/
theorem isOpen_subgroupSmulOrbit [IsPretransitive G X] (K : Subgroup G) (hK : IsOpen (K : Set G))
    (x₀ : X) : IsOpen (Set.range fun l : K ↦ l • x₀) := by
  rw [range_subtype_smul_eq_image]
  exact isOpenMap_smul_of_sigmaCompact x₀ _ hK

end Openness

/-! ## Transitivity in the two forms, and invariance along a subgroup -/

section Transfer

variable {G X : Type*} [Group G] [MulAction G X]

/-- The chain's transitivity predicate gives mathlib's. -/
theorem isPretransitive_of_isTransitiveAction (h : IsTransitiveAction G X) :
    IsPretransitive G X :=
  ⟨fun x y ↦ h x y⟩

/-- And conversely, so the two forms are interchangeable and no new transitivity input is needed. -/
theorem isTransitiveAction_of_isPretransitive [IsPretransitive G X] : IsTransitiveAction G X :=
  fun x y ↦ IsPretransitive.exists_smul_eq x y

/-- Invariance along a subgroup is free: a measure invariant under the acting group is invariant
under any subgroup of it, so the chain's auxiliary invariance hypothesis is not separate. -/
theorem smulInvariantMeasure_subgroup [MeasurableSpace X] (K : Subgroup G) (μ : Measure X)
    [SMulInvariantMeasure G X μ] : SMulInvariantMeasure K X μ :=
  ⟨fun l _ hs ↦ SMulInvariantMeasure.measure_preimage_smul (μ := μ) (l : G) hs⟩

end Transfer

/-! ## The auxiliary probability Haar exists -/

/-- A compact group carries a left-invariant probability measure, so the averaging measure the
comparison consumes is not an extra hypothesis.  It is mathlib's `haarMeasure` at the top
positive-compact set, whose normalisation `haarMeasure K₀ K₀ = 1` reads as total mass one there. -/
theorem exists_isProbabilityMeasure_isMulLeftInvariant (K : Type*) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] :
    ∃ haar : Measure K, IsProbabilityMeasure haar ∧ haar.IsMulLeftInvariant := by
  refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance⟩
  have h := Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts K))
  rwa [PositiveCompacts.coe_top] at h

/-! ## The comparison with hypotheses only on `G`, `X` and the subgroup -/

/-- The comparison from a compact open subgroup.  Every hypothesis is about the acting group, the
space, or the subgroup: nothing about the orbit, nothing about any test, and no auxiliary measure
supplied.  This is the form to instantiate. -/
theorem smul_measure_eq_of_compactOpen_subgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [T2Space G] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MulAction G X]
    [ContinuousSMul G X] [MeasurableConstSMul G X] (μ nu : Measure X) [μ.Regular] [nu.Regular]
    [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X nu] (htrans : IsTransitiveAction G X)
    (x₀ : X) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    (nu ((fun g : G ↦ g • x₀) '' (K : Set G))) • μ =
      (μ ((fun g : G ↦ g • x₀) '' (K : Set G))) • nu := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology ↥(K : Set G))
  haveI : IsPretransitive G X := isPretransitive_of_isTransitiveAction htrans
  haveI := smulInvariantMeasure_subgroup K μ
  haveI := smulInvariantMeasure_subgroup K nu
  obtain ⟨haar, hprob, hinv⟩ := exists_isProbabilityMeasure_isMulLeftInvariant K
  haveI := hprob
  haveI := hinv
  rw [← range_subtype_smul_eq_image]
  exact smul_measure_eq_of_compactOpen_orbit haar μ nu htrans x₀
    (isOpen_subgroupSmulOrbit K hKo x₀) (isCompact_subgroupSmulOrbit K hKc x₀)

/-- The pinning side conditions, also from the subgroup.  The orbit of a compact open subgroup has
measure strictly between zero and infinity for every nonzero invariant regular measure -- exactly the
two conditions the fiber-scalar pinning consumes, and the subgroup supplies its own nonemptiness
through the identity. -/
theorem measure_pos_lt_top_of_compactOpen_subgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SigmaCompactSpace G] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ] [μ.Regular] (htrans : IsTransitiveAction G X)
    (x₀ : X) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hμ : μ ≠ 0) :
    0 < μ ((fun g : G ↦ g • x₀) '' (K : Set G)) ∧
      μ ((fun g : G ↦ g • x₀) '' (K : Set G)) < ⊤ := by
  haveI : IsPretransitive G X := isPretransitive_of_isTransitiveAction htrans
  exact measure_pos_lt_top_of_compactOpen_orbit μ htrans hKc hKo ⟨1, K.one_mem⟩
    (continuous_id.smul continuous_const) (isOpenMap_smul_of_sigmaCompact x₀) hμ

/-- Proportionality with the scalar written out.  Dividing the cross-multiplied
identity is legitimate exactly because the orbit mass is neither zero nor infinite, which the previous
theorem supplies from the subgroup.  The
scalar is the ratio of the two orbit masses, and evaluating it needs an independent computation of
both, which invariance never performs. -/
theorem eq_smul_of_compactOpen_subgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [T2Space G] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MulAction G X]
    [ContinuousSMul G X] [MeasurableConstSMul G X] (μ nu : Measure X) [μ.Regular] [nu.Regular]
    [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X nu] (htrans : IsTransitiveAction G X)
    (x₀ : X) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hnu : nu ≠ 0) :
    μ = (μ ((fun g : G ↦ g • x₀) '' (K : Set G)) /
      nu ((fun g : G ↦ g • x₀) '' (K : Set G))) • nu := by
  obtain ⟨hpos, htop⟩ :=
    measure_pos_lt_top_of_compactOpen_subgroup nu htrans x₀ K hKc hKo hnu
  have h := smul_measure_eq_of_compactOpen_subgroup μ nu htrans x₀ K hKc hKo
  calc μ = (nu ((fun g : G ↦ g • x₀) '' (K : Set G)))⁻¹ •
        ((nu ((fun g : G ↦ g • x₀) '' (K : Set G))) • μ) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hpos.ne' htop.ne, one_smul]
    _ = (nu ((fun g : G ↦ g • x₀) '' (K : Set G)))⁻¹ •
        ((μ ((fun g : G ↦ g • x₀) '' (K : Set G))) • nu) := by rw [h]
    _ = _ := by rw [smul_smul, mul_comm, ← div_eq_mul_inv]

/-- Equality at one orbit suffices.  Once the two measures are proportional with the
scalar the ratio of the orbit masses, agreement at the single set `U` forces the scalar to be one
and the measures to be equal.  So the hypothesis needed is not a family of tests and not an
identity of functionals: it is the equality of two masses at one compact open orbit -- and that
equality is sufficient, not merely necessary.  It is a separate computation, which invariance never
performs. -/
theorem eq_of_measure_orbit_eq {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MulAction G X] [ContinuousSMul G X] [MeasurableConstSMul G X]
    (μ nu : Measure X) [μ.Regular] [nu.Regular] [SMulInvariantMeasure G X μ]
    [SMulInvariantMeasure G X nu] (htrans : IsTransitiveAction G X) (x₀ : X) (K : Subgroup G)
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (hnu : nu ≠ 0)
    (hmass : μ ((fun g : G ↦ g • x₀) '' (K : Set G)) =
      nu ((fun g : G ↦ g • x₀) '' (K : Set G))) :
    μ = nu := by
  obtain ⟨hpos, htop⟩ := measure_pos_lt_top_of_compactOpen_subgroup nu htrans x₀ K hKc hKo hnu
  have h := eq_smul_of_compactOpen_subgroup μ nu htrans x₀ K hKc hKo hnu
  rwa [hmass, ENNReal.div_self hpos.ne' htop.ne, one_smul] at h

end SMSFormula.CompactOrbit
