import SMSFormula.SpecialOrthogonalFullAdelicProperQuotientEquiv
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient

/-!
# Measurability of proper-domain normalization

The preimage of a measurable proper-domain set under normalization is the
countable union of its rational diagonal translates.  This makes the exact
carrier equivalence between the concrete rational adelic `SO` quotient and
the proper fundamental-domain subtype a measurable equivalence, using the
literal quotient measurable structure already present in the project.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- Membership after proper normalization is detected by one rational
diagonal translate landing in the corresponding subtype set. -/
theorem preimage_concreteFullAdelicProperNormalization
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (s : Set {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      z ∈ L.concreteFullAdelicProperTransversal}) :
    L.concreteFullAdelicProperNormalization ⁻¹' s =
      ⋃ gamma : L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup,
        (fun g : L.ConcreteFullAdelicSpecialOrthogonalGroup =>
          (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) ⁻¹'
            (((↑) :
              {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
                z ∈ L.concreteFullAdelicProperTransversal} →
                  L.ConcreteFullAdelicSpecialOrthogonalGroup) '' s) := by
  ext g
  constructor
  · intro hg
    rw [Set.mem_iUnion]
    refine ⟨L.concreteFullAdelicProperNormalizerDiagonal g, ?_⟩
    exact ⟨L.concreteFullAdelicProperNormalization g, hg, rfl⟩
  · rw [Set.mem_iUnion]
    rintro ⟨gamma, z, hz, hzg⟩
    have hgamma :
        ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) ∈
          L.concreteFullAdelicProperTransversal := by
      change z.1 =
        (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g at hzg
      rw [← hzg]
      exact z.2
    have heq : gamma = L.concreteFullAdelicProperNormalizerDiagonal g :=
      (Classical.choose_spec
        (L.concreteFullAdelicProperTransversal_existsUnique_diagonal g)).2
        gamma hgamma
    have hnorm : L.concreteFullAdelicProperNormalization g = z := by
      apply Subtype.ext
      change
        (L.concreteFullAdelicProperNormalizerDiagonal g :
            L.ConcreteFullAdelicSpecialOrthogonalGroup) * g = z.1
      rw [← heq, hzg]
    change L.concreteFullAdelicProperNormalization g ∈ s
    rwa [hnorm]

/-- Proper-domain normalization is measurable. -/
theorem measurable_concreteFullAdelicProperNormalization
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    Measurable L.concreteFullAdelicProperNormalization := by
  letI : Countable L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup_countable
  intro s hs
  rw [L.preimage_concreteFullAdelicProperNormalization s]
  apply MeasurableSet.iUnion
  intro gamma
  apply MeasurableSet.preimage
  · exact MeasurableSet.subtype_image
      (L.concreteFullAdelicProperTransversal_measurableSet inst) hs
  · exact (continuous_const.mul continuous_id).measurable

/-- The normalization map descended to the literal concrete `SO` quotient
is measurable. -/
theorem measurable_concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    Measurable L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hnorm := L.measurable_concreteFullAdelicProperNormalization inst
  simpa [concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain,
    Function.comp_def] using measurable_iff_comap_le.mp hnorm

/-- The exact proper fundamental domain and the concrete rational adelic
`SO` quotient are measurably equivalent. -/
noncomputable def concreteFullAdelicSpecialOrthogonalLeftQuotientProperDomainMeasurableEquiv
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient ≃ᵐ
      {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
        z ∈ L.concreteFullAdelicProperTransversal} where
  toEquiv := L.concreteFullAdelicSpecialOrthogonalLeftQuotientProperDomainEquiv
  measurable_toFun :=
    L.measurable_concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain inst
  measurable_invFun :=
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap_measurable.comp
      measurable_subtype_coe

end PositiveDefiniteIntegralLattice
