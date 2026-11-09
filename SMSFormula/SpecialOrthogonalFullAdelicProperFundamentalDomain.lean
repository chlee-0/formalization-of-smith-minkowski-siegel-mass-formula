import SMSFormula.SpecialOrthogonalFullAdelicProperDomainUniqueness

/-!
# Full-adelic proper fundamental domain

The lifted proper transversal is measurable and every full-adelic point has
exactly one rational diagonal subgroup element translating it into that set.
This module bundles those facts as a Mathlib
`IsFundamentalDomain`, first for an arbitrary ambient measure and then for the
internally constructed differential Haar measure.

No quotient measure or Weil identity is constructed here.
-/

noncomputable section

open MeasureTheory

set_option synthInstance.maxHeartbeats 100000

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Every full-adelic point has a unique rational diagonal subgroup element
which moves it into the lifted proper transversal. -/
theorem concreteFullAdelicProperTransversal_existsUnique_diagonal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    ∃! gamma : L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup,
      (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g ∈
        L.concreteFullAdelicProperTransversal := by
  rcases L.concreteFullAdelicProperTransversal_cover g with ⟨q, hq⟩
  let gamma : L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    ⟨L.rationalSpecialOrthogonalFullAdelicDiagonalHom q, ⟨q, rfl⟩⟩
  refine ⟨gamma, by simpa [gamma] using hq, ?_⟩
  intro gamma' hgamma'
  rcases gamma'.2 with ⟨q', hq'⟩
  have hq'mem :
      L.rationalSpecialOrthogonalFullAdelicDiagonalHom q' * g ∈
        L.concreteFullAdelicProperTransversal := by
    rw [hq']
    exact hgamma'
  have hqq' : q = q' :=
    L.concreteFullAdelicProperTransversal_rationalDiagonal_unique
      g q q' hq hq'mem
  subst q'
  apply Subtype.ext
  exact hq'.symm

/-- The lifted proper transversal is a fundamental domain for the rational
diagonal subgroup with respect to any ambient measure. -/
theorem concreteFullAdelicProperTransversal_isFundamentalDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (μ : Measure L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    IsFundamentalDomain
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      L.concreteFullAdelicProperTransversal μ := by
  apply IsFundamentalDomain.mk'
    (L.concreteFullAdelicProperTransversal_measurableSet
      inst).nullMeasurableSet
  intro g
  change ∃! gamma : L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup,
    (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g ∈
      L.concreteFullAdelicProperTransversal
  exact L.concreteFullAdelicProperTransversal_existsUnique_diagonal g

/-- In particular, the lifted proper transversal is a fundamental domain for
the internally constructed full-adelic differential Haar measure. -/
theorem concreteFullAdelicProperTransversal_isFundamentalDomain_differential
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (P : ℝ) :
    IsFundamentalDomain
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      L.concreteFullAdelicProperTransversal
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
  L.concreteFullAdelicProperTransversal_isFundamentalDomain inst
    (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)

end PositiveDefiniteIntegralLattice
