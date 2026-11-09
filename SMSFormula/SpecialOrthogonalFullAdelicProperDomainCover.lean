import SMSFormula.SpecialOrthogonalFullAdelicProperDomainCarrier

/-!
# Strict cover by the full-adelic proper transversal

The exact finite right-transversal cover is exposed independently of its
later measure-theoretic fundamental-domain packaging.  Its rational witness
then lifts through the concrete real/finite splitting to the full-adelic
proper domain.

This module is set-theoretic.  It does not choose a quotient
measure or assert a Weil formula.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Every finite-adelic special-orthogonal element can be moved into the
concrete proper finite transversal by one rational special-orthogonal
diagonal element. -/
theorem concreteProperFiniteTransversalFundamentalDomain_cover
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    ∃ q : L.rationalSpecialOrthogonalMatrixSubgroup,
      L.rationalSpecialOrthogonalDiagonalHom q * g ∈
        L.concreteProperFiniteTransversalFundamentalDomain := by
  let slice : L.ConcreteProperRationalDoubleCosetSet →
      Set L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C)
  have htrans : ∀ C : L.ConcreteProperRationalDoubleCosetSet,
      IsLeftCosetTransversal
        (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
          (Quot.out C))
        (slice C) := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
      (Quot.out C)
  have hlocal : ∀ C : L.ConcreteProperRationalDoubleCosetSet,
      ∀ h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup,
        ∃ gamma : L.rationalSpecialOrthogonalDiagonalSubgroup,
          ∃ c : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup,
            c ∈ slice C ∧
              (gamma : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) *
                  (Quot.out C *
                    (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)) =
                Quot.out C *
                  (c : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
    intro C
    exact local_right_cover_of_stabilizer_transversal
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup (Quot.out C)
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        (Quot.out C))
      (slice C)
      (L.concreteProperLocalRightStabilizer_conjugates (Quot.out C))
      (htrans C).decomp
  have hcover :=
    finiteRightTransversalFundamentalDomain_cover_of_local_right_cover
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C) slice hlocal
  rcases hcover g with ⟨gamma, C, c, hc, hgamma⟩
  rcases gamma.2 with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply (mem_finiteRightTransversalFundamentalDomain
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
    slice (L.rationalSpecialOrthogonalDiagonalHom q * g)).2
  refine ⟨C, c, hc, ?_⟩
  rw [← hgamma, hq]

/-- Every concrete full-adelic special-orthogonal element can be moved into
the lifted proper domain by one rational diagonal element. -/
theorem concreteFullAdelicProperTransversal_cover
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    ∃ q : L.rationalSpecialOrthogonalMatrixSubgroup,
      L.rationalSpecialOrthogonalFullAdelicDiagonalHom q * g ∈
        L.concreteFullAdelicProperTransversal := by
  rcases L.concreteProperFiniteTransversalFundamentalDomain_cover
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [L.mem_concreteFullAdelicProperTransversal_iff]
  simpa using hq

end PositiveDefiniteIntegralLattice
