import SMSFormula.RationalAdeleFiniteLocalReplacementLocalRatio
import SMSFormula.PadicQuadraticOrbitCarrierResidueData
import SMSFormula.QuadraticPadicCayleyGoodPlaceMass

/-!
# Bridging the replacement lemma to the Cayley orbit side

The replacement lemma works with the p-adic quadratic map of the lattice Gram matrix, while
the stabilizer atlas-glue theorem works with the commutative scalar extension of the
rational form `V`.  For a supplied lattice with `L.rationalFormMatrix = V.pairingMatrix` the two
Gram matrices over `ℚ_p` coincide.  To avoid transporting atlases across a propositional equality
of forms, the local ratio is restated for any matrix `G` equal to the lattice matrix (the equality
is then substituted), so it can be read directly in the form `G = V.pairingMatrix.map (ℚ → ℚ_p)`.

Glue masses of a carrying restricted set and of the carried set agree across two atlases: the
slices coincide on the shell, and atlas independence compares the two glues on any
measurable set covered by both.  With these, the local mass `glue_M(T_{R_p})` of the replacement
lemma is the orbit glue `glue_M(K · x_old)` of the stabilizer theorem.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Matrix Set
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance obPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance obPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The Gram bridge: a lattice whose rational Gram matrix is `G` has `p`-adic Gram matrix
`G.map (ℚ → ℚ_p)`. -/
theorem padicFormMatrix_eq_map_of_rationalFormMatrix_eq (L : PositiveDefiniteIntegralLattice n)
    {G : Matrix (Fin n) (Fin n) ℚ} (hL : L.rationalFormMatrix = G) (p : ℕ) [Fact p.Prime] :
    (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) =
      G.map (algebraMap ℚ ℚ_[p]) := by
  subst hL
  ext i j
  simp [rationalFormMatrix]

/-- The value `M` read in `ℚ_p` through `ℤ_p` is its rational image. -/
theorem padicIntCast_intCast_eq_algebraMap (p : ℕ) [Fact p.Prime] (M : ℤ) :
    (((M : ℤ) : ℤ_[p]) : ℚ_[p]) = algebraMap ℚ ℚ_[p] ((M : ℤ) : ℚ) := by
  simp

/-- The local ratio for any matrix equal to the lattice Gram matrix, at any value equal to `M`. -/
theorem eventually_restrictedResidueCount_primePow_mul_glue_eq_of_eq (L : PositiveDefiniteIntegralLattice n)
    (M : ℤ) (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) {p : ℕ} [Fact p.Prime] (hpP : p ∈ P)
    (G : Matrix (Fin n) (Fin n) ℚ_[p])
    (hG : (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) = G)
    (value : ℚ_[p]) (hvalue : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) = value) (hM : value ≠ 0)
    (point : ℕ → Fin n → ℚ_[p]) (hpoint : ∀ i, G.toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((G.toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin n → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {w | G.toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (G.toQuadraticMap').padicSquareBranchAtlasRegion p point hpoint i) :
    ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) *
          (G.toQuadraticMap').padicSquareBranchAtlasGlue p point hpoint tH νs νv value
            {x | ‖x.1‖ ≤ 1} =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) *
          (G.toQuadraticMap').padicSquareBranchAtlasGlue p point hpoint tH νs νv value
            (Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) := by
  subst hG hvalue
  exact L.eventually_restrictedResidueCount_primePow_mul_glue_eq M P e R hP hpP hM point hpoint
    tH νs νv hcover

/-- The nonvanishing for any matrix equal to the lattice Gram matrix. -/
theorem eventually_fullResidueCount_primePow_ne_zero_of_eq (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    {p : ℕ} [Fact p.Prime] (G : Matrix (Fin n) (Fin n) ℚ_[p])
    (hG : (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) = G)
    (value : ℚ_[p]) (hvalue : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) = value) (hM : value ≠ 0)
    (point : ℕ → Fin n → ℚ_[p]) (hpoint : ∀ i, G.toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((G.toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin n → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {w | G.toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (G.toQuadraticMap').padicSquareBranchAtlasRegion p point hpoint i)
    (hg0 : (G.toQuadraticMap').padicSquareBranchAtlasGlue p point hpoint tH νs νv value
      {x | ‖x.1‖ ≤ 1} ≠ 0) :
    ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0 := by
  subst hG hvalue
  exact L.eventually_fullResidueCount_primePow_ne_zero M hM point hpoint tH νs νv hcover hg0

end PositiveDefiniteIntegralLattice

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime] {N : ℕ}

local instance obQPadicMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance obQPadicBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

/-- Carrying and carried glues agree across two atlases: if `T ∩ {Q = a} = O`, the first atlas
covers the nonisotropic vectors and the second covers the slice of `O`, then
`glue_a(T)` (first atlas) `= glue_a(O)` (second atlas), provided the slice of `O` is measurable. -/
theorem padicSquareBranchAtlasGlue_carrying_eq (form : QuadraticForm ℚ_[prime] (Fin N → ℚ_[prime]))
    (point : ℕ → Fin N → ℚ_[prime]) (hpoint : ∀ i, form (point i) ≠ 0)
    (tH : ∀ i, Measure (form.anisotropicOrthogonal (point i))) [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {w | form w ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (point' : ℕ → Fin N → ℚ_[prime]) (hpoint' : ∀ i, form (point' i) ≠ 0)
    (tH' : ∀ i, Measure (form.anisotropicOrthogonal (point' i))) [∀ i, (tH' i).IsAddHaarMeasure]
    (νs : Measure ℚ_[prime]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[prime]))
    [νv.IsAddHaarMeasure] {value : ℚ_[prime]} (hvalue : value ≠ 0)
    {T O : Set (Fin N → ℚ_[prime])} (hTO : T ∩ {w | form w = value} = O)
    (hO : MeasurableSet (Subtype.val ⁻¹' O : Set {w : Fin N → ℚ_[prime] // form w = value}))
    (hcov' : (Subtype.val ⁻¹' O : Set {w : Fin N → ℚ_[prime] // form w = value}) ⊆
      ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point' i) (hpoint' i) value)) :
    form.padicSquareBranchAtlasGlue prime point hpoint tH νs νv value (Subtype.val ⁻¹' T) =
      form.padicSquareBranchAtlasGlue prime point' hpoint' tH' νs νv value (Subtype.val ⁻¹' O) := by
  have hslice : (Subtype.val ⁻¹' T : Set {w : Fin N → ℚ_[prime] // form w = value}) =
      Subtype.val ⁻¹' O := by
    ext x
    simp only [mem_preimage]
    constructor
    · intro h
      rw [← hTO]
      exact ⟨h, x.2⟩
    · intro h
      rw [← hTO] at h
      exact h.1
  rw [hslice]
  refine form.padicSquareBranchAtlasGlue_apply_eq_of_cover prime point hpoint tH point' hpoint' tH'
    νs νv value hO ?_ hcov'
  intro y _
  have hy : y.1 ∈ {w | form w ≠ 0} := by
    change form y.1 ≠ 0
    rw [y.2]
    exact hvalue
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hy)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [form.range_padicSquareBranchFiberMap prime (point i) (hpoint i) value]
  exact hi

end QuadraticMap
