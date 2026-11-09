import SMSFormula.Product
import Mathlib.GroupTheory.Coset.Card
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Adelic measure lemmas

This module contains the measure-theoretic algebra used by the adelic
quotient-volume formalization.  It is split out of `SMSFormula.Adelic` so that
later finite-adelic and Schulze--Pillot declarations do not have to be checked
when only these generic map/comap, restriction, periodization, or scaled
pushforward lemmas change.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u
universe v
universe w

variable {n : ℕ}

open MeasureTheory
open scoped ENNReal

/-! ## A measure lemma for quotient-piece periodization -/

/-- Finite measure additivity over a measurable disjoint cover of the whole
space. -/
theorem measure_univ_eq_sum_of_fintype_iUnion_disjoint
    {X : Type u} {ι : Type v} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (s : ι → Set X)
    (hcover : (⋃ i, s i) = Set.univ)
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j))
    (hmeas : ∀ i, MeasurableSet (s i)) :
    μ Set.univ = ∑ i, μ (s i) := by
  calc
    μ Set.univ = μ (⋃ i, s i) := by
      rw [hcover]
    _ = ∑' i, μ (s i) := by
      exact measure_iUnion (fun i j hij => hdisj hij) hmeas
    _ = ∑ i, μ (s i) := by
      rw [tsum_fintype]

/-- If a nonnegative function is almost everywhere the constant `c` on a
measurable set `Y` and zero off `Y`, then an identity for its lintegral is the
same as the product identity `c * μ(Y) = m`.

This is the measure-theoretic algebra used after the
periodized-indicator count: a future Weil quotient-measure theorem supplies
`hInt`, while the already formal group count supplies `hP`. -/
theorem const_mul_measure_eq_of_lintegral_eq_of_ae_eq_indicator
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    {Y : Set X} (hY : MeasurableSet Y)
    {P : X → ℝ≥0∞} {c m : ℝ≥0∞}
    (hP : P =ᵐ[μ] Y.indicator (fun _ => c))
    (hInt : ∫⁻ x, P x ∂μ = m) :
    c * μ Y = m := by
  calc
    c * μ Y = ∫⁻ x, Y.indicator (fun _ => c) x ∂μ := by
      exact (lintegral_indicator_const (μ := μ) hY c).symm
    _ = ∫⁻ x, P x ∂μ := by
      exact (lintegral_congr_ae hP).symm
    _ = m := hInt

/-- If a piece measure maps to the ambient measure restricted to a measurable
piece, then integrating the restriction of an arbitrary ambient nonnegative
function over the piece is the same as integrating the piece indicator in the
ambient space.

This is the measure algebra needed to turn an actual
finite-adelic construction of the selected quotient-piece measure into the
function-specific restriction identity used by the compact-slice Weil
normalization. -/
theorem lintegral_map_eq_lintegral_indicator_of_map_eq_restrict
    {Y : Type u} {X : Type v} [MeasurableSpace Y] [MeasurableSpace X]
    (μY : Measure Y) (μX : Measure X) (i : Y → X) (s : Set X)
    (hi : MeasurableEmbedding i) (hs : MeasurableSet s)
    (hmap : Measure.map i μY = μX.restrict s) (f : X → ℝ≥0∞) :
    ∫⁻ y, f (i y) ∂μY = ∫⁻ x, s.indicator f x ∂μX := by
  calc
    ∫⁻ y, f (i y) ∂μY = ∫⁻ x, f x ∂Measure.map i μY := by
      exact (hi.lintegral_map f).symm
    _ = ∫⁻ x, f x ∂μX.restrict s := by
      rw [hmap]
    _ = ∫⁻ x, s.indicator f x ∂μX := by
      exact (lintegral_indicator (μ := μX) hs f).symm

/-- A comap construction of a piece measure gives the pushforward-restriction
identity used by `lintegral_map_eq_lintegral_indicator_of_map_eq_restrict`.

This isolates the standard quotient-piece measure construction: define the
piece measure as the comap of the ambient quotient measure along a measurable
embedding whose range is the selected piece. -/
theorem map_eq_restrict_of_eq_comap_of_measurableEmbedding
    {Y : Type u} {X : Type v} [MeasurableSpace Y] [MeasurableSpace X]
    (μY : Measure Y) (μX : Measure X) (i : Y → X) (s : Set X)
    (hi : MeasurableEmbedding i) (hrange : Set.range i = s)
    (hμ : μY = Measure.comap i μX) :
    Measure.map i μY = μX.restrict s := by
  calc
    Measure.map i μY = Measure.map i (Measure.comap i μX) := by
      rw [hμ]
    _ = μX.restrict (Set.range i) := by
      exact hi.map_comap μX
    _ = μX.restrict s := by
      rw [hrange]

/-- If the pushforward of a source measure is the ambient measure restricted to
the map range, then the ambient mass of that range is the source total mass. -/
theorem measure_range_eq_univ_of_map_eq_restrict
    {Y : Type u} {X : Type v} [MeasurableSpace Y] [MeasurableSpace X]
    (μY : Measure Y) (μX : Measure X) (i : Y → X)
    (hi : Measurable i)
    (hmap : Measure.map i μY = μX.restrict (Set.range i)) :
    μX (Set.range i) = μY Set.univ := by
  calc
    μX (Set.range i) =
        (μX.restrict (Set.range i)) Set.univ := by
      simp
    _ = (Measure.map i μY) Set.univ := by
      rw [← hmap]
    _ = μY (i ⁻¹' (Set.univ : Set X)) := by
      rw [Measure.map_apply hi MeasurableSet.univ]
    _ = μY Set.univ := by
      simp

/-- If the pushforward of a source measure is the ambient measure restricted
to the map range, then measurable source sets have the same source mass as
their ambient image mass. -/
theorem measure_apply_eq_image_of_map_eq_restrict
    {Y : Type u} {X : Type v} [MeasurableSpace Y] [MeasurableSpace X]
    (μY : Measure Y) (μX : Measure X) (i : Y → X)
    (hi : MeasurableEmbedding i)
    (hmap : Measure.map i μY = μX.restrict (Set.range i))
    {B : Set Y} (hB : MeasurableSet B) :
    μY B = μX (i '' B) := by
  have hBimage : MeasurableSet (i '' B) :=
    (hi.measurableSet_image).2 hB
  have hpre : i ⁻¹' (i '' B) = B := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy_eq : z = y := hi.injective hzy
      simpa [hzy_eq] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hmap_image :
      (Measure.map i μY) (i '' B) = μY B := by
    rw [Measure.map_apply hi.measurable hBimage, hpre]
  have himage_subset : i '' B ⊆ Set.range i := by
    rintro _ ⟨y, _hy, rfl⟩
    exact ⟨y, rfl⟩
  have hrestrict_image :
      (μX.restrict (Set.range i)) (i '' B) = μX (i '' B) := by
    rw [Measure.restrict_apply hBimage]
    congr 1
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, himage_subset hx⟩
  calc
    μY B = (Measure.map i μY) (i '' B) := hmap_image.symm
    _ = (μX.restrict (Set.range i)) (i '' B) := by rw [hmap]
    _ = μX (i '' B) := hrestrict_image

/-- Transporting the source measurable-space instance in `Measure.comap`
agrees with rebuilding the comap measure using the transported instance. -/
theorem measure_comap_congr_source_mspace
    {Y : Type u} {X : Type v}
    {mY₁ mY₂ : MeasurableSpace Y} [mX : MeasurableSpace X]
    (hm : mY₁ = mY₂) (i : Y → X) (μX : @Measure X mX) :
    (hm ▸ @Measure.comap Y X mY₁ mX i μX) =
      @Measure.comap Y X mY₂ mX i μX := by
  cases hm
  rfl

/-- If the source measurable space is the comap of the target measurable
space, then an injective map with measurable range is a measurable embedding.

This is the standard measurable-structure input for quotient-piece subtypes:
after choosing the piece measurable space as the pullback from the ambient
quotient and proving the fiber is measurable, no separate embedding theorem
is needed. -/
theorem measurableEmbedding_of_comap_eq_of_injective_of_measurableSet_range
    {Y : Type u} {X : Type v} [MeasurableSpace Y] [MeasurableSpace X]
    {i : Y → X} (hi : Function.Injective i)
    (hcomap :
      MeasurableSpace.comap i (inferInstance : MeasurableSpace X) =
        (inferInstance : MeasurableSpace Y))
    (hrange : MeasurableSet (Set.range i)) :
    MeasurableEmbedding i := by
  rw [MeasurableEmbedding.iff_comap_eq]
  exact ⟨hi, hcomap, hrange⟩

/-- The converse algebraic step to
`const_mul_measure_eq_of_lintegral_eq_of_ae_eq_indicator`: once a future
Weil slice theorem supplies `c * μ(Y) = m`, an almost-everywhere constant
periodized indicator integrates to `m`. -/
theorem lintegral_eq_of_ae_eq_indicator_of_const_mul_measure_eq
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    {Y : Set X} (hY : MeasurableSet Y)
    {P : X → ℝ≥0∞} {c m : ℝ≥0∞}
    (hP : P =ᵐ[μ] Y.indicator (fun _ => c))
    (hProd : c * μ Y = m) :
    ∫⁻ x, P x ∂μ = m := by
  calc
    ∫⁻ x, P x ∂μ = ∫⁻ x, Y.indicator (fun _ => c) x ∂μ := by
      exact lintegral_congr_ae hP
    _ = c * μ Y := by
      exact lintegral_indicator_const (μ := μ) hY c
    _ = m := hProd

/-- Measurable-set version of `const_mul_scaled_pushforward_measure_univ_eq`.
If a quotient-piece measure is `1 / c` times a pushforward, then the
product-form slice identity holds on every measurable target set. -/
theorem const_mul_scaled_pushforward_measure_apply
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (f : A → X)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞) (B : Set X) :
    c * ((c⁻¹ • Measure.map f μA) B) = (Measure.map f μA) B := by
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]
  calc
    c * (c⁻¹ * Measure.map f μA B) =
        (c * c⁻¹) * Measure.map f μA B := by
      rw [mul_assoc]
    _ = 1 * Measure.map f μA B := by
      rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = Measure.map f μA B := by
      simp

theorem const_mul_scaled_pushforward_measure_apply_eq_preimage
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (f : A → X) (hf : Measurable f)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    {B : Set X} (hB : MeasurableSet B) :
    c * ((c⁻¹ • Measure.map f μA) B) = μA (f ⁻¹' B) := by
  rw [const_mul_scaled_pushforward_measure_apply μA f (c := c) hc0 hctop B]
  exact Measure.map_apply hf hB

/-- Converse to the scaled-pushforward slice identity.

If a measure `μX` on a target is characterized on every measurable set by
`c * μX(B) = μA(f ⁻¹' B)`, then `μX` is the `1 / c`-scaled pushforward of
`μA` along `f`.  This is the measure algebra needed when a future
Weil quotient theorem supplies the finite-slice formula directly rather than a
measure equality. -/
theorem measure_eq_scaled_pushforward_of_const_mul_apply_eq_preimage
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (μX : Measure X) (f : A → X) (hf : Measurable f)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hslice : ∀ ⦃B : Set X⦄, MeasurableSet B → c * μX B = μA (f ⁻¹' B)) :
    μX = c⁻¹ • Measure.map f μA := by
  ext B hB
  have hsliceB : c * μX B = μA (f ⁻¹' B) := hslice hB
  calc
    μX B = 1 * μX B := by simp
    _ = (c⁻¹ * c) * μX B := by
      rw [mul_comm c⁻¹ c, ENNReal.mul_inv_cancel hc0 hctop]
    _ = c⁻¹ * (c * μX B) := by
      rw [mul_assoc]
    _ = c⁻¹ * μA (f ⁻¹' B) := by
      rw [hsliceB]
    _ = c⁻¹ * (Measure.map f μA) B := by
      rw [Measure.map_apply hf hB]
    _ = (c⁻¹ • Measure.map f μA) B := by
      rw [Measure.smul_apply]
      rfl

/-- A setwise slice formula on a measurable target piece identifies the
restricted target measure with the corresponding scaled pushforward.

This is the last abstract measure step in the one-piece Weil quotient plan:
after a future Weil-periodization theorem proves the formula on every
measurable `B ⊆ Y`, the selected-piece restricted measure is exactly the
finite-stabilizer-scaled pushforward of the Haar slice. -/
theorem restrict_measure_eq_scaled_map_of_apply_eq_preimage_on_piece
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (μX : Measure X) (f : A → X) (Y : Set X)
    (hf : Measurable f) (hY : MeasurableSet Y)
    {c : ℝ≥0∞} (hfY : ∀ a : A, f a ∈ Y)
    (hformula : ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
      μX B = c⁻¹ * μA (f ⁻¹' B)) :
    μX.restrict Y = c⁻¹ • Measure.map f μA := by
  ext E hE
  rw [Measure.restrict_apply hE]
  have hEY : MeasurableSet (E ∩ Y) := hE.inter hY
  have hsub : E ∩ Y ⊆ Y := Set.inter_subset_right
  rw [hformula hEY hsub]
  have hpre : f ⁻¹' (E ∩ Y) = f ⁻¹' E := by
    ext a
    constructor
    · intro ha
      exact ha.1
    · intro ha
      exact ⟨ha, hfY a⟩
  rw [hpre, Measure.smul_apply, Measure.map_apply hf hE]
  rfl

/-- Periodized-indicator form of
`restrict_measure_eq_scaled_map_of_apply_eq_preimage_on_piece`.

This is the measure algebra closest to the remaining Weil quotient-measure
input: if the periodized indicator `P` is almost everywhere the constant `c`
on every measurable subset of the selected piece `Y`, and Weil's formula
identifies its integral over each such subset with the Haar preimage under the
orbit map, then the restricted quotient measure on `Y` is the
finite-stabilizer-scaled pushforward of the Haar slice. -/
theorem restrict_measure_eq_scaled_map_of_periodized_lintegral_on_piece
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (μX : Measure X) (f : A → X) (Y : Set X)
    (hf : Measurable f) (hY : MeasurableSet Y)
    {P : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hfY : ∀ a : A, f a ∈ Y)
    (hP_const :
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
        B.indicator P =ᵐ[μX] B.indicator (fun _ => c))
    (hWeil :
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
        ∫⁻ x, B.indicator P x ∂μX = μA (f ⁻¹' B)) :
    μX.restrict Y = c⁻¹ • Measure.map f μA := by
  refine
    restrict_measure_eq_scaled_map_of_apply_eq_preimage_on_piece
      (μA := μA) (μX := μX) (f := f) (Y := Y) hf hY hfY ?_
  intro B hB hsub
  have hprod : c * μX B = μA (f ⁻¹' B) := by
    calc
      c * μX B = ∫⁻ x, B.indicator (fun _ : X => c) x ∂μX := by
        exact (lintegral_indicator_const (μ := μX) hB c).symm
      _ = ∫⁻ x, B.indicator P x ∂μX := by
        exact (lintegral_congr_ae (hP_const hB hsub)).symm
      _ = μA (f ⁻¹' B) := hWeil hB hsub
  calc
    μX B = 1 * μX B := by simp
    _ = (c⁻¹ * c) * μX B := by
      rw [mul_comm c⁻¹ c, ENNReal.mul_inv_cancel hc0 hctop]
    _ = c⁻¹ * (c * μX B) := by
      rw [mul_assoc]
    _ = c⁻¹ * μA (f ⁻¹' B) := by
      rw [hprod]

/-- Slice-preimage form of the periodized-integral input.

This is the algebra suggested by the standard Weil quotient
formula.  Instead of assuming directly that the selected-piece periodized
indicator integrates to the Haar measure of the orbit preimage, it is enough
to know the Weil formula for the ambient slice
`S ∩ q ⁻¹' B`, the pointwise rewrite of that periodization as
`B.indicator P`, and the compatibility of the Haar slice measure with the
same preimage. -/
theorem lintegral_indicator_eq_preimage_measure_of_weil_slice_periodization
    {A : Type u} {G : Type v} {X : Type w}
    [MeasurableSpace A] [MeasurableSpace G] [MeasurableSpace X]
    (μA : Measure A) (μG : Measure G) (μX : Measure X)
    (f : A → X) (q : G → X) (S : Set G)
    (Periodize : Set G → X → ℝ≥0∞) (P : X → ℝ≥0∞)
    {B : Set X}
    (hperiodize :
      Periodize (S ∩ q ⁻¹' B) =ᵐ[μX] B.indicator P)
    (hWeil :
      ∫⁻ x, Periodize (S ∩ q ⁻¹' B) x ∂μX =
        μG (S ∩ q ⁻¹' B))
    (hslice :
      μA (f ⁻¹' B) = μG (S ∩ q ⁻¹' B)) :
    ∫⁻ x, B.indicator P x ∂μX = μA (f ⁻¹' B) := by
  calc
    ∫⁻ x, B.indicator P x ∂μX =
        ∫⁻ x, Periodize (S ∩ q ⁻¹' B) x ∂μX := by
      exact (lintegral_congr_ae hperiodize).symm
    _ = μG (S ∩ q ⁻¹' B) := hWeil
    _ = μA (f ⁻¹' B) := hslice.symm

/-- Slice-preimage form of
`restrict_measure_eq_scaled_map_of_periodized_lintegral_on_piece`.

For a future concrete quotient presentation, the remaining measure input can
now be stated as the standard Weil periodization formula for the ambient sets
`S ∩ q ⁻¹' B`, plus the compatibility between the selected Haar measure and
those slice preimages.  Lean derives the restricted scaled-pushforward measure
identity from these smaller inputs. -/
theorem restrict_measure_eq_scaled_map_of_weil_slice_periodization_on_piece
    {A : Type u} {G : Type v} {X : Type w}
    [MeasurableSpace A] [MeasurableSpace G] [MeasurableSpace X]
    (μA : Measure A) (μG : Measure G) (μX : Measure X)
    (f : A → X) (q : G → X) (S : Set G) (Y : Set X)
    (hf : Measurable f) (hY : MeasurableSet Y)
    {P : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hfY : ∀ a : A, f a ∈ Y)
    (Periodize : Set G → X → ℝ≥0∞)
    (hP_const :
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
        B.indicator P =ᵐ[μX] B.indicator (fun _ => c))
    (hperiodize :
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
        Periodize (S ∩ q ⁻¹' B) =ᵐ[μX] B.indicator P)
    (hWeil :
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
        ∫⁻ x, Periodize (S ∩ q ⁻¹' B) x ∂μX =
          μG (S ∩ q ⁻¹' B))
    (hslice :
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ Y →
        μA (f ⁻¹' B) = μG (S ∩ q ⁻¹' B)) :
    μX.restrict Y = c⁻¹ • Measure.map f μA := by
  refine
    restrict_measure_eq_scaled_map_of_periodized_lintegral_on_piece
      (μA := μA) (μX := μX) (f := f) (Y := Y) hf hY
      (P := P) (c := c) hc0 hctop hfY ?_ ?_
  · intro B hB hsub
    exact hP_const hB hsub
  · intro B hB hsub
    exact
      lintegral_indicator_eq_preimage_measure_of_weil_slice_periodization
        (μA := μA) (μG := μG) (μX := μX) (f := f) (q := q)
        (S := S) (Periodize := Periodize) (P := P)
        (hperiodize hB hsub) (hWeil hB hsub) (hslice hB hsub)

/-- Transporting a scaled pushforward across a measurable map composes the
underlying orbit map.

This is the generic measure algebra needed when a concrete quotient-measure
construction first builds a measure on an intermediate quotient and then
identifies that quotient with the selected adelic piece. -/
theorem scaled_pushforward_measure_map_comp
    {A : Type u} {Q : Type v} {X : Type w}
    [MeasurableSpace A] [MeasurableSpace Q] [MeasurableSpace X]
    (μA : Measure A) (q : A → Q) (e : Q → X)
    (hq : Measurable q) (he : Measurable e) {c : ℝ≥0∞} :
    Measure.map e (c⁻¹ • Measure.map q μA) =
      c⁻¹ • Measure.map (fun a => e (q a)) μA := by
  rw [Measure.map_smul]
  rw [Measure.map_map he hq]
  rfl

/-- If a quotient-piece measure is defined as `1 / c` times the pushforward of
an ambient slice measure, then the product-form slice identity follows from
the total mass of the ambient slice.

This is the measure algebra behind the intended Weil quotient
construction: a future concrete finite-adelic presentation can prove the
selected piece measure is the scaled pushforward of Haar measure on `H_f`, and
then use this lemma to obtain the `c * μ(X_g) = μ(H_f)` slice formula. -/
theorem const_mul_scaled_pushforward_measure_univ_eq
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (f : A → X) (hf : Measurable f)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    c * ((c⁻¹ • Measure.map f μA) Set.univ) = μA Set.univ := by
  calc
    c * ((c⁻¹ • Measure.map f μA) Set.univ) =
        (Measure.map f μA) Set.univ := by
      exact const_mul_scaled_pushforward_measure_apply μA f (c := c) hc0 hctop Set.univ
    _ = μA Set.univ := by
      rw [Measure.map_apply hf MeasurableSet.univ]
      simp

/-- Total-mass form of a scaled pushforward by a positive finite stabilizer
cardinality.

This is the `ℝ≥0∞` bookkeeping needed by a concrete Weil quotient-measure
construction: once the selected quotient-piece measure is defined as
`1 / c` times the pushforward of a Haar slice and the Haar slice has real
total mass `M`, the selected piece has total mass `M / c`. -/
theorem scaled_pushforward_measure_univ_eq_ofReal_div_nat
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (f : A → X) (hf : Measurable f)
    {c : ℕ} (hc : 0 < c) {M : ℝ}
    (hμA : μA Set.univ = ENNReal.ofReal M) :
    (((c : ℝ≥0∞)⁻¹ • Measure.map f μA) Set.univ) =
      ENNReal.ofReal (M / (c : ℝ)) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  calc
    (((c : ℝ≥0∞)⁻¹ • Measure.map f μA) Set.univ) =
        (c : ℝ≥0∞)⁻¹ * μA Set.univ := by
          rw [Measure.smul_apply, Measure.map_apply hf MeasurableSet.univ]
          simp
    _ = (c : ℝ≥0∞)⁻¹ * ENNReal.ofReal M := by
          rw [hμA]
    _ = ENNReal.ofReal M * (c : ℝ≥0∞)⁻¹ := by
          rw [mul_comm]
    _ = ENNReal.ofReal M / ENNReal.ofReal (c : ℝ) := by
          rw [ENNReal.ofReal_natCast]
          rfl
    _ = ENNReal.ofReal (M / (c : ℝ)) := by
          exact (ENNReal.ofReal_div_of_pos (x := M) hcR).symm

/-- Normalized total-mass form of a scaled pushforward by a positive finite
stabilizer cardinality.

This is the common `μ(A)=1` specialization used by canonical finite quotient
presentations whose selected quotient-piece measure is the stabilizer-scaled
pushforward of a normalized Haar slice. -/
theorem scaled_pushforward_measure_univ_eq_ofReal_inv_nat
    {A : Type u} {X : Type v} [MeasurableSpace A] [MeasurableSpace X]
    (μA : Measure A) (f : A → X) (hf : Measurable f)
    {c : ℕ} (hc : 0 < c)
    (hμA : μA Set.univ = ENNReal.ofReal 1) :
    (((c : ℝ≥0∞)⁻¹ • Measure.map f μA) Set.univ) =
      ENNReal.ofReal ((c : ℝ)⁻¹) := by
  simpa [one_div] using
    scaled_pushforward_measure_univ_eq_ofReal_div_nat μA f hf hc hμA

end PositiveDefiniteIntegralLattice

end
