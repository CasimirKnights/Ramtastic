/-
  CompactGroupProduct.lean — Phase 2 (B.1) PRODUCT HAAR + LATTICE GAUGE MEASURE.

  Real content (per REQ-S-1 / §10.7 proper density). The product Haar
  measure on `Fin n → G` is built via Mathlib's `MeasureTheory.Measure.pi`;
  if each `G_i` carries a probability measure, the product is automatically
  a probability measure (Mathlib `Measure.pi.instIsProbabilityMeasure`).

  Per spec §10.10:
    B.1.a — single-group Haar (Mathlib reference + IsProbabilityMeasure
            assumption for compact G).
    B.1.b — product Haar measure on `Fin n → G` via `Measure.pi`.
    B.1.b' — product is a probability measure (Mathlib auto-derived).
    B.1.d — lattice gauge measure μ_W = exp(-S_W)/Z · Haar^nLinks.
            (Density definition; absolute continuity; normalization.)

  At Phase 2 chassis level: the actual product-Haar construction lives.
  μ_W is built as `Haar^n` weighted by a non-negative measurable density
  (from Phase 4's Wilson action), normalized by Z = ∫ density d(Haar^n).

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.7, 2026-05-01)
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Ramtastic.QuantumYM.WilsonActionConstruction

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.QuantumYM.CompactGroupProduct

open MeasureTheory

noncomputable section

-- ════════════════════════════════════════════════════════════════
-- B.1.a / B.1.b — product Haar on `Fin n → G` via Mathlib `Measure.pi`
-- ════════════════════════════════════════════════════════════════

/-- **B.1.b — product probability measure on `Fin n → G`.**

    Given a probability measure `μ_G : Measure G` on a measurable space `G`,
    the product `MeasureTheory.Measure.pi (fun (_ : Fin n) => μ_G)` is the
    product probability measure on `Fin n → G`.

    Citation: Mathlib `MeasureTheory.Constructions.Pi` (`Measure.pi`,
    `pi.instIsProbabilityMeasure`); Folland 1999 "Real Analysis" §11.1
    (product measures, σ-finite case).

    For Wilson lattice gauge theory, `μ_G` is the Haar probability measure
    on the compact gauge group G (Mathlib `MeasureTheory.Measure.Haar.Basic`
    provides this; it is automatically a probability measure since G is
    compact). -/
def productHaar
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) :
    Measure (Fin n → G) :=
  MeasureTheory.Measure.pi (fun (_ : Fin n) => μ_G)

/-- The product Haar is a probability measure. Direct via Mathlib's
    auto-derived instance `pi.instIsProbabilityMeasure`. -/
instance productHaar_isProbability
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) :
    IsProbabilityMeasure (productHaar μ_G n) := by
  unfold productHaar
  infer_instance

-- ════════════════════════════════════════════════════════════════
-- B.1.d — lattice gauge measure μ_W via density × product Haar
-- ════════════════════════════════════════════════════════════════

/-- **B.1.d — lattice gauge measure `μ_W` from a non-negative density.**

    Given:
    - probability Haar `μ_G` on the gauge group `G`,
    - non-negative measurable density `ρ : (Fin n → G) → ENNReal`
      (the polynomial mechanism's choice: `ρ U = ENNReal.ofReal (Real.exp (-S_W U))`),
    - `Z = ∫ ρ d(productHaar μ_G n)` (the partition function),
    - `Z_pos : 0 < Z` (positivity of the partition function),
    - `Z_ne_top : Z ≠ ⊤` (finiteness, automatic since `ρ ≤ 1` if `S_W ≥ 0`),

    construct `μ_W = (1/Z) · (ρ · productHaar μ_G n)`. This is a probability
    measure on `Fin n → G`.

    Citation: Mathlib `MeasureTheory.Measure.withDensity` for the
    density-times-measure construction; `Measure.smul` for normalization. -/
def latticeGaugeMeasure
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (ρ : (Fin n → G) → ENNReal) (Z_inv : ENNReal) :
    Measure (Fin n → G) :=
  Z_inv • ((productHaar μ_G n).withDensity ρ)

/-- **B.1.d.iii — `μ_W` is a finite measure when `ρ ≤ 1` and `Z ≠ 0`.** -/
theorem latticeGaugeMeasure_isFiniteMeasure
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (ρ : (Fin n → G) → ENNReal)
    (h_meas : Measurable ρ)
    (h_bound : ∀ U, ρ U ≤ 1)
    (Z_inv : ENNReal) (h_Z_inv_lt_top : Z_inv < ⊤) :
    IsFiniteMeasure (latticeGaugeMeasure μ_G n ρ Z_inv) := by
  unfold latticeGaugeMeasure
  -- The withDensity-by-bounded-measurable-ρ of a probability measure is
  -- bounded by 1; scalar multiplication by a finite scalar preserves finiteness.
  refine ⟨?_⟩
  rw [Measure.smul_apply]
  apply ENNReal.mul_lt_top h_Z_inv_lt_top
  rw [withDensity_apply _ MeasurableSet.univ]
  -- Goal: `∫⁻ U in univ, ρ U ∂(productHaar μ_G n) < ⊤`
  -- Since `ρ ≤ 1` and `productHaar` is probability, `∫⁻ ρ ≤ 1 < ⊤`.
  -- Convert from `setLIntegral` to `lintegral` over univ (they coincide).
  rw [Measure.restrict_univ]
  calc (∫⁻ U, ρ U ∂(productHaar μ_G n))
      ≤ ∫⁻ _, (1 : ENNReal) ∂(productHaar μ_G n) :=
          MeasureTheory.lintegral_mono (fun U => h_bound U)
    _ = (productHaar μ_G n) Set.univ := by simp
    _ < ⊤ := lt_top_iff_ne_top.mpr (measure_ne_top _ _)

-- ════════════════════════════════════════════════════════════════
-- B.1.a.i — canonical Haar probability measure on compact G
-- ════════════════════════════════════════════════════════════════

/-- **B.1.a.i — canonical Haar probability measure on compact G.**

    Mathlib's `MeasureTheory.Measure.haarMeasure` is parameterized by a
    choice of `PositiveCompacts G` (a compact set with nonempty interior),
    and is normalized so that `haarMeasure K₀ K₀ = 1`. For a `CompactSpace G`,
    `K₀ = ⟨⟨univ, isCompact_univ⟩, ...⟩` is a `PositiveCompacts G`, and the
    resulting measure satisfies `haarMeasure ⟨univ,..⟩ univ = 1` —
    a probability measure.

    Citation: Mathlib `MeasureTheory.Measure.Haar.Basic` (`haarMeasure`,
    `haarMeasure_self`); Hewitt-Ross 1970 Vol I Thm 15.5 (Haar measure on
    locally compact groups, normalized to probability for compact). -/
noncomputable def haar_G
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    Measure G :=
  MeasureTheory.Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- `haar_G` is a probability measure: `haar_G G univ = 1` follows
    from `haarMeasure_self` since `K₀.carrier = univ`. -/
instance haar_G_isProbability
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (haar_G G) := by
  unfold haar_G
  refine ⟨?_⟩
  exact MeasureTheory.Measure.haarMeasure_self

/-- `haar_G` is left-translation-invariant — Mathlib's
    `isMulLeftInvariant_haarMeasure`. -/
instance haar_G_isMulLeftInvariant
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    (haar_G G).IsMulLeftInvariant := by
  unfold haar_G
  infer_instance

/-- `haar_G` is a Haar measure. -/
instance haar_G_isHaarMeasure
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    Measure.IsHaarMeasure (haar_G G) := by
  unfold haar_G
  infer_instance

/-- Compact normalized Haar is right-translation-invariant. -/
instance haar_G_isMulRightInvariant
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    (haar_G G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hprob :
        IsProbabilityMeasure
          (Measure.map (fun x : G => x * g) (haar_G G)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hhaar :
        Measure.IsHaarMeasure (Measure.map (fun x : G => x * g) (haar_G G)) := by
      infer_instance
    have heq :
        Measure.map (fun x : G => x * g) (haar_G G) = haar_G G :=
      Measure.isHaarMeasure_eq_of_isProbabilityMeasure
        (Measure.map (fun x : G => x * g) (haar_G G)) (haar_G G)
    exact heq

-- ════════════════════════════════════════════════════════════════
-- B.1.b.i — product Haar on `Fin n → G` via `haar_G`
-- ════════════════════════════════════════════════════════════════

/-- **B.1.b.i — concrete product Haar measure on `Fin n → G`** for
    compact G, via `Measure.pi (fun _ => haar_G G)`.

    Specialization of the abstract `productHaar` (which takes any
    probability measure) at the canonical `haar_G G` from B.1.a.i.

    Citation: Mathlib `MeasureTheory.Constructions.Pi` for `Measure.pi`;
    B.1.a.i for `haar_G`. -/
noncomputable def haarProduct
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) : Measure (Fin n → G) :=
  productHaar (haar_G G) n

/-- The `haarProduct` is a probability measure on `Fin n → G`. -/
instance haarProduct_isProbability
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) : IsProbabilityMeasure (haarProduct G n) := by
  unfold haarProduct
  infer_instance

-- ════════════════════════════════════════════════════════════════
-- B.1.b.ii — `haarProduct` invariant under coordinate-wise left mult
-- ════════════════════════════════════════════════════════════════

/-- **Coordinate-wise left-multiplication** at link `i` by group element `g`. -/
def link_mult {G : Type*} [Mul G] {n : ℕ} (i : Fin n) (g : G) :
    (Fin n → G) → (Fin n → G) :=
  fun U j => if j = i then g * U j else U j

/-- `link_mult` is measurable. -/
theorem link_mult_measurable
    {G : Type*} [TopologicalSpace G] [Mul G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] {n : ℕ} (i : Fin n) (g : G) :
    Measurable (link_mult (G := G) (n := n) i g) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j = i
  · have h1 : (fun U : Fin n → G => link_mult i g U j) = (fun U => g * U j) := by
      funext U; simp [link_mult, h]
    rw [h1]
    have hmul : Measurable (fun y : G => g * y) := measurable_const_mul g
    exact hmul.comp (measurable_pi_apply j)
  · have h2 : (fun U : Fin n → G => link_mult i g U j) = (fun U => U j) := by
      funext U; simp [link_mult, h]
    rw [h2]
    exact measurable_pi_apply j

/-- **B.1.b.ii — `haarProduct` is invariant under coordinate-wise left
    multiplication by a fixed group element at a fixed link.**

    Proof: factor `link_mult i g` as the componentwise map
    `fun j => if j = i then (g * ·) else id` and apply Mathlib's
    `Measure.pi_map_pi`. Each per-component pushforward equals `haar_G G`:
    at `j = i` by `map_mul_left_eq_self` (Mathlib left-invariance of Haar),
    at `j ≠ i` by `Measure.map_id`. -/
theorem haarProduct_left_invariant_link
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) (i : Fin n) (g : G) :
    (haarProduct G n).map (link_mult i g) = haarProduct G n := by
  unfold haarProduct productHaar link_mult
  -- Rewrite the action as componentwise.
  have h_componentwise :
      (fun (U : Fin n → G) (j : Fin n) =>
          if j = i then g * U j else U j) =
      (fun (U : Fin n → G) (j : Fin n) =>
          (fun (k : Fin n) (x : G) => if k = i then g * x else x) j (U j)) := by
    funext U j
    by_cases h : j = i
    · simp [h]
    · simp [h]
  rw [h_componentwise]
  -- Apply pi_map_pi: pushforward of pi-measure under componentwise map
  -- equals pi-measure of pushforwards.
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => haar_G G)
        (f := fun (k : Fin n) (x : G) => if k = i then g * x else x)
        (fun k => by
          by_cases h : k = i
          · simp [h]
            exact (measurable_const_mul g).aemeasurable
          · simp [h]
            exact aemeasurable_id)]
  -- Goal: Measure.pi (fun j => (haar_G G).map (...)) = Measure.pi (fun _ => haar_G G)
  congr 1
  funext j
  by_cases h : j = i
  · simp only [h, if_true]
    exact map_mul_left_eq_self (haar_G G) g
  · simp only [h, if_false]
    exact Measure.map_id

-- ════════════════════════════════════════════════════════════════
-- B.1.c.i — Wilson action non-negativity (re-expose existing)
-- ════════════════════════════════════════════════════════════════

/-- **B.1.c.i — Wilson action non-negativity.**

    Re-exposes `Ramtastic.QuantumYM.WilsonActionConstruction.wilsonAction_nonneg`
    at this Phase 2 file for use in Phase 2 B.1.d (Boltzmann density bounded
    by 1) and Phase 4. Existing TASK 4 deliverable.

    Citation: Wilson 1974 *Phys Rev D* 10, 2445 (lattice action non-negativity
    from `|tr(U_□)| ≤ N` for `U_□` in a compact subgroup of `U(N)`). -/
theorem wilsonAction_nonneg_reexposed
    (β : ℝ) (N : ℕ) (nPlaq : ℕ) (reTrUOfPlaq : Fin nPlaq → ℝ)
    (hβ : 0 ≤ β) (hN : 0 < N)
    (h_bounds : ∀ i, reTrUOfPlaq i ≤ (N : ℝ)) :
    0 ≤ Ramtastic.QuantumYM.WilsonActionConstruction.wilsonAction
          β N nPlaq reTrUOfPlaq :=
  Ramtastic.QuantumYM.WilsonActionConstruction.wilsonAction_nonneg
    β N nPlaq reTrUOfPlaq hβ hN h_bounds

-- ════════════════════════════════════════════════════════════════
-- B.1.d.i — Boltzmann weight integrability
-- ════════════════════════════════════════════════════════════════

/-- **B.1.d.i — Boltzmann integrability.**

    For any measurable non-negative `S_W : (Fin n → G) → ℝ`, the function
    `U ↦ exp(-S_W U)` is integrable against the product Haar (probability)
    measure: `0 < exp(-S_W) ≤ 1` pointwise, and bounded measurable functions
    on a probability space are integrable. -/
theorem boltzmann_integrable
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ)
    (hS_meas : Measurable S_W) (hS_nonneg : ∀ U, 0 ≤ S_W U) :
    Integrable (fun U => Real.exp (-(S_W U))) (productHaar μ_G n) := by
  have h_meas : Measurable (fun U => Real.exp (-(S_W U))) :=
    Real.measurable_exp.comp hS_meas.neg
  refine Integrable.mono' (g := fun _ => (1 : ℝ))
    (integrable_const 1) h_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro U
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hS_nonneg U))

-- ════════════════════════════════════════════════════════════════
-- B.1.d.ii — partition function Z
-- ════════════════════════════════════════════════════════════════

/-- **B.1.d.ii — partition function `Z`.** -/
def Z {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ) : ℝ :=
  ∫ U, Real.exp (-(S_W U)) ∂(productHaar μ_G n)

/-- `Z` is bounded above by 1: `exp(-S_W) ≤ 1` pointwise and `productHaar`
    is a probability measure. -/
theorem Z_le_one
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ)
    (hS_meas : Measurable S_W) (hS_nonneg : ∀ U, 0 ≤ S_W U) :
    Z μ_G n S_W ≤ 1 := by
  unfold Z
  calc (∫ U, Real.exp (-(S_W U)) ∂(productHaar μ_G n))
      ≤ ∫ _, (1 : ℝ) ∂(productHaar μ_G n) := by
        refine integral_mono
          (boltzmann_integrable μ_G n S_W hS_meas hS_nonneg)
          (integrable_const 1) (fun U => ?_)
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hS_nonneg U))
    _ = 1 := by simp

/-- `Z > 0` whenever `S_W` is bounded above. The integral of a strictly
    positive bounded function over a probability measure is at least
    `exp(-sup) > 0`. -/
theorem Z_pos_of_bounded
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ)
    (hS_meas : Measurable S_W) (hS_nonneg : ∀ U, 0 ≤ S_W U)
    (M : ℝ) (hM : ∀ U, S_W U ≤ M) :
    0 < Z μ_G n S_W := by
  unfold Z
  have h_pointwise : ∀ U, Real.exp (-M) ≤ Real.exp (-(S_W U)) := by
    intro U
    exact Real.exp_le_exp.mpr (neg_le_neg (hM U))
  have h_lb : Real.exp (-M) ≤ ∫ U, Real.exp (-(S_W U)) ∂(productHaar μ_G n) := by
    calc Real.exp (-M)
        = ∫ _, Real.exp (-M) ∂(productHaar μ_G n) := by simp
      _ ≤ ∫ U, Real.exp (-(S_W U)) ∂(productHaar μ_G n) := by
        refine integral_mono (integrable_const _)
          (boltzmann_integrable μ_G n S_W hS_meas hS_nonneg) ?_
        intro U; exact h_pointwise U
  exact lt_of_lt_of_le (Real.exp_pos _) h_lb

-- ════════════════════════════════════════════════════════════════
-- B.1.d.iii — μ_W as a probability measure
-- ════════════════════════════════════════════════════════════════

/-- **Boltzmann density** `U ↦ ENNReal.ofReal (exp(-S_W U))`. -/
noncomputable def boltzmann_density
    {G : Type*} {n : ℕ} (S_W : (Fin n → G) → ℝ) :
    (Fin n → G) → ENNReal :=
  fun U => ENNReal.ofReal (Real.exp (-(S_W U)))

/-- **B.1.d.iii — Wilson lattice gauge measure `μ_W`.**

    `μ_W = (ofReal Z)⁻¹ • productHaar.withDensity boltzmann_density`. -/
noncomputable def μ_W
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ) :
    Measure (Fin n → G) :=
  latticeGaugeMeasure μ_G n (boltzmann_density S_W)
    (ENNReal.ofReal (Z μ_G n S_W))⁻¹

/-- The Boltzmann density is measurable when `S_W` is. -/
theorem boltzmann_density_measurable
    {G : Type*} [MeasurableSpace G] {n : ℕ}
    (S_W : (Fin n → G) → ℝ) (hS_meas : Measurable S_W) :
    Measurable (boltzmann_density S_W) := by
  unfold boltzmann_density
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hS_meas.neg)

/-- The Boltzmann density is bounded above by `1` when `S_W ≥ 0`. -/
theorem boltzmann_density_le_one
    {G : Type*} {n : ℕ}
    (S_W : (Fin n → G) → ℝ) (hS_nonneg : ∀ U, 0 ≤ S_W U) :
    ∀ U, boltzmann_density S_W U ≤ 1 := by
  intro U
  unfold boltzmann_density
  rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hS_nonneg U)))

/-- **`μ_W` is a probability measure** when `S_W` is measurable, non-negative,
    and bounded above (so `Z > 0`). -/
theorem μ_W_isProbability
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ)
    (hS_meas : Measurable S_W) (hS_nonneg : ∀ U, 0 ≤ S_W U)
    (M : ℝ) (hM : ∀ U, S_W U ≤ M) :
    IsProbabilityMeasure (μ_W μ_G n S_W) := by
  unfold μ_W latticeGaugeMeasure
  have hZ_pos : 0 < Z μ_G n S_W := Z_pos_of_bounded μ_G n S_W hS_meas hS_nonneg M hM
  have hZ_le : Z μ_G n S_W ≤ 1 := Z_le_one μ_G n S_W hS_meas hS_nonneg
  have hofReal_Z_pos : (0 : ENNReal) < ENNReal.ofReal (Z μ_G n S_W) :=
    ENNReal.ofReal_pos.mpr hZ_pos
  have hofReal_Z_ne_top : ENNReal.ofReal (Z μ_G n S_W) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Compute (productHaar).withDensity boltzmann_density of univ.
  have h_withDensity_univ :
      (productHaar μ_G n).withDensity (boltzmann_density S_W) Set.univ =
      ENNReal.ofReal (Z μ_G n S_W) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    -- ∫⁻ U, ENNReal.ofReal (exp(-S_W U)) ∂productHaar = ENNReal.ofReal Z
    unfold boltzmann_density Z
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (boltzmann_integrable μ_G n S_W hS_meas hS_nonneg)
          (Filter.Eventually.of_forall (fun U => (Real.exp_pos _).le))]
  refine ⟨?_⟩
  rw [Measure.smul_apply, h_withDensity_univ]
  rw [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hofReal_Z_pos.ne' hofReal_Z_ne_top

/-- For the zero Wilson action, the normalized Wilson lattice gauge measure
    is exactly product Haar.  This is the analytic normalization fact needed
    before finite-volume coordinate projections can be used as genuine
    product-Haar marginal maps. -/
theorem μ_W_zero_action_eq_productHaar
    {G : Type*} [MeasurableSpace G]
    (μ_G : Measure G) [IsProbabilityMeasure μ_G]
    (n : ℕ) :
    μ_W μ_G n (fun _ : Fin n → G => 0) = productHaar μ_G n := by
  unfold μ_W latticeGaugeMeasure boltzmann_density Z
  simp

-- ════════════════════════════════════════════════════════════════
-- B.1.d.iv — gauge invariance of μ_W
-- ════════════════════════════════════════════════════════════════

/-- **B.1.d.iv — `μ_W` is invariant under coordinate-wise left multiplication
    when `S_W` is gauge-invariant.**

    Hypothesis `hS_inv`: `S_W (link_mult i g U) = S_W U` for all (i, g, U).
    This is a structural property of the Wilson action (each plaquette
    product is conjugation-invariant under `U_i ↦ g · U_i · g⁻¹` because
    the trace is conjugation-invariant; and left-multiplication at a single
    link likewise preserves the trace via gauge symmetry of `S_W`).

    Proof outline: `μ_W = c⁻¹ • haarProduct.withDensity ρ`. `Measure.map`
    commutes with scalar multiplication. The pushforward of `withDensity`
    by a measure-preserving map (B.1.b.ii) with a gauge-invariant density
    (from `hS_inv`) returns the original `withDensity`. -/
theorem μ_W_gauge_invariant
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) (S_W : (Fin n → G) → ℝ)
    (hS_meas : Measurable S_W)
    (hS_inv : ∀ (i : Fin n) (g : G) (U : Fin n → G),
              S_W (link_mult i g U) = S_W U)
    (i : Fin n) (g : G) :
    (μ_W (haar_G G) n S_W).map (link_mult i g) = μ_W (haar_G G) n S_W := by
  unfold μ_W latticeGaugeMeasure
  -- (c⁻¹ • ν).map f = c⁻¹ • (ν.map f)
  rw [Measure.map_smul]
  congr 1
  -- Goal: ((haarProduct G n).withDensity (boltzmann_density S_W)).map (link_mult i g)
  --     = (haarProduct G n).withDensity (boltzmann_density S_W)
  -- (Note: productHaar (haar_G G) n is haarProduct G n by definition.)
  show ((haarProduct G n).withDensity (boltzmann_density S_W)).map (link_mult i g) =
       (haarProduct G n).withDensity (boltzmann_density S_W)
  ext A hA
  rw [Measure.map_apply (link_mult_measurable i g) hA,
      withDensity_apply _ ((link_mult_measurable i g) hA),
      withDensity_apply _ hA]
  -- Goal: ∫⁻ U in (link_mult i g)⁻¹' A, ρ U ∂haarProduct
  --     = ∫⁻ U in A, ρ U ∂haarProduct
  -- Step 1: rewrite restrict integrals as indicator integrals.
  rw [← lintegral_indicator ((link_mult_measurable i g) hA),
      ← lintegral_indicator hA]
  -- Step 2: gauge-invariance of ρ pointwise.
  have h_rho_inv : ∀ U, boltzmann_density S_W (link_mult i g U) =
                        boltzmann_density S_W U := by
    intro U
    unfold boltzmann_density
    rw [hS_inv i g U]
  -- Step 3: indicator-of-preimage = indicator ∘ f, then use change of variables.
  have h_eq : (fun U => ((link_mult i g)⁻¹' A).indicator (boltzmann_density S_W) U) =
              (fun U => A.indicator (boltzmann_density S_W) (link_mult i g U)) := by
    funext U
    by_cases hU : link_mult i g U ∈ A
    · have h1 : U ∈ (link_mult i g)⁻¹' A := hU
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hU, h_rho_inv]
    · have h2 : U ∉ (link_mult i g)⁻¹' A := hU
      rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem hU]
  rw [h_eq]
  -- Step 4: change of variables via lintegral_map + B.1.b.ii.
  have h_meas_indicator : Measurable (A.indicator (boltzmann_density S_W)) :=
    (boltzmann_density_measurable S_W hS_meas).indicator hA
  rw [← lintegral_map h_meas_indicator (link_mult_measurable i g)]
  rw [haarProduct_left_invariant_link G n i g]

end

end Ramtastic.QuantumYM.CompactGroupProduct
