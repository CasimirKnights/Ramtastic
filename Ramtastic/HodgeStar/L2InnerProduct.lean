/-
  L2InnerProduct.lean — The L² inner product on differential forms.

  (ω, η)_L² = ∫_M ⟨ω(x), η(x)⟩ dvol(x)

  The L² inner product makes k-forms into a pre-Hilbert space.

  Key results:
  - l2NormSq: ‖ω‖²_L² = ∫ ‖ω(x)‖² dμ
  - l2NormSq_nonneg: ‖ω‖²_L² ≥ 0
  - l2NormSq_zero: ‖0‖²_L² = 0
  - L2InnerProductData: abstract L² pairing with symmetry + bilinearity

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Ramtastic.HodgeStar.HodgeLaplacian

namespace Ramtastic.HodgeStar.L2InnerProduct

open MeasureTheory
open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

-- ═══════════════════════════════════════════════════════════════════
-- L² NORM SQUARED (concrete, using the operator norm)
-- ═══════════════════════════════════════════════════════════════════

/-- The L² norm squared of a k-form:
    ‖ω‖²_L² = ∫_E ‖ω(x)‖² dμ(x)
    where ‖ω(x)‖ is the operator norm of the alternating map ω(x). -/
def l2NormSq {k : ℕ} (ω : DiffForm ℝ E ℝ k) (μ : Measure E) : ℝ :=
  ∫ x, ‖ω x‖ ^ 2 ∂μ

/-- The L² norm squared is nonneg. -/
theorem l2NormSq_nonneg {k : ℕ} (ω : DiffForm ℝ E ℝ k) (μ : Measure E) :
    0 ≤ l2NormSq ω μ := by
  apply integral_nonneg; intro x; positivity

/-- The L² norm squared of zero is zero. -/
theorem l2NormSq_zero {k : ℕ} (μ : Measure E) :
    l2NormSq (0 : DiffForm ℝ E ℝ k) μ = 0 := by
  unfold l2NormSq; simp [norm_zero]

/-- The L² norm squared is homogeneous: ‖c·ω‖² = c²·‖ω‖². -/
theorem l2NormSq_smul {k : ℕ} (c : ℝ) (ω : DiffForm ℝ E ℝ k) (μ : Measure E) :
    l2NormSq (c • ω) μ = c ^ 2 * l2NormSq ω μ := by
  unfold l2NormSq
  simp only [Pi.smul_apply, norm_smul, mul_pow]
  have : (fun x : E => ‖c‖ ^ 2 * ‖ω x‖ ^ 2) = fun x => c ^ 2 * ‖ω x‖ ^ 2 := by
    ext x; rw [Real.norm_eq_abs, sq_abs]
  rw [this, integral_const_mul]

-- ═══════════════════════════════════════════════════════════════════
-- L² INNER PRODUCT (abstract, via class)
-- ═══════════════════════════════════════════════════════════════════

/-- The L² inner product on k-forms.
    Carries the pairing, its algebraic properties, AND a factorization through
    a pointwise pairing function so bilinearity can be derived under integrability.

    STRIPPED (2026-04-16): `l2Inner_self_eq_normSq` field removed — it claimed
    `l2Inner ω ω = l2NormSq ω`, but `l2NormSq` uses the OPERATOR norm while the
    natural L² inner product uses the INNER PRODUCT norm on forms (via basis
    expansion). These norms DIFFER for non-trivial forms: e.g. for ω = e⁰¹ + e²³
    in dim 4, ‖ω‖_op = 1 but ‖ω‖_inner = √2. Making the equation unconditional
    would silently propagate a false claim. Consistency with norm is a per-
    construction theorem taken at point of use.

    RESTORED 2026-04-16: bilinearity content restored via the `pairingFn`
    factorization. The class now exposes:
    - `pairingFn ω η x` — the pointwise integrand (real-valued).
    - `l2Inner_eq_integral` — `l2Inner ω η μ = ∫ x, pairingFn ω η x ∂μ`.
    - `pairingFn_add_left`, `pairingFn_smul_left` — UNCONDITIONAL pointwise
      bilinearity of the pairing function.
    From these, the derived theorems `l2Inner_add_left` (gated by integrability
    of both summand pairings) and `l2Inner_smul_left` (unconditional via
    `integral_const_mul`) reconstruct the L² bilinearity content properly. -/
class L2InnerProductData (k : ℕ) where
  /-- The L² inner product. -/
  l2Inner : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k → Measure E → ℝ
  /-- Symmetry. -/
  l2Inner_symm : ∀ ω η μ, l2Inner ω η μ = l2Inner η ω μ
  /-- Positive definiteness: ⟨ω, ω⟩ ≥ 0. -/
  l2Inner_self_nonneg : ∀ ω μ, 0 ≤ l2Inner ω ω μ
  /-- Pointwise pairing function: l2Inner is the integral of this. -/
  pairingFn : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k → E → ℝ
  /-- l2Inner is the integral of the pointwise pairing. -/
  l2Inner_eq_integral : ∀ ω η μ, l2Inner ω η μ = ∫ x, pairingFn ω η x ∂μ
  /-- Pointwise additivity in first argument (UNCONDITIONAL). -/
  pairingFn_add_left : ∀ (ω₁ ω₂ η : DiffForm ℝ E ℝ k) (x : E),
    pairingFn (ω₁ + ω₂) η x = pairingFn ω₁ η x + pairingFn ω₂ η x
  /-- Pointwise scalar linearity in first argument (UNCONDITIONAL). -/
  pairingFn_smul_left : ∀ (c : ℝ) (ω η : DiffForm ℝ E ℝ k) (x : E),
    pairingFn (c • ω) η x = c * pairingFn ω η x

variable {k : ℕ} [lid : L2InnerProductData (E := E) k]

-- ═══════════════════════════════════════════════════════════════════
-- DERIVED BILINEARITY (gated by integrability)
-- ═══════════════════════════════════════════════════════════════════

/-- Additivity of the L² inner product in the first argument, gated by
    integrability of both summand pairings. Derived from the pointwise additivity
    of `pairingFn` (`pairingFn_add_left`) and `MeasureTheory.integral_add`. -/
theorem l2Inner_add_left (ω₁ ω₂ η : DiffForm ℝ E ℝ k) (μ : Measure E)
    (h₁ : Integrable (lid.pairingFn ω₁ η) μ)
    (h₂ : Integrable (lid.pairingFn ω₂ η) μ) :
    lid.l2Inner (ω₁ + ω₂) η μ = lid.l2Inner ω₁ η μ + lid.l2Inner ω₂ η μ := by
  rw [lid.l2Inner_eq_integral, lid.l2Inner_eq_integral, lid.l2Inner_eq_integral]
  have heq : (fun x => lid.pairingFn (ω₁ + ω₂) η x) =
      (fun x => lid.pairingFn ω₁ η x + lid.pairingFn ω₂ η x) := by
    funext x; exact lid.pairingFn_add_left ω₁ ω₂ η x
  rw [heq]
  exact MeasureTheory.integral_add h₁ h₂

/-- Scalar linearity of the L² inner product in the first argument (UNCONDITIONAL).
    Derived from the pointwise linearity of `pairingFn` (`pairingFn_smul_left`)
    and `MeasureTheory.integral_const_mul`. -/
theorem l2Inner_smul_left (c : ℝ) (ω η : DiffForm ℝ E ℝ k) (μ : Measure E) :
    lid.l2Inner (c • ω) η μ = c * lid.l2Inner ω η μ := by
  rw [lid.l2Inner_eq_integral, lid.l2Inner_eq_integral]
  have heq : (fun x => lid.pairingFn (c • ω) η x) =
      (fun x => c * lid.pairingFn ω η x) := by
    funext x; exact lid.pairingFn_smul_left c ω η x
  rw [heq, MeasureTheory.integral_const_mul]

end

end Ramtastic.HodgeStar.L2InnerProduct
