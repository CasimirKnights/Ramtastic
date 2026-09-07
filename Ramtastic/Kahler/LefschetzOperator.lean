/-
  LefschetzOperator.lean — The Lefschetz operator L = ω∧.

  L : Ω^k → Ω^{k+2} sends a k-form α to ω ∧ α (wedge with the Kähler form).
  L is the raising operator of the sl(2,ℝ) representation on forms.

  The adjoint Λ = L* lowers degree by 2. Together with the weight operator
  H = [L, Λ], they satisfy the sl(2) commutation relations.

  This file provides the abstract class `LefschetzMap` carrying L with
  linearity, plus the abstract `LambdaMap` for Λ with the adjointness
  property tying L and Λ via the L² inner product.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Ramtastic.Kahler.KahlerForm
import Ramtastic.HodgeStar.L2InnerProduct
import Ramtastic.DeRham.WedgeProduct

namespace Ramtastic.Kahler.LefschetzOperator

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.Kahler.KahlerForm
open Ramtastic.HodgeStar.L2InnerProduct

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════���═══════════════════════════════════════════════════
-- LEFSCHETZ OPERATOR L
-- ═══════════════════════════════════════════════════════════════════

/-- The Lefschetz operator L : Ω^k → Ω^{k+2} (wedge with ω).
    Carries the function + linearity (additive and ℝ-linear). -/
class LefschetzMap (k : ℕ) where
  /-- The Lefschetz operator. -/
  lef : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ (k + 2)
  /-- Additive: L(α + β) = L(α) + L(β). -/
  lef_add : ∀ α β, lef (α + β) = lef α + lef β
  /-- ℝ-linear: L(c·α) = c·L(α). -/
  lef_smul : ∀ (c : ℝ) α, lef (c • α) = c • lef α
  /-- **L = ω∧**: the Lefschetz operator is wedge product with a specific
      2-form (the Kähler form ω). This TIES L to the Kähler structure.
      `wedgeDiffForm kahler α` has type `DiffForm ℝ E ℝ (2 + k)`, while
      `lef α` has type `DiffForm ℝ E ℝ (k + 2)`. The HEq bridges the
      arithmetic equality `2 + k = k + 2`. -/
  kahler : DiffForm ℝ E ℝ 2
  /-- L(α) = ω ∧ α (up to the canonical degree identification 2+k = k+2). -/
  lef_is_wedge : ∀ α,
    HEq (lef α) (Ramtastic.DeRham.WedgeProduct.wedgeDiffForm kahler α)

variable {k : ℕ} [lm : LefschetzMap (E := E) k]

/-- L(0) = 0 (from linearity). -/
theorem lef_zero : lm.lef (0 : DiffForm ℝ E ℝ k) = 0 := by
  have h := lm.lef_smul 0 (0 : DiffForm ℝ E ℝ k)
  simp at h; exact h

-- ═══════���═══════════════════════════════════════════════════════════
-- LAMBDA (Λ) — THE LEFSCHETZ ADJOINT
-- ═══��═══════════════════════════════════════════════════���═══════════

/-- The Lefschetz adjoint Λ : Ω^k → Ω^{k-2} (the L² adjoint of L).
    Carries the function + linearity. -/
class LambdaMap (k k' : ℕ) where
  /-- The Λ operator. -/
  lambda : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k'
  /-- Additive. -/
  lambda_add : ∀ α β, lambda (α + β) = lambda α + lambda β
  /-- ℝ-linear. -/
  lambda_smul : ∀ (c : ℝ) α, lambda (c • α) = c • lambda α

/-- Λ(0) = 0. -/
theorem lambda_zero {k' : ℕ} [lam : LambdaMap (E := E) k k'] :
    lam.lambda (0 : DiffForm ℝ E ℝ k) = 0 := by
  have h := lam.lambda_smul 0 (0 : DiffForm ℝ E ℝ k)
  simp at h; exact h

-- ══��═════════════════════���═════════════════════��════════════════════
-- L² ADJOINTNESS: L and Λ
-- ═══════════════════════════════════════════════════════��═══════════

/-- L² adjointness linking L and Λ: ⟨L α, β⟩_L² = ⟨α, Λ β⟩_L².
    This IS the defining property of Λ: it's the unique operator satisfying
    this for all α, β in L². -/
class LefschetzAdjoint (k : ℕ) [MeasurableSpace E]
    [lm : LefschetzMap (E := E) k]
    [lam : LambdaMap (E := E) (k + 2) k]
    [l2_lo : L2InnerProductData (E := E) k]
    [l2_hi : L2InnerProductData (E := E) (k + 2)] where
  /-- L² adjointness: ⟨Lα, β⟩_{k+2} = ⟨α, Λβ⟩_k. -/
  adjoint : ∀ (α : DiffForm ℝ E ℝ k) (β : DiffForm ℝ E ℝ (k + 2))
    (μ : MeasureTheory.Measure E),
    l2_hi.l2Inner (lm.lef α) β μ = l2_lo.l2Inner α (lam.lambda β) μ

-- ═══════════════════════════════════════════════════════════════════
-- PRIMITIVE FORMS
-- ═════════════════════════════���════════════════════���════════════════

/-- A form is primitive if Λα = 0 (it has no "L-component" to peel off). -/
def IsPrimitive (k' : ℕ) [lam : LambdaMap (E := E) k k']
    (α : DiffForm ℝ E ℝ k) : Prop :=
  lam.lambda α = 0

/-- Zero is always primitive. -/
theorem zero_isPrimitive (k' : ℕ) [lam : LambdaMap (E := E) k k'] :
    IsPrimitive k' (0 : DiffForm ℝ E ℝ k) :=
  lambda_zero (k' := k')

-- ═══════════════════════════════════��═══════════════════════════════
-- sl(2) COMMUTATOR: [L, Λ] = (k - n) on k-forms
-- ════════════════��═════════════════════════════���════════════════════

-- ═══════════════════════════════════════════════════════════════════
-- sl(2) COMMUTATOR: [L, Λ] = (k - n) · id — FULL STATEMENT
-- ═══════════════════════════════════════════════════════════════════

/-- The FULL Kähler sl(2) weight identity at degree k.

    [L, Λ](α) = Λ(L(α)) - L(Λ(α)) = ((k : ℤ) - n) • α

    This requires FOUR operator instances:
    - lm_k : LefschetzMap k (L on k-forms, producing (k+2)-forms)
    - lam_hi : LambdaMap (k+2) k (Λ applied to (k+2)-forms → k-forms)
    - lam_lo : LambdaMap k k_lo (Λ applied to k-forms → (k-2)-forms)
    - lm_lo : LefschetzMap k_lo (L on (k-2)-forms, producing k-forms)

    The degree compatibility `k_lo + 2 = k` ensures L(Λ(α)) lands back
    in k-forms. The identity then says:
        Λ(L(α)) - L(Λ(α)) = ((k : ℤ) - n) • α

    where the subtraction is in the k-form space. -/
class KahlerSL2Data (n : ℕ) (k k_lo : ℕ)
    [lm_k : LefschetzMap (E := E) k]
    [lam_hi : LambdaMap (E := E) (k + 2) k]
    [lam_lo : LambdaMap (E := E) k k_lo]
    [lm_lo : LefschetzMap (E := E) k_lo] where
  /-- Degree compatibility: k_lo + 2 = k (so L ∘ Λ maps k → k_lo → k). -/
  degree_compat : k_lo + 2 = k
  /-- **The FULL [L, Λ] = (k - n) identity.**
      Λ(L(α)) = ((k : ℤ) - n) • α + L(Λ(α))
      where L(Λ(α)) is cast from (k_lo + 2)-forms to k-forms via degree_compat.
      Equivalently: Λ(L(α)) - L(Λ(α)) = ((k : ℤ) - n) • α. -/
  sl2_weight : ∀ (α : DiffForm ℝ E ℝ k),
    lam_hi.lambda (lm_k.lef α) =
      ((k : ℤ) - (n : ℤ)) • α + degree_compat ▸ lm_lo.lef (lam_lo.lambda α)

end

end Ramtastic.Kahler.LefschetzOperator
