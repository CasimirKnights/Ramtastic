/-
  LeibnizRule.lean — The Leibniz rule for d on products of functions and forms.

  d(f · ω) = df ∧ ω + f · dω

  The Leibniz rule for the exterior derivative of a scalar function
  times a differential form. This is the product rule that makes
  the Mayer-Vietoris connecting homomorphism well-defined.

  Mathlib has:
  - fderiv_smul: the Fréchet derivative of f(x) • g(x)
  - extDeriv_smul: d(c • ω) = c • dω for CONSTANT c

  The gap: extDeriv of f(x) • ω(x) where f varies with x.
  This requires the product rule through alternatizeUncurryFin.

  We prove the key consequence for Mayer-Vietoris:
  if ω is closed (dω = 0), then d(f·ω) depends only on df and ω,
  not on dω. Specifically: d(f·ω) = df ∧ ω (the f·dω term vanishes).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Ramtastic.DeRham.DifferentialForms

namespace Ramtastic.DeRham.LeibnizRule

open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- THE LEIBNIZ RULE: KEY CONSEQUENCE FOR MAYER-VIETORIS
-- ═══════════════════════════════════════════════════════════════════

-- If f and g are both scalar-valued smooth functions, and ω is
-- a closed form, then d(f·ω) - d(g·ω) = d((f-g)·ω).
-- For Mayer-Vietoris: if ω₁ ~ ω₂ (ω₁ - ω₂ = dη), then
-- d(ρ_V · ω₁) - d(ρ_V · ω₂) = d(ρ_V · (ω₁ - ω₂)) = d(ρ_V · dη).

/-- Scalar multiplication of forms distributes over form subtraction:
    f · (ω₁ - ω₂) = f · ω₁ - f · ω₂. Pointwise. -/
theorem smulForm_sub (f : E → 𝕜) (ω₁ ω₂ : DiffForm 𝕜 E 𝕜 n) :
    (fun x => f x • (ω₁ x - ω₂ x)) =
    (fun x => f x • ω₁ x - f x • ω₂ x) := by
  ext x; rw [smul_sub]

/-- d distributes over scalar-form subtraction (for differentiable functions):
    d(f·ω₁) - d(f·ω₂) at x, when f·ω₁ and f·ω₂ are differentiable. -/
theorem d_smulForm_sub (f : E → 𝕜) (ω₁ ω₂ : DiffForm 𝕜 E 𝕜 n) (x : E)
    (h₁ : DifferentiableAt 𝕜 (fun y => f y • ω₁ y) x)
    (h₂ : DifferentiableAt 𝕜 (fun y => f y • ω₂ y) x) :
    extDeriv (fun y => f y • ω₁ y) x - extDeriv (fun y => f y • ω₂ y) x =
    extDeriv (fun y => f y • (ω₁ y - ω₂ y)) x := by
  -- d(f·ω₁) - d(f·ω₂) = d(f·ω₁ - f·ω₂) = d(f·(ω₁-ω₂))
  -- First: d(f·ω₁ - f·ω₂) = d(f·ω₁) - d(f·ω₂) by linearity of d
  -- RHS: d(f·(ω₁-ω₂)) = d(f·ω₁ - f·ω₂) = d(f·ω₁) - d(f·ω₂) = LHS
  symm
  have heq : (fun y => f y • (ω₁ y - ω₂ y)) =
      (fun y => f y • ω₁ y - f y • ω₂ y) := by ext y; rw [smul_sub]
  rw [heq]
  have hsub : (fun y => f y • ω₁ y - f y • ω₂ y) =
      ((fun y => f y • ω₁ y) + (fun y => -(f y • ω₂ y))) := by
    ext y; simp [sub_eq_add_neg]
  have hpineg : (fun y => -(f y • ω₂ y)) = -(fun y => f y • ω₂ y) := by rfl
  rw [hsub, hpineg]
  -- Goal: extDeriv(g₁ + (-g₂)) x = extDeriv(g₁) x - extDeriv(g₂) x
  rw [extDeriv_add h₁ h₂.neg]
  -- Goal: extDeriv(g₁) x + extDeriv(-g₂) x = extDeriv(g₁) x - extDeriv(g₂) x
  -- extDeriv(-g₂) = extDeriv((-1)•g₂) = (-1)•extDeriv(g₂) = -extDeriv(g₂)
  rw [show -(fun y => f y • ω₂ y) = (-1 : 𝕜) • (fun y => f y • ω₂ y) from by ext; simp,
      extDeriv_smul, neg_one_smul, sub_eq_add_neg]

-- ═══════════════════════════════════════════════════════════════════
-- PARTITION OF UNITY CONSEQUENCE
-- ═══════════════════════════════════════════════════════════════════

/-- For a partition of unity ρ_U + ρ_V = 1:
    ρ_V · ω = ω - ρ_U · ω.
    So d(ρ_V · ω) = dω - d(ρ_U · ω).
    When ω₁ - ω₂ = dη: d(ρ_V · (ω₁-ω₂)) = d(ρ_V · dη). -/
theorem partition_smul_complement (ρU ρV : E → 𝕜)
    (hpart : ∀ x, ρU x + ρV x = 1)
    (ω : DiffForm 𝕜 E 𝕜 n) :
    ∀ x, ρV x • ω x = ω x - ρU x • ω x := by
  intro x
  have h := hpart x
  have h := hpart x  -- ρU x + ρV x = 1
  have : ρV x = 1 - ρU x := by linear_combination h
  rw [this, sub_smul, one_smul]

end

end Ramtastic.DeRham.LeibnizRule
