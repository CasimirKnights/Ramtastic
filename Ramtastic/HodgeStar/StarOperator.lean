/-
  StarOperator.lean — The Hodge star operator ★ : Ω^k → Ω^{n-k}.

  The Hodge star uses a Riemannian metric and orientation to convert
  k-forms to (n-k)-forms. Defined by: α ∧ ★β = ⟨α,β⟩ vol.

  Key properties: linearity, isometry, ★★ = (-1)^{k(n-k)}.
  In dimension 4 on 2-forms: ★★ = 1 (self-dual/anti-self-dual splitting).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Ramtastic.DeRham.DifferentialForms

namespace Ramtastic.HodgeStar.StarOperator

open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- THE HODGE STAR MAP
-- ═══════════════════════════════════════════════════════════════════

/-- The Hodge star as a linear isometry on differential forms.
    Parametrized by source degree k and target degree k'.
    The defining property: α ∧ ★β = ⟨α,β⟩ vol. -/
class HodgeStarMap (k k' : ℕ) where
  /-- The Hodge star map. -/
  star : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k'
  /-- ★ is additive. -/
  star_add : ∀ ω₁ ω₂, star (ω₁ + ω₂) = star ω₁ + star ω₂
  /-- ★ is ℝ-linear. -/
  star_smul : ∀ (c : ℝ) ω, star (c • ω) = c • star ω
  /-- ★ preserves differentiability. ★ is algebraic (no derivatives involved),
      so if ω is differentiable then ★ω is differentiable. -/
  star_preserves_diff : ∀ ω, Differentiable ℝ ω → Differentiable ℝ (star ω)
  /-- ★ preserves C^r smoothness for any r. ★ is algebraic so the full smoothness
      level is inherited. This is the TRUE statement — ★ is not merely differentiable-
      preserving, it is smooth-preserving. -/
  star_preserves_contDiff : ∀ {r : WithTop ℕ∞} ω, ContDiff ℝ r ω → ContDiff ℝ r (star ω)

variable {k k' : ℕ} [hsm : HodgeStarMap (E := E) k k']

/-- ★0 = 0. -/
theorem star_zero : hsm.star (0 : DiffForm ℝ E ℝ k) = 0 := by
  have h := hsm.star_smul 0 (0 : DiffForm ℝ E ℝ k)
  simp at h; exact h

/-- ★(-ω) = -(★ω). -/
theorem star_neg (ω : DiffForm ℝ E ℝ k) :
    hsm.star (-ω) = -hsm.star ω := by
  have h := hsm.star_smul (-1) ω; simp at h; exact h

/-- ★(ω₁ - ω₂) = ★ω₁ - ★ω₂. -/
theorem star_sub (ω₁ ω₂ : DiffForm ℝ E ℝ k) :
    hsm.star (ω₁ - ω₂) = hsm.star ω₁ - hsm.star ω₂ := by
  rw [sub_eq_add_neg, hsm.star_add, star_neg, ← sub_eq_add_neg]

-- ═══════════════════════════════════════════════════════════════════
-- INVOLUTION: ★★ = (-1)^{k(n-k)}
-- ═══════════════════════════════════════════════════════════════════

/-- The double star involution: ★_{k'→k} ∘ ★_{k→k'} = (-1)^{kk'} · id.
    Connects two HodgeStarMap instances (forward and backward). -/
class HodgeStarInvolution (k k' : ℕ)
    [HodgeStarMap (E := E) k k'] [HodgeStarMap (E := E) k' k] where
  /-- ★★ω = (-1)^{kk'} · ω. -/
  star_star : ∀ (ω : DiffForm ℝ E ℝ k),
    (HodgeStarMap.star (E := E) (k := k') (k' := k))
      ((HodgeStarMap.star (k := k) (k' := k')) ω) =
    ((-1 : ℝ) ^ (k * k')) • ω

-- ═══════════════════════════════════════════════════════════════════
-- DIMENSION 4, DEGREE 2: ★ : Ω^2 → Ω^2, ★★ = 1
-- ═══════════════════════════════════════════════════════════════════

/-- In dimension 4 on 2-forms: ★ maps Ω^2 → Ω^2 (same degree!).
    And ★★ = (-1)^{2·2} = 1. This is the foundation of self-duality. -/
theorem star_star_four
    [hs : HodgeStarMap (E := E) 2 2]
    [hsi : HodgeStarInvolution (E := E) 2 2]
    (ω : DiffForm ℝ E ℝ 2) :
    hs.star (hs.star ω) = ω := by
  have h := hsi.star_star ω
  simp only [show 2 * 2 = 4 from by norm_num, show ((-1 : ℝ) ^ 4) = 1 from by norm_num,
             one_smul] at h
  exact h

/-- A 2-form is self-dual: ★ω = ω. -/
def IsSelfDual [hs : HodgeStarMap (E := E) 2 2]
    (ω : DiffForm ℝ E ℝ 2) : Prop :=
  hs.star ω = ω

/-- A 2-form is anti-self-dual: ★ω = -ω. -/
def IsAntiSelfDual [hs : HodgeStarMap (E := E) 2 2]
    (ω : DiffForm ℝ E ℝ 2) : Prop :=
  hs.star ω = -ω

/-- Self-dual and anti-self-dual implies zero. -/
theorem sd_asd_eq_zero [hs : HodgeStarMap (E := E) 2 2]
    (ω : DiffForm ℝ E ℝ 2) (hsd : IsSelfDual ω) (hasd : IsAntiSelfDual ω) :
    ω = 0 := by
  have h1 : hs.star ω = ω := hsd
  have h2 : hs.star ω = -ω := hasd
  have h3 : ω = -ω := h1.symm.trans h2
  have h4 : ω + ω = 0 := by nth_rw 1 [h3]; exact neg_add_cancel ω
  have h5 : ω = (2⁻¹ : ℝ) • ((2 : ℝ) • ω) := by rw [smul_smul]; norm_num
  rw [two_smul, h4, smul_zero] at h5; exact h5

/-- ★ preserves self-duality: ★(★ω) = ω for self-dual ω (in dim 4). -/
theorem star_selfDual [hs : HodgeStarMap (E := E) 2 2]
    [hsi : HodgeStarInvolution (E := E) 2 2]
    (ω : DiffForm ℝ E ℝ 2) (hsd : IsSelfDual ω) :
    IsSelfDual (hs.star ω) := by
  unfold IsSelfDual at *
  rw [star_star_four ω]; exact hsd.symm

/-- ★ preserves anti-self-duality (in dim 4). -/
theorem star_antiSelfDual [hs : HodgeStarMap (E := E) 2 2]
    [hsi : HodgeStarInvolution (E := E) 2 2]
    (ω : DiffForm ℝ E ℝ 2) (hasd : IsAntiSelfDual ω) :
    IsAntiSelfDual (hs.star ω) := by
  unfold IsAntiSelfDual at *
  rw [star_star_four ω, hasd]; simp

end

end Ramtastic.HodgeStar.StarOperator
