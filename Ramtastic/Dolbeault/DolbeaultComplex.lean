/-
  DolbeaultComplex.lean — The Dolbeault complex.

  ∂̄-closed and ∂̄-exact forms. ∂̄² = 0: exact implies closed.
  This is the chain complex whose cohomology is Dolbeault cohomology.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ComplexStructure.Integrability

namespace Ramtastic.Dolbeault.DolbeaultComplex

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.ComplexStructure.AlmostComplex
open Ramtastic.ComplexStructure.TypeDecomposition
open Ramtastic.ComplexStructure.DelDelBar

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [acs : AlmostComplexStr E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- ═══════════════════════════════════════════════════════════════════
-- ∂̄-CLOSED AND ∂̄-EXACT
-- ═══════════════════════════════════════════════════════════════════

/-- ∂̄-closed: the exterior derivative of both components satisfies
    the Dolbeault closedness condition. -/
def IsDelbarClosed (ω : ComplexForm E F 1) : Prop :=
  (∀ x, extDeriv ω.re x = 0) ∧
  (∀ x m, proj20_02 (fun x => extDeriv ω.im x) x m = 0)

/-- ∂̄-exact: ω = ∂̄f for some function. -/
def IsDelbarExact (ω : ComplexForm E F 1) : Prop :=
  ∃ f : DiffForm ℝ E F 0, delbar f = ω

-- ═══════════════════════════════════════════════════════════════════
-- THE CHAIN COMPLEX PROPERTY: ∂̄² = 0
-- ═══════════════════════════════════════════════════════════════════

/-- **∂̄² = 0: every ∂̄-exact form is ∂̄-closed.**
    The real part: d(Re(∂̄f)) = 0 from d²f = 0.
    The imaginary part: proj20_02(d(Im(∂̄f))) = 0 from h_type11_complete. -/
theorem delbarExact_implies_closed {r : WithTop ℕ∞}
    {ω : ComplexForm E F 1} (hω : IsDelbarExact ω)
    (hsmooth : ∀ f, delbar f = ω → ContDiff ℝ r f)
    (hr : minSmoothness ℝ 2 ≤ r)
    (h_pd : ∀ f, delbar f = ω →
      ∀ y, DifferentiableAt ℝ (pullbackJ (fun x => extDeriv f x)) y)
    (h_ed : ∀ f, delbar f = ω →
      ∀ y, DifferentiableAt ℝ (fun x => extDeriv f x) y) :
    IsDelbarClosed ω := by
  obtain ⟨f, hf⟩ := hω; subst hf
  exact ⟨fun x => delbar_sq_re f (hsmooth f rfl) hr x,
         fun x m => delbar_sq_proj f x m
           (h_type11_complete f (hsmooth f rfl) hr (h_pd f rfl) (h_ed f rfl))⟩

-- ═══════════════════════════════════════════════════════════════════
-- ∂̄-CLOSEDNESS IS A SUBMODULE CONDITION
-- ═══════════════════════════════════════════════════════════════════

/-- ∂̄-closedness is preserved under negation. -/
theorem isDelbarClosed_neg {ω : ComplexForm E F 1} (h : IsDelbarClosed ω) :
    IsDelbarClosed ⟨-ω.re, -ω.im⟩ := by
  constructor
  · intro x
    rw [show (-ω.re : DiffForm ℝ E F 1) = (-1 : ℝ) • ω.re from by ext; simp]
    rw [extDeriv_smul]; simp [h.1 x]
  · intro x m
    rw [show (-ω.im : DiffForm ℝ E F 1) = (-1 : ℝ) • ω.im from by ext; simp]
    simp only [proj20_02, extDeriv_smul, pullbackJ_smul, pullbackJ_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply]
    have h0 := h.2 x m
    simp only [proj20_02, pullbackJ_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply] at h0
    -- h0 : (1/2) • (extDeriv ω.im x (J∘m) - extDeriv ω.im x m) = 0... hmm
    -- Actually h0 already says proj20_02(...) = 0
    -- Our goal should be (-1) • (1/2) • (same thing) = 0
    -- Which is (-1/2) • thing = 0. Since (1/2) • thing = 0: thing = 0.
    -- Then (-1/2) • 0 = 0.
    -- Use: if (1/2) • a = 0 then a = 0 (smul_eq_zero)
    have h1 : extDeriv ω.im x (acs.J ∘ m) = (extDeriv ω.im x) m := by
      have h1 := (smul_eq_zero.mp h0).resolve_left (by norm_num : (1 : ℝ)/2 ≠ 0)
      exact (sub_eq_zero.mp h1).symm
    rw [h1]; module

/-- ∂̄-closedness is preserved under addition (for differentiable forms). -/
theorem isDelbarClosed_add {ω₁ ω₂ : ComplexForm E F 1}
    (h₁ : IsDelbarClosed ω₁) (h₂ : IsDelbarClosed ω₂)
    (hd_re : Differentiable ℝ ω₁.re) (hd_re' : Differentiable ℝ ω₂.re)
    (hd_im : Differentiable ℝ ω₁.im) (hd_im' : Differentiable ℝ ω₂.im) :
    IsDelbarClosed ⟨ω₁.re + ω₂.re, ω₁.im + ω₂.im⟩ := by
  constructor
  · intro x
    rw [extDeriv_add hd_re.differentiableAt hd_re'.differentiableAt]
    simp [h₁.1 x, h₂.1 x]
  · intro x m
    -- .im of the struct = ω₁.im + ω₂.im
    show proj20_02 (fun x => extDeriv (ω₁.im + ω₂.im) x) x m = 0
    simp only [proj20_02, extDeriv_add hd_im.differentiableAt hd_im'.differentiableAt,
      pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply]
    have h1_0 := h₁.2 x m; have h2_0 := h₂.2 x m
    simp only [proj20_02, pullbackJ_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply] at h1_0 h2_0
    have ha : extDeriv ω₁.im x (acs.J ∘ m) = extDeriv ω₁.im x m := by
      have := (smul_eq_zero.mp h1_0).resolve_left (by norm_num : (1 : ℝ)/2 ≠ 0)
      exact (sub_eq_zero.mp this).symm
    have hb : extDeriv ω₂.im x (acs.J ∘ m) = extDeriv ω₂.im x m := by
      have := (smul_eq_zero.mp h2_0).resolve_left (by norm_num : (1 : ℝ)/2 ≠ 0)
      exact (sub_eq_zero.mp this).symm
    rw [ha, hb]; module

end

end Ramtastic.Dolbeault.DolbeaultComplex
