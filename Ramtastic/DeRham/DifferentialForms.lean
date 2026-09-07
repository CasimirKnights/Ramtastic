/-
  DifferentialForms.lean — Differential forms and the exterior derivative.

  A differential n-form on a normed space E with values in F is:
    ω : E → E [⋀^Fin n]→L[𝕜] F

  The exterior derivative d takes n-forms to (n+1)-forms:
    d : (E → E [⋀^Fin n]→L[𝕜] F) → (E → E [⋀^Fin (n+1)]→L[𝕜] F)

  The fundamental property: d² = 0 (Mathlib: extDeriv_extDeriv).
  This means: every exact form is closed (im d ⊆ ker d).
  De Rham cohomology: H^n = ker(d)/im(d).

  This module defines:
  - DiffForm: abbreviation for the form type
  - Closed forms: ker(d) = {ω : dω = 0}
  - Exact forms: im(d) = {ω : ∃ η, dη = ω}
  - The inclusion: exact → closed (from d² = 0)

  Built from Mathlib's extDeriv.
  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Tactic

namespace Ramtastic.DeRham.DifferentialForms

open scoped ContinuousAlternatingMap

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- DIFFERENTIAL FORMS
-- ═══════════════════════════════════════════════════════════════════

/-- A differential n-form on E with values in F.
    ω assigns to each point x ∈ E a continuous alternating
    n-linear map E^n → F. -/
abbrev DiffForm (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n : ℕ) : Type _ :=
  E → E [⋀^Fin n]→L[𝕜] F

/-- The exterior derivative: d takes n-forms to (n+1)-forms.
    This is Mathlib's extDeriv. -/
def d (ω : DiffForm 𝕜 E F n) : DiffForm 𝕜 E F (n + 1) :=
  fun x => extDeriv ω x

-- ═══════════════════════════════════════════════════════════════════
-- CLOSED AND EXACT FORMS
-- ═══════════════════════════════════════════════════════════════════

/-- A closed n-form: dω = 0. In the kernel of d.
    Closed forms are the NUMERATOR of de Rham cohomology. -/
def IsClosed (ω : DiffForm 𝕜 E F n) : Prop :=
  ∀ x : E, extDeriv ω x = 0

/-- An exact n-form: ω = dη for some (n-1)-form η. In the image of d.
    Exact forms are the DENOMINATOR of de Rham cohomology.
    (Only defined for n ≥ 1 since there's no (-1)-form.) -/
def IsExact (ω : DiffForm 𝕜 E F (n + 1)) : Prop :=
  ∃ η : DiffForm 𝕜 E F n, d η = ω

-- ═══════════════════════════════════════════════════════════════════
-- d² = 0: EVERY EXACT FORM IS CLOSED
-- ═══════════════════════════════════════════════════════════════════

/-- **d² = 0**: the exterior derivative of the exterior derivative vanishes.
    This is the FUNDAMENTAL PROPERTY that makes cohomology well-defined.
    im(d) ⊆ ker(d) because d(dη) = 0 for any η.

    From Mathlib: extDeriv_extDeriv (for smooth forms). -/
theorem exact_is_closed {r : WithTop ℕ∞} (ω : DiffForm 𝕜 E F n)
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    IsClosed (d ω) := by
  intro x
  exact congr_fun (extDeriv_extDeriv hω hr) x

-- ═══════════════════════════════════════════════════════════════════
-- LINEARITY OF d
-- ═══════════════════════════════════════════════════════════════════

/-- d is additive: d(ω₁ + ω₂) = dω₁ + dω₂ (pointwise).
    Requires differentiability of both forms. -/
theorem d_add (ω₁ ω₂ : DiffForm 𝕜 E F n) (x : E)
    (h₁ : DifferentiableAt 𝕜 ω₁ x) (h₂ : DifferentiableAt 𝕜 ω₂ x) :
    d (ω₁ + ω₂) x = d ω₁ x + d ω₂ x := by
  unfold d; exact extDeriv_add h₁ h₂

/-- d commutes with scalar multiplication: d(c • ω) = c • dω. -/
theorem d_smul (c : 𝕜) (ω : DiffForm 𝕜 E F n) (x : E) :
    d (c • ω) x = c • d ω x := by
  unfold d; exact extDeriv_smul c ω

/-- d sends 0 to 0: d(0) = 0. -/
theorem d_zero (x : E) : d (0 : DiffForm 𝕜 E F n) x = 0 := by
  unfold d extDeriv
  have : fderiv 𝕜 (0 : E → E [⋀^Fin n]→L[𝕜] F) x = 0 :=
    (hasFDerivAt_const (0 : E [⋀^Fin n]→L[𝕜] F) x).fderiv
  rw [this]; exact map_zero _

/-- d sends negation through: d(-ω) = -dω. -/
theorem d_neg (ω : DiffForm 𝕜 E F n) (x : E) :
    d (-ω) x = -d ω x := by
  rw [show (-ω : DiffForm 𝕜 E F n) = ((-1 : 𝕜) • ω : DiffForm 𝕜 E F n) from by ext; simp]
  rw [d_smul, neg_one_smul]

-- ═══════════════════════════════════════════════════════════════════
-- CLOSED FORMS: SUBMODULE PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- The zero form is closed: d(0) = 0. -/
theorem zero_isClosed : IsClosed (0 : DiffForm 𝕜 E F n) :=
  fun x => d_zero x

/-- Closed forms are closed under addition (for differentiable forms). -/
theorem isClosed_add {ω₁ ω₂ : DiffForm 𝕜 E F n}
    (h₁ : IsClosed ω₁) (h₂ : IsClosed ω₂)
    (hd₁ : Differentiable 𝕜 ω₁) (hd₂ : Differentiable 𝕜 ω₂) :
    IsClosed (ω₁ + ω₂) := by
  intro x
  -- IsClosed means extDeriv (ω₁+ω₂) x = 0
  show extDeriv (ω₁ + ω₂) x = 0
  rw [extDeriv_add hd₁.differentiableAt hd₂.differentiableAt]
  rw [show extDeriv ω₁ x = 0 from h₁ x, show extDeriv ω₂ x = 0 from h₂ x, add_zero]

/-- Closed forms are closed under scalar multiplication. -/
theorem isClosed_smul {ω : DiffForm 𝕜 E F n} (h : IsClosed ω) (c : 𝕜) :
    IsClosed (c • ω) := by
  intro x
  show extDeriv (c • ω) x = 0
  rw [extDeriv_smul, show extDeriv ω x = 0 from h x, smul_zero]

/-- Closed forms are closed under negation. -/
theorem isClosed_neg {ω : DiffForm 𝕜 E F n} (h : IsClosed ω) :
    IsClosed (-ω) := by
  intro x; show extDeriv (-ω) x = 0
  rw [show (-ω : DiffForm 𝕜 E F n) = ((-1 : 𝕜) • ω) from by ext; simp]
  rw [extDeriv_smul, show extDeriv ω x = 0 from h x, smul_zero]

/-- The zero form is exact: 0 = d(0). -/
theorem zero_isExact : IsExact (0 : DiffForm 𝕜 E F (n + 1)) :=
  ⟨0, funext fun x => by show d 0 x = 0; exact d_zero x⟩

/-- Exact forms are closed under scalar multiplication. -/
theorem isExact_smul {ω : DiffForm 𝕜 E F (n + 1)} (h : IsExact ω) (c : 𝕜) :
    IsExact (c • ω) := by
  obtain ⟨η, hη⟩ := h
  exact ⟨c • η, funext fun x => by
    change extDeriv (c • η) x = c • ω x
    rw [extDeriv_smul]; change c • d η x = c • ω x
    rw [congr_fun hη x]⟩

/-- Exact forms are closed under addition (for differentiable primitives). -/
theorem isExact_add {ω₁ ω₂ : DiffForm 𝕜 E F (n + 1)}
    (h₁ : ∃ η : DiffForm 𝕜 E F n, Differentiable 𝕜 η ∧ d η = ω₁)
    (h₂ : ∃ η : DiffForm 𝕜 E F n, Differentiable 𝕜 η ∧ d η = ω₂) :
    IsExact (ω₁ + ω₂) := by
  obtain ⟨η₁, hdiff₁, hη₁⟩ := h₁
  obtain ⟨η₂, hdiff₂, hη₂⟩ := h₂
  exact ⟨η₁ + η₂, funext fun x => by
    change extDeriv (η₁ + η₂) x = ω₁ x + ω₂ x
    rw [extDeriv_add hdiff₁.differentiableAt hdiff₂.differentiableAt]
    change d η₁ x + d η₂ x = ω₁ x + ω₂ x
    rw [congr_fun hη₁ x, congr_fun hη₂ x]⟩

end

end Ramtastic.DeRham.DifferentialForms
