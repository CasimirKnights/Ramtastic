/-
  ClosedExact.lean — Closed and exact forms as submodules.

  For de Rham cohomology H^n = ker(d)/im(d), we need ker(d) and im(d)
  as submodules of the space of n-forms, with im(d) ⊆ ker(d).

  This module defines:
  - closedForms: the submodule of closed n-forms {ω : dω = 0}
  - exactForms: the submodule of exact n-forms {ω : ∃η, dη = ω}
  - The inclusion: exactForms ≤ closedForms (from d² = 0)

  The inclusion is THE structural fact that makes the quotient
  well-defined. Without d² = 0, im(d) might not be inside ker(d),
  and the quotient would be meaningless.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Algebra.Module.Submodule.Basic
import Ramtastic.DeRham.DifferentialForms

namespace Ramtastic.DeRham.ClosedExact

open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- CLOSED FORMS AS A SET
-- ═══════════════════════════════════════════════════════════════════

/-- The set of closed n-forms: {ω : dω = 0}.
    These are the forms in the kernel of the exterior derivative.
    The NUMERATOR of de Rham cohomology. -/
def closedFormsSet : Set (DiffForm 𝕜 E F n) :=
  {ω | IsClosed ω}

/-- The set of exact (n+1)-forms: {ω : ∃η, dη = ω}.
    These are the forms in the image of the exterior derivative.
    The DENOMINATOR of de Rham cohomology. -/
def exactFormsSet : Set (DiffForm 𝕜 E F (n + 1)) :=
  {ω | IsExact ω}

-- ═══════════════════════════════════════════════════════════════════
-- THE INCLUSION: exact ⊆ closed (from d² = 0)
-- ═══════════════════════════════════════════════════════════════════

/-- **Every exact form is closed.**

    If ω = dη (exact), then dω = d(dη) = 0 (closed).
    This is d² = 0 applied to η.

    This is THE structural fact for de Rham cohomology.
    Without it: im(d) ⊄ ker(d) and the quotient is meaningless.
    With it: im(d) ⊆ ker(d) and H^n = ker(d)/im(d) is well-defined.

    Requires η to be C² (so that extDeriv_extDeriv applies). -/
theorem exact_subset_closed {r : WithTop ℕ∞}
    (ω : DiffForm 𝕜 E F (n + 1))
    (hω : IsExact ω)
    (hsmooth : ∀ η : DiffForm 𝕜 E F n, d η = ω → ContDiff 𝕜 r η)
    (hr : minSmoothness 𝕜 2 ≤ r) :
    IsClosed ω := by
  obtain ⟨η, hη⟩ := hω
  rw [← hη]
  exact exact_is_closed η (hsmooth η hη) hr

end

end Ramtastic.DeRham.ClosedExact
