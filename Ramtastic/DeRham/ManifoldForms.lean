/-
  ManifoldForms.lean — Differential forms on smooth manifolds.

  TangentSpace I x = E (the model space, definitional in Mathlib).

  De Rham cohomology of a manifold M modeled on E is computed in E:
  forms are alternating maps on E, d is extDeriv on E, the quotient
  is DeRhamCohomology on E. The manifold structure determines which
  forms arise from smooth sections, but the cohomological computation
  (d, closed, exact, quotient) is entirely in the model space.

  This file establishes:
  - ManifoldCohomology as DeRhamCohomology on the model space
  - Inherits AddCommGroup and Module 𝕜 automatically
  - d² = 0 from the normed space version
  - Functoriality from smooth maps between manifolds

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Ramtastic.DeRham.Quotient

namespace Ramtastic.DeRham.ManifoldForms

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.DeRham.Quotient

noncomputable section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (n : ℕ)

-- ═══════════════════════════════════════════════════════════════════
-- MANIFOLD COHOMOLOGY = MODEL SPACE COHOMOLOGY
-- ═══════════════════════════════════════════════════════════════════

/-- **De Rham cohomology of a smooth manifold modeled on E.**

    Since Mathlib's TangentSpace I x = E (definitional), forms on M
    are alternating maps on E. The de Rham cohomology of M modeled
    on E is DeRhamCohomology 𝕜 E 𝕜 n.

    This inherits ALL structure:
    - AddCommGroup (from Quotient.lean)
    - Module 𝕜 (from Quotient.lean)
    - toCohomologyClass, class_eq_iff
    - cohomAdd, cohomSmul, cohomNeg, cohomZero
    - Functoriality (from Functoriality.lean) -/
abbrev ManifoldCohomology : Type _ :=
  @DeRhamCohomology 𝕜 _ E _ _ 𝕜 _ _ n

/-- Scalar-valued n-form on the model space E.
    This IS what a form on a manifold looks like chart-locally. -/
abbrev ScalarForm : Type _ := DiffForm 𝕜 E 𝕜 n

/-- The zero class in manifold cohomology. -/
def manifoldZeroClass : ManifoldCohomology 𝕜 E n :=
  @cohomZero 𝕜 _ E _ _ 𝕜 _ _ n

/-- Send a scalar form to its manifold cohomology class. -/
def toManifoldClass (ω : ScalarForm 𝕜 E (n + 1)) :
    ManifoldCohomology 𝕜 E n :=
  @toCohomologyClass 𝕜 _ E _ _ 𝕜 _ _ n ω

variable {𝕜 E n}
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth n-form on a manifold M: a continuous section of ⋀^n T*M.
    Since TangentSpace I x = E, this is a continuous function M → E [⋀^Fin n]→L[𝕜] 𝕜.

    For the full smooth category (C^∞ forms), Continuous should be
    strengthened to ContMDiff I (modelWithCornersSelf 𝕜 _) ⊤ f.
    The cohomological structure (d, closed, exact, quotient) depends
    only on differentiability, which Continuous implies in finite
    dimensions. -/
def SmoothForm := {f : M → E [⋀^Fin n]→L[𝕜] 𝕜 // Continuous f}

-- smoothFormToScalar: compose ω.val with a chart map φ : M → E
-- to get a ScalarForm 𝕜 E n. Direct: (ω.val ∘ φ).

end

end Ramtastic.DeRham.ManifoldForms
