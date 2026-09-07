/-
  Connection.lean — Connections on principal bundles (𝔤-valued 1-forms).

  A connection A is a 𝔤-valued 1-form: at each point x, A(x) maps
  tangent vectors to Lie algebra elements. A tells you how to
  parallel transport. It IS the gauge field.

  Curvature F = dA (abelian case). Gauge invariant by d²=0.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Ramtastic.PrincipalBundles.PrincipalBundle
import Ramtastic.DeRham.DifferentialForms

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.PrincipalBundles.Connection

open Ramtastic.PrincipalBundles.PrincipalBundle
open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ggd : GaugeGroupData]

-- ═══════════════════════════════════════════════════════════════════
-- CONNECTION AND CURVATURE FORMS
-- ═══════════════════════════════════════════════════════════════════

/-- A 𝔤-valued 1-form: the connection (gauge field).
    Explicitly: a function E → ContinuousAlternatingMap ℝ E 𝔤 (Fin 1). -/
abbrev ConnectionForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝔤 : Type*) [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] : Type _ :=
  E → E [⋀^Fin 1]→L[ℝ] 𝔤

/-- A 𝔤-valued 2-form: the curvature (field strength). -/
abbrev CurvatureForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝔤 : Type*) [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] : Type _ :=
  E → E [⋀^Fin 2]→L[ℝ] 𝔤

/-- The curvature of a connection (abelian case): F = dA.
    For G = U(1): the Lie bracket vanishes, so F = dA exactly.
    For non-abelian G: F = dA + ½[A∧A]. The bracket term
    requires the wedge product of Lie-algebra-valued forms. -/
def curvature (A : ConnectionForm E ggd.𝔤) : CurvatureForm E ggd.𝔤 :=
  fun x => extDeriv A x

-- ═══════════════════════════════════════════════════════════════════
-- GAUGE TRANSFORMATIONS (abelian)
-- ═══════════════════════════════════════════════════════════════════

/-- Abelian gauge transformation: A ↦ A + dθ where θ is a 𝔤-valued 0-form.
    For U(1): θ is a scalar function, dθ is its gradient. -/
def gaugeAct (A : ConnectionForm E ggd.𝔤)
    (θ : E → E [⋀^Fin 0]→L[ℝ] ggd.𝔤) : ConnectionForm E ggd.𝔤 :=
  fun x => A x + extDeriv θ x

/-- **Gauge invariance of curvature (abelian).**
    F(A + dθ) = dA + d(dθ) = dA = F(A).
    Because d² = 0. -/
theorem curvature_gauge_invariant {r : WithTop ℕ∞}
    (A : ConnectionForm E ggd.𝔤)
    (θ : E → E [⋀^Fin 0]→L[ℝ] ggd.𝔤)
    (hθ : ContDiff ℝ r θ) (hr : minSmoothness ℝ 2 ≤ r)
    (x : E) (hA : DifferentiableAt ℝ A x) (hdθ : DifferentiableAt ℝ (extDeriv θ) x) :
    curvature (gaugeAct A θ) x = curvature A x := by
  unfold curvature gaugeAct
  have heq : (fun x => A x + extDeriv θ x) = (A + extDeriv θ) := rfl
  rw [heq, extDeriv_add hA hdθ]
  have h_dsq : extDeriv (extDeriv θ) x = 0 :=
    congr_fun (extDeriv_extDeriv hθ hr) x
  rw [h_dsq, add_zero]

-- ═══════════════════════════════════════════════════════════════════
-- YANG-MILLS FUNCTIONAL
-- ═══════════════════════════════════════════════════════════════════

/-- The Yang-Mills functional: YM(A) = ∫ ‖F_A‖² dvol.
    The integral of the squared norm of the curvature.
    The Yang-Mills equations are the Euler-Lagrange equations for this functional.

    We define the INTEGRAND (the pointwise squared norm of the curvature).
    The full functional requires integration over M (measure theory). -/
def yangMillsIntegrand (A : ConnectionForm E ggd.𝔤) (x : E) : ℝ :=
  ‖curvature A x‖ ^ 2

/-- The Yang-Mills integrand is nonneg everywhere. -/
theorem yangMillsIntegrand_nonneg (A : ConnectionForm E ggd.𝔤) (x : E) :
    0 ≤ yangMillsIntegrand A x := by
  unfold yangMillsIntegrand; positivity

-- ═══════════════════════════════════════════════════════════════════
-- ZERO CONNECTION
-- ═══════════════════════════════════════════════════════════════════

/-- The zero connection: A = 0 (no gauge field). -/
def zeroConnection : ConnectionForm E ggd.𝔤 := fun _ => 0

/-- The curvature of the zero connection is zero: F(0) = d(0) = 0. -/
theorem curvature_zero (x : E) :
    curvature (zeroConnection (E := E) (ggd := ggd)) x = 0 := by
  unfold curvature zeroConnection extDeriv
  simp [fderiv_const, Pi.zero_apply]
  exact map_zero _

end

end Ramtastic.PrincipalBundles.Connection
