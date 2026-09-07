/-
  KahlerForm.lean — The Kähler form ω = g(J·, ·).

  On a Kähler manifold (M, g, J, ω): the metric g, the almost complex
  structure J, and the Kähler form ω are compatible:
    ω(v, w) = g(Jv, w)
  with ω closed (dω = 0) and J an isometry.

  This file provides `KahlerData`, bundling the compatibility conditions.
  The Kähler form is a real (1,1)-form: J-invariant and closed. It is
  the starting point for all Kähler identities.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Ramtastic.ComplexStructure.AlmostComplex
import Ramtastic.DeRham.DifferentialForms

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.Kahler.KahlerForm

open Ramtastic.ComplexStructure.AlmostComplex
open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- KÄHLER DATA
-- ═══════════════════════════════════════════════════════════════════

/-- The data of a Kähler structure: an almost complex structure J compatible
    with the inner product (J is skew-adjoint: ⟨Jv, w⟩ = -⟨v, Jw⟩), plus
    the Kähler form ω defined as ω(v, w) = ⟨Jv, w⟩, plus closedness of ω.

    The skew-adjointness of J is the KEY compatibility. From it:
    - ω is a well-defined alternating 2-form (⟨Jv, v⟩ = -⟨v, Jv⟩ ⟹ ω(v,v) = 0).
    - ω is J-invariant: ω(Jv, Jw) = ⟨J²v, Jw⟩ = -⟨v, Jw⟩ = ⟨Jv, w⟩ = ω(v,w).
    - J preserves norms: ‖Jv‖² = ⟨Jv, Jv⟩ = -⟨v, J²v⟩ = ⟨v, v⟩ = ‖v‖².

    From the Bass perspective: J is a Hinge generator on the tangent space.
    The skew-adjointness IS the geometric content of Convention B (the circle,
    not the hyperbola). The Kähler form is the SHADOW of the rotation on forms. -/
class KahlerData where
  /-- The almost complex structure. -/
  [acs : AlmostComplexStr E]
  /-- J is skew-adjoint: ⟨Jv, w⟩ = -⟨v, Jw⟩.
      This is the fundamental compatibility between J and the metric. -/
  J_skewAdj : ∀ (v w : E), @inner ℝ E _ (acs.J v) w = -@inner ℝ E _ v (acs.J w)
  /-- The Kähler form as a differential 2-form on E.
      Defined as ω(x)(v, w) = ⟨J(v), w⟩ (pointwise, using the metric). -/
  kahlerForm : DiffForm ℝ E ℝ 2
  /-- **ω = g(J·, ·)**: the Kähler form evaluates as the inner product of J
      applied to the first argument with the second argument. This TIES
      kahlerForm to J and the metric — not a free-floating 2-form. -/
  kahlerForm_def : ∀ (x : E) (v w : E),
    kahlerForm x ![v, w] = @inner ℝ E _ (acs.J v) w
  /-- ω is closed: dω = 0. The Kähler condition. -/
  kahler_closed : IsClosed kahlerForm

attribute [reducible, instance] KahlerData.acs

variable [kd : KahlerData (E := E)]

-- ═══════════════════════════════════════════════════════════════════
-- CONSEQUENCES OF SKEW-ADJOINTNESS
-- ═══════════════════════════════════════════════════════════════════

/-- J(Jv) = -v for any v, from J² = -id. -/
theorem J_J_eq_neg (v : E) : kd.acs.J (kd.acs.J v) = -v := by
  have := congr_fun (congr_arg DFunLike.coe kd.acs.J_sq) v
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at this
  exact this

/-- J preserves inner products: ⟨Jv, Jw⟩ = ⟨v, w⟩.
    From skew-adjointness + J² = -id:
    ⟨Jv, Jw⟩ = -⟨v, J(Jw)⟩ = -⟨v, -w⟩ = ⟨v, w⟩. -/
theorem J_inner_preserving (v w : E) :
    @inner ℝ E _ (kd.acs.J v) (kd.acs.J w) = @inner ℝ E _ v w := by
  rw [kd.J_skewAdj, J_J_eq_neg, inner_neg_right, neg_neg]

/-- J preserves norms: ‖Jv‖ = ‖v‖.
    Immediate from `J_inner_preserving` applied at v = w:
    ‖Jv‖² = ⟨Jv, Jv⟩ = ⟨v, v⟩ = ‖v‖². -/
theorem J_norm_preserving (v : E) :
    ‖kd.acs.J v‖ = ‖v‖ := by
  have h := J_inner_preserving (kd := kd) v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [sq_nonneg ‖kd.acs.J v‖, sq_nonneg ‖v‖, sq_abs ‖kd.acs.J v‖, sq_abs ‖v‖,
    norm_nonneg (kd.acs.J v), norm_nonneg v]

end

end Ramtastic.Kahler.KahlerForm
