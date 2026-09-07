/-
  CartanProof.lean — The Cartan identity {ξ∧, ξ⌟} = ‖ξ‖².
  The one bolt. Author: C. Forrester / Mael (2026-04-18) 🐟
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.Sobolev.CartanProof

open ContinuousAlternatingMap

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Interior product: ξ ⌟ ω = ω(ξ, ·). -/
abbrev interiorProd {k : ℕ} (ξ : E) (ω : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    E [⋀^Fin k]→L[ℝ] ℝ :=
  ω.curryLeft ξ

/-- Exterior product: ξ ∧ ω = alternation of ⟨ξ,·⟩ ⊗ ω. -/
def exteriorProd {k : ℕ} (ξ : E) (ω : E [⋀^Fin k]→L[ℝ] ℝ) :
    E [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ
    ((innerSL ℝ ξ).smulRight ω)

theorem cartan_identity {k : ℕ} (ξ : E) (ω : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    interiorProd ξ (exteriorProd ξ ω) +
    exteriorProd ξ (interiorProd ξ ω) =
    (‖ξ‖ ^ 2 : ℝ) • ω := by
  unfold interiorProd exteriorProd
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    curryLeft_apply_apply]
  -- Goal: (alternatizeUncurryFinCLM ℝ E ℝ (smulRight (innerSL ℝ ξ) ω)) (vecCons ξ v) +
  --       (alternatizeUncurryFinCLM ℝ E ℝ (smulRight (innerSL ℝ ξ) (curryLeft ω ξ))) v =
  --       ‖ξ‖² • ω v
  -- Rewrite alternatizeUncurryFinCLM to alternatizeUncurryFin (they're rfl-equal)
  -- Then apply alternatizeUncurryFin_apply to expand into sums
  simp only [alternatizeUncurryFinCLM_apply]
  rw [alternatizeUncurryFin_apply, alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, curryLeft_apply_apply]
  -- NOW the goal should be two Finset.sum expressions.
  -- First: ∑ i : Fin(k+2), (-1)^i • ⟨ξ, vecCons ξ v i⟩_ℝ • ω(removeNth i (vecCons ξ v))
  -- Second: ∑ j : Fin(k+1), (-1)^j • ⟨ξ, v j⟩_ℝ • ω(vecCons ξ (removeNth j v))
  -- Split first sum at i=0.
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, real_inner_self_eq_norm_sq]
  -- i=0 term: ‖ξ‖² • ω(removeNth 0 (vecCons ξ v))
  -- removeNth 0 (vecCons ξ v) = v
  -- Remaining: ∑ i, (-1)^(i+1) • ⟨ξ, v i⟩ • ω(removeNth (succ i) (vecCons ξ v))
  --          + ∑ j, (-1)^j • ⟨ξ, v j⟩ • ω(vecCons ξ (removeNth j v))
  -- removeNth (succ i) (vecCons ξ v) = vecCons ξ (removeNth i v) [KEY IDENTITY]
  -- (-1)^(i+1) = -(-1)^i
  -- So the two sums cancel: ∑(-(-1)^i • x_i) + ∑((-1)^j • x_j) = 0.
  -- What remains: ‖ξ‖² • ω v.
  -- Step 1: removeNth 0 (vecCons ξ v) = v → the leading term is ‖ξ‖² • ω v.
  -- Step 2: Show the two sums cancel.
  -- (-1)^(i+1) = -(-1)^i means the i-sum is the negative of the j-sum.
  -- So their sum is 0. What remains: ‖ξ‖² • ω(removeNth 0 (vecCons ξ v)) = ‖ξ‖² • ω v.
  -- Try: simp + ring to close.
  simp only [Fin.removeNth_zero, pow_succ, neg_one_mul, neg_smul]
  -- After simp: the removeNth 0 should simplify to v.
  -- And the cross terms should have -(-1)^i form.
  -- The two sums: ∑(-1 • (-1)^i • x_i) + ∑((-1)^j • x_j) where x_i = x_j.
  -- = ∑((-(-1)^i) • x_i + (-1)^i • x_i) = ∑ 0 = 0.
  -- Need removeNth (succ i) (vecCons ξ v) = vecCons ξ (removeNth i v)
  -- to make the x_i match the x_j.
  -- Need: removeNth (succ i) (vecCons ξ v) = vecCons ξ (removeNth i v)
  -- And then the two sums cancel (opposite signs, same terms).
  -- Use congr_arg to rewrite inside the sum, then add_neg_cancel.
  have key : ∀ i : Fin (k + 1),
      Fin.removeNth (Fin.succ i) (Matrix.vecCons ξ v) =
      Matrix.vecCons ξ (Fin.removeNth i v) := by
    intro i
    funext j
    simp only [Fin.removeNth, Matrix.vecCons, Function.comp]
    -- Both sides: functions applied to j.
    -- LHS: (Fin.cons ξ v) ((Fin.succ i).succAbove j)
    -- RHS: (Fin.cons ξ (fun j => v (i.succAbove j))) j
    -- Case j = 0: succAbove (succ i) 0 = 0 (since 0 < succ i). LHS = ξ. RHS = ξ.
    -- Case j > 0: need to show equality of v-indices.
    refine Fin.cases ?_ (fun j' => ?_) j
    · -- j = 0
      simp [Fin.succAbove, Fin.cons_zero]
    · -- j = succ j'
      -- LHS: Fin.cons ξ v ((Fin.succ i).succAbove (Fin.succ j'))
      -- RHS: Fin.cons ξ (Fin.removeNth i v) (Fin.succ j')
      --     = v (i.succAbove j')                [by Fin.cons_succ + removeNth def]
      -- Use Fin.succ_succAbove_succ: (succ i).succAbove (succ j') = succ (i.succAbove j')
      simp only [Fin.succ_succAbove_succ, Fin.cons_succ, Fin.removeNth]
  simp_rw [key]
  -- Now both sums: ∑ i, -((-1)^i • ⟨ξ, v i⟩ • ω(vecCons ξ (removeNth i v)))
  --             + ∑ j, (-1)^j • ⟨ξ, v j⟩ • ω(vecCons ξ (removeNth j v))
  -- = -S + S = 0.
  -- After simp_rw [key]: both sums have the same ω argument.
  -- The signs differ: one has -((-1)^i • ...) and the other has (-1)^i • ...
  -- Their sum is zero. What remains: ‖ξ‖² • ω(removeNth 0 (vecCons ξ v)) = ‖ξ‖² • ω v.
  -- But removeNth 0 (vecCons ξ v) = v already handled by earlier simp.
  -- Try: the goal should now be ‖ξ‖² • ω ? + (-S + S) = ‖ξ‖² • ω v.
  -- The -S + S = 0 part:
  ring_nf
  simp [add_comm, add_left_comm, add_assoc, neg_add_cancel]

end

end Ramtastic.Sobolev.CartanProof
