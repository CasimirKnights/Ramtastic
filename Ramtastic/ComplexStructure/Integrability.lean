/-
  Integrability.lean — Integrability of almost complex structures.

  An almost complex structure J is integrable if the Nijenhuis tensor
  N_J vanishes. On flat spaces this is automatic.

  The key consequence for ∂̄²=0: d(J*df) is type (1,1) on flat spaces.
  This follows from J²=-id and symmetry of the second derivative.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ComplexStructure.DelDelBar

namespace Ramtastic.ComplexStructure.Integrability

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.ComplexStructure.AlmostComplex
open Ramtastic.ComplexStructure.TypeDecomposition
open Ramtastic.ComplexStructure.DelDelBar

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [acs : AlmostComplexStr E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- ═══════════════════════════════════════════════════════════════════
-- FLAT NIJENHUIS = 0
-- ═══════════════════════════════════════════════════════════════════

/-- On a flat space, Nijenhuis tensor vanishes (from AlmostComplex). -/
theorem flat_nijenhuis_zero (X Y : E) :
    nijenhuisTensor (acs := acs) (fun _ _ => 0) X Y = 0 :=
  nijenhuis_vanishes_flat X Y

-- ═══════════════════════════════════════════════════════════════════
-- THE COMPLETE ∂/∂̄ PACKAGE
-- ═══════════════════════════════════════════════════════════════════

/-- The full ∂/∂̄ package on functions.
    Given the type (1,1) property for d(J*df):
    1. d = ∂ + ∂̄ (splitting)
    2. ∂f is type (1,0), ∂̄f is type (0,1) (eigenvalue properties)
    3. d(Re(∂f)) = 0, d(Re(∂̄f)) = 0 (from d²=0)
    4. d(Im(∂̄f)) is type (1,1), so ∂̄²=0 in the (0,2)-projection
    5. d(Im(∂f)) is type (1,1), so ∂²=0 in the (2,0)-projection -/
theorem del_delbar_package {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r)
    (h_type11 : ∀ y (m : Fin 2 → E),
      extDeriv (pullbackJ (fun x => extDeriv f x)) y (acs.J ∘ m) =
      extDeriv (pullbackJ (fun x => extDeriv f x)) y m) :
    -- 1. Splitting: Re(∂f) + Re(∂̄f) = df
    (∀ x m, (del f).re x m + (delbar f).re x m = extDeriv f x m) ∧
    -- 2. Eigenvalues: ∂f is (1,0), ∂̄f is (0,1)
    (∀ x m, pullbackJ (del f).re x m = -((del f).im x m)) ∧
    (∀ x m, pullbackJ (delbar f).re x m = (delbar f).im x m) ∧
    -- 3. d(Re) = 0 from d²=0
    (∀ x, extDeriv (del f).re x = 0) ∧
    (∀ x, extDeriv (delbar f).re x = 0) ∧
    -- 4. d(Im) is type (1,1) — ∂²=0 and ∂̄²=0 in the correct projection
    (∀ x m, proj20_02 (fun x => extDeriv (delbar f).im x) x m = 0) ∧
    (∀ x m, proj20_02 (fun x => extDeriv (del f).im x) x m = 0) :=
  ⟨del_add_delbar_re f,
   del_eigenvalue_re f,
   delbar_eigenvalue_re f,
   fun x => del_sq_re f hf hr x,
   fun x => delbar_sq_re f hf hr x,
   fun x m => delbar_sq_proj f x m h_type11,
   fun x m => del_sq_proj f x m h_type11⟩

end

end Ramtastic.ComplexStructure.Integrability
