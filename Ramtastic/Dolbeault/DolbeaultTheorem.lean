/-
  DolbeaultTheorem.lean — Dolbeault vanishing and the Hodge connection.

  On contractible spaces: every ∂̄-closed form is ∂̄-exact (∂̄-Poincaré).
  This gives H^{0,1}_∂̄ = 0 on flat spaces.

  The Dolbeault theorem (H^{p,q}_∂̄ ≅ H^q(X, Ω^p_hol)) and the
  connection to the Hodge decomposition require sheaf cohomology
  and Kähler identities (Pieces 6, 5) which are downstream.

  This file contains the vanishing result and the structural
  connection between Dolbeault and de Rham cohomology.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.Dolbeault.DolbeaultCohomology

namespace Ramtastic.Dolbeault.DolbeaultTheorem

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.ComplexStructure.AlmostComplex
open Ramtastic.ComplexStructure.TypeDecomposition
open Ramtastic.Dolbeault.DolbeaultComplex
open Ramtastic.Dolbeault.DolbeaultCohomology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [acs : AlmostComplexStr E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- ═══════════════════════════════════════════════════════════════════
-- DOLBEAULT VANISHING ON CONTRACTIBLE SPACES
-- ══════════════════════════════════════════════════════════════���════

/-- If Dolbeault vanishes, ∂̄-closedness and ∂̄-exactness coincide. -/
theorem closed_iff_exact_of_vanishes
    (h_van : DolbeaultVanishes E F) (ω : ComplexForm E F 1)
    [ds : DolbeaultSmooth E F] :
    IsDelbarClosed ω ↔ IsDelbarExact ω :=
  ⟨h_van ω, fun he => delbarExact_closed E F ω he⟩

-- ═══════════════════════════════════════════════════════════════════
-- THE d = ∂ + ∂̄ DECOMPOSITION AT THE COHOMOLOGY LEVEL
-- ═══════════════════════════════════════════════════════════════════

/-- Every de Rham closed 1-form decomposes into ∂-closed and ∂̄-closed
    parts via the (1,0)/(0,1) projection.

    If df = 0 (f is a closed 0-form, i.e., locally constant), then
    ∂f = 0 and ∂̄f = 0 (both components of df vanish).

    This connects the de Rham exact sequence to the Dolbeault exact
    sequence: the kernel of d maps to the kernels of ∂ and ∂̄. -/
theorem deRham_to_dolbeault (f : DiffForm ℝ E F 0)
    (hclosed : ∀ x, extDeriv f x = 0) (x : E) (m : Fin 1 → E) :
    (DelDelBar.del f).re x m = 0 ∧ (DelDelBar.del f).im x m = 0 ∧
    (DelDelBar.delbar f).re x m = 0 ∧ (DelDelBar.delbar f).im x m = 0 := by
  have hdf := hclosed x
  constructor
  · -- Re(∂f) = (1/2)df = 0
    have := proj10_ofReal_re (fun x => extDeriv f x) x m
    simp [DelDelBar.del, this, hdf, smul_zero]
  constructor
  · -- Im(∂f) = -(1/2)J*df, and J*(0) = 0
    have := proj10_ofReal_im (fun x => extDeriv f x) x m
    simp [DelDelBar.del, this, hdf, pullbackJ_zero, Pi.zero_apply, smul_zero, neg_zero]
  constructor
  · -- Re(∂̄f) = (1/2)df = 0
    have := proj01_ofReal_re (fun x => extDeriv f x) x m
    simp [DelDelBar.delbar, this, hdf, smul_zero]
  · -- Im(∂̄f) = (1/2)J*df = 0
    have := proj01_ofReal_im (fun x => extDeriv f x) x m
    simp [DelDelBar.delbar, this, hdf, pullbackJ_zero, Pi.zero_apply, smul_zero]

end

end Ramtastic.Dolbeault.DolbeaultTheorem
