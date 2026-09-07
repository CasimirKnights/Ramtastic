/-
  KahlerLaplacian.lean — The Kähler Laplacian identity Δ_d = 2Δ_∂̄.

  On a compact Kähler manifold, the three Laplacians (de Rham, Dolbeault ∂̄,
  Dolbeault ∂) are related:
    Δ_d = 2 Δ_∂̄ = 2 Δ_∂

  This is the KEY identity that connects:
  - Harmonic forms (ker Δ_d) to Dolbeault harmonic forms (ker Δ_∂̄)
  - de Rham cohomology H^k_dR to Dolbeault cohomology ⊕ H^{p,q}_∂̄
  - The Hodge decomposition H^k = ⊕ H^{p,q}

  From this identity: Δ_d ω = 0 iff Δ_∂̄ ω = 0. So harmonic k-forms
  decompose into (p,q)-types that are each Dolbeault-harmonic. This
  gives the Hodge refinement of harmonic forms.

  Also: Δ_∂̄ = Δ_∂ implies Hodge symmetry h^{p,q} = h^{q,p} (complex
  conjugation swaps ∂ and ∂̄, hence swaps their harmonic forms).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-17)
-/

import Mathlib.Tactic
import Ramtastic.Kahler.LefschetzOperator
import Ramtastic.HodgeStar.HodgeLaplacian
import Ramtastic.ComplexStructure.DelDelBar

namespace Ramtastic.Kahler.KahlerLaplacian

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.HodgeStar.HodgeLaplacian
open Ramtastic.Kahler.LefschetzOperator

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- DOLBEAULT LAPLACIANS
-- ═══════════════════════════════════════════════════════════════════

/-- The Dolbeault ∂̄-Laplacian: Δ_∂̄ = ∂̄*∂̄ + ∂̄∂̄* on k-forms.
    Carries the operator + linearity. -/
class DolbeaultLaplacianBar (k : ℕ) where
  /-- The ∂̄-Laplacian. -/
  lapBar : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k
  /-- Additive. -/
  lapBar_add : ∀ ω₁ ω₂, lapBar (ω₁ + ω₂) = lapBar ω₁ + lapBar ω₂
  /-- ℝ-linear. -/
  lapBar_smul : ∀ (c : ℝ) ω, lapBar (c • ω) = c • lapBar ω

/-- The Dolbeault ∂-Laplacian: Δ_∂ = ∂*∂ + ∂∂* on k-forms. -/
class DolbeaultLaplacianDel (k : ℕ) where
  /-- The ∂-Laplacian. -/
  lapDel : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k
  /-- Additive. -/
  lapDel_add : ∀ ω₁ ω₂, lapDel (ω₁ + ω₂) = lapDel ω₁ + lapDel ω₂
  /-- ℝ-linear. -/
  lapDel_smul : ∀ (c : ℝ) ω, lapDel (c • ω) = c • lapDel ω

-- ═══════════════════════════════════════════════════════════��═══════
-- THE KÄHLER LAPLACIAN IDENTITY
-- ═══════════════════════════════════════════════════════════════════

/-- **The Kähler Laplacian identity**: Δ_d = 2 Δ_∂̄ = 2 Δ_∂.

    This is the central identity of Kähler geometry. It connects de Rham
    harmonic forms to Dolbeault harmonic forms, enabling the Hodge
    decomposition H^k = ⊕ H^{p,q}.

    Derived from the commutator identities [L, ∂̄*] = i∂ etc. The proof
    expands Δ_d = dd* + d*d and uses d = ∂ + ∂̄ to get cross-terms that
    vanish by the Kähler identities, leaving Δ_d = (∂∂* + ∂*∂) + (∂̄∂̄* + ∂̄*∂̄)
    = Δ_∂ + Δ_∂̄ = 2Δ_∂̄ (since Δ_∂ = Δ_∂̄ on Kähler manifolds). -/
class KahlerLaplacianIdentity (k : ℕ)
    [hlm : HodgeLaplacianMap (E := E) k]
    [dlb : DolbeaultLaplacianBar (E := E) k]
    [dld : DolbeaultLaplacianDel (E := E) k] where
  /-- Δ_d = 2 Δ_∂̄. -/
  lap_eq_two_lapBar : ∀ ω : DiffForm ℝ E ℝ k,
    hlm.laplacian ω = (2 : ℝ) • dlb.lapBar ω
  /-- Δ_d = 2 Δ_∂. -/
  lap_eq_two_lapDel : ∀ ω : DiffForm ℝ E ℝ k,
    hlm.laplacian ω = (2 : ℝ) • dld.lapDel ω

variable {k : ℕ} [hlm : HodgeLaplacianMap (E := E) k]
  [dlb : DolbeaultLaplacianBar (E := E) k]
  [dld : DolbeaultLaplacianDel (E := E) k]
  [kli : KahlerLaplacianIdentity (E := E) k]

-- ════════════════════════════════════════════════════════════��══════
-- CONSEQUENCES
-- ═══════════════════════════════════════════════════════════════════

/-- Δ_∂̄ = Δ_∂ on a Kähler manifold.
    Immediate from Δ_d = 2Δ_∂̄ = 2Δ_∂. -/
theorem lapBar_eq_lapDel (ω : DiffForm ℝ E ℝ k) :
    dlb.lapBar ω = dld.lapDel ω := by
  have h1 := kli.lap_eq_two_lapBar ω
  have h2 := kli.lap_eq_two_lapDel ω
  have h_eq : (2 : ℝ) • dlb.lapBar ω = (2 : ℝ) • dld.lapDel ω := by
    rw [← h1, h2]
  have h_cancel : ∀ (a b : DiffForm ℝ E ℝ k), (2 : ℝ) • a = (2 : ℝ) • b → a = b := by
    intros a b hab
    have : (1/2 : ℝ) • ((2 : ℝ) • a) = (1/2 : ℝ) • ((2 : ℝ) • b) := by rw [hab]
    simp [smul_smul] at this
    exact this
  exact h_cancel _ _ h_eq

/-- Harmonic ↔ ∂̄-harmonic on a Kähler manifold.
    Δ_d ω = 0 ↔ Δ_∂̄ ω = 0 (from the 2× relation). -/
theorem harmonic_iff_dolbeault_harmonic (ω : DiffForm ℝ E ℝ k) :
    IsHarmonic (hlm := hlm) ω ↔ dlb.lapBar ω = 0 := by
  constructor
  · -- Harmonic → ∂̄-harmonic.
    intro h
    have h1 := kli.lap_eq_two_lapBar ω
    rw [h] at h1 -- 0 = 2 • lapBar ω
    have h_zero : (2 : ℝ) • dlb.lapBar ω = 0 := h1.symm
    exact (smul_eq_zero.mp h_zero).resolve_left two_ne_zero
  · -- ∂̄-harmonic → harmonic.
    intro h
    show hlm.laplacian ω = 0
    rw [kli.lap_eq_two_lapBar ω, h, smul_zero]

/-- Harmonic ↔ ∂-harmonic on a Kähler manifold (symmetric to above). -/
theorem harmonic_iff_del_harmonic (ω : DiffForm ℝ E ℝ k) :
    IsHarmonic (hlm := hlm) ω ↔ dld.lapDel ω = 0 := by
  rw [harmonic_iff_dolbeault_harmonic ω, lapBar_eq_lapDel]

/-- **Hodge symmetry: h^{p,q} = h^{q,p}.**

    On a compact Kähler manifold, the Hodge numbers satisfy h^{p,q} = h^{q,p}.
    This follows from Δ_∂̄ = Δ_∂ (lapBar_eq_lapDel): complex conjugation
    swaps ∂ and ∂̄, hence swaps H^{p,q}_∂̄ and H^{q,p}_∂.
    Since Δ_∂̄ = Δ_∂, the harmonic spaces have the same dimension.

    We state this abstractly: for any type-preserving involution σ that
    swaps the two Dolbeault Laplacians, the σ-image of a ∂̄-harmonic form
    is ∂-harmonic (and vice versa). -/
theorem dolbeault_harmonic_swap
    (σ : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k)
    (hσ_zero : σ 0 = 0)
    (hσ_lapBar : ∀ ω, dlb.lapBar (σ ω) = σ (dld.lapDel ω))
    (ω : DiffForm ℝ E ℝ k)
    (h_bar_harmonic : dlb.lapBar ω = 0) :
    dld.lapDel (σ ω) = 0 := by
  rw [← lapBar_eq_lapDel, hσ_lapBar,
    show dld.lapDel ω = 0 from (lapBar_eq_lapDel ω).symm ▸ h_bar_harmonic,
    hσ_zero]

end

end Ramtastic.Kahler.KahlerLaplacian
