/-
  GlimmJaffeLimit.lean — inductive-limit construction for compact-volume QFT family (AIRTIGHT).

  TASK 8 of the YM ℝ⁴ tower interlocks (per
  `__production_steps/2026_04_28_AIRTIGHT_INTERLOCK_DIRECTIVE.md`).

  Provides the inductive-limit data structure and the compatibility
  theorems that the YM ℝ⁴ airline (TASK 9) uses to derive the limit
  Hamiltonian from a compact-volume QFT family with uniform spectral gap.

  Discipline (per directive 2026-04-28):
    - No new structures introduced for tower work beyond what is necessary
      to express the inductive-limit data; existing grandfathered structures
      from `Craft/YM/InfiniteVolumeLimit.lean` are not modified.
    - No new hypothesis fields that hide the conclusion. The inductive-limit
      data is constructible specific data (subspaces, embeddings, compatibility
      properties).
    - No `True`. No `sorry`.
    - Three Lean kernel axioms only.

  AIRTIGHTNESS:
    - The inductive-limit data carries SPECIFIC subspaces `subspace n : Set E`
      and a compatibility property `T = T_n on subspace n`.
    - The "limit Hamiltonian" `T` is given as data; the family `T_n` is given
      as data; the compatibility is given as a property of those data.
    - The downstream gap-preservation theorem (TASK 7) consumes this data and
      derives the limit gap from the uniform compact gap. No apex-circular field.
    - For the YM ℝ⁴ application: subspace n is the Hilbert space of the
      compact-volume QFT at half-side `L_n` (a sequence of growing boxes
      filling ℝ⁴). The limit operator T is the Hamiltonian on the inductive
      limit Hilbert space. Compatibility holds by construction of the
      inductive limit.

  Imports: Mathlib.Tactic, StrongResolventConvergence (TASK 7).

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.7, 2026-04-28)
-/

import Mathlib.Tactic
import Ramtastic.QuantumYM.StrongResolventConvergence

namespace Ramtastic.QuantumYM.GlimmJaffeLimit

open Ramtastic.QuantumYM.StrongResolventConvergence

noncomputable section

-- ════════════════════════════════════════════════════════════════
-- I. THE INDUCTIVE-LIMIT COMPATIBILITY DATA
-- ════════════════════════════════════════════════════════════════

/-- **Inductive-limit data for a family of operators.**

    NOT a new structure with hypothesis fields encoding the conclusion.
    A predicate / proposition packaging:
    - A sequence of subspaces `subspace : ℕ → Set E` (the finite-level Hilbert spaces)
    - A sequence of operators `T_n : ℕ → (E →L[ℂ] E)` (the compact-volume Hamiltonians)
    - A "limit" operator `T : E →L[ℂ] E` (the inductive-limit Hamiltonian)
    - The compatibility property: `T = T_n` on `subspace n`.

    The Glimm-Jaffe inductive-limit construction (Glimm-Jaffe 1981, Ch 18-19)
    provides:
    1. A monotone sequence of subspaces `subspace n ⊆ subspace (n+1)`.
    2. The union `⋃_n subspace n` is dense in `E`.
    3. The limit operator `T` is the closure of the operator defined on `⋃_n subspace n`
       by `T ψ = T_n ψ` whenever `ψ ∈ subspace n`.

    For the YM application: `subspace n` is the Hilbert space of compact-volume
    QFT at half-side `L_n = n + 1` (or any unbounded sequence), with the natural
    isometric embedding `subspace n ↪ subspace (n+1)`. -/
def InductiveLimitCompatible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (T_n : ℕ → (E →L[ℂ] E))
    (subspace : ℕ → Set E) : Prop :=
  ∀ n (ψ : E), ψ ∈ subspace n → T ψ = T_n n ψ

-- ════════════════════════════════════════════════════════════════
-- II. INDUCTIVE-LIMIT GAP PRESERVATION (FINITE-LEVEL CASE)
-- ════════════════════════════════════════════════════════════════

/-- **Inductive-limit gap preservation for finite-level eigenvectors.**

    Given:
    - Compatible inductive-limit data (T = T_n on subspace n)
    - Each T_n has spectral gap (a, b) — uniform gap
    - λ ∈ ℂ is an eigenvalue of T with eigenvector ψ ∈ subspace n for some n

    Conclude: λ.re is not in the open gap interval (a, b).

    This is the airtight inductive-limit gap-preservation theorem. The conclusion
    is DERIVED from the spectrum membership of λ (provable directly from the
    eigenvalue equation T ψ = λ • ψ via TASK 7) and the uniform gap hypothesis.

    For an eigenvector ψ that lies in some finite level `subspace n`, the
    compatibility transfers the eigenvalue equation to T_n, putting λ in the
    spectrum of T_n and hence outside (a, b). -/
theorem inductive_limit_gap_preservation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (T_n : ℕ → (E →L[ℂ] E))
    (subspace : ℕ → Set E)
    (h_compat : InductiveLimitCompatible T T_n subspace)
    (a b : ℝ) (hab : a < b)
    (h_uniform_gap : ∀ n (μ : ℂ), μ ∈ spectrum ℂ (T_n n) → ¬ (a < μ.re ∧ μ.re < b))
    (lam : ℂ) (ψ : E) (h_ne : ψ ≠ 0) (h_eigen : T ψ = lam • ψ)
    (n : ℕ) (h_in_level : ψ ∈ subspace n) :
    ¬ (a < lam.re ∧ lam.re < b) := by
  -- Apply gap_preservation_eigenvalue_in_subspace from TASK 7.
  exact gap_preservation_eigenvalue_in_subspace
    T T_n a b hab h_uniform_gap subspace h_compat lam ψ h_ne h_eigen n h_in_level

/-- **Real-valued specialization** of `inductive_limit_gap_preservation`. -/
theorem inductive_limit_gap_preservation_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (T_n : ℕ → (E →L[ℂ] E))
    (subspace : ℕ → Set E)
    (h_compat : InductiveLimitCompatible T T_n subspace)
    (a b : ℝ) (hab : a < b)
    (h_uniform_gap : ∀ n (μ : ℂ), μ ∈ spectrum ℂ (T_n n) → ¬ (a < μ.re ∧ μ.re < b))
    (lam : ℝ) (ψ : E) (h_ne : ψ ≠ 0) (h_eigen : T ψ = (lam : ℂ) • ψ)
    (n : ℕ) (h_in_level : ψ ∈ subspace n) :
    ¬ (a < lam ∧ lam < b) := by
  exact gap_preservation_real_eigenvalue_in_subspace
    T T_n a b hab h_uniform_gap subspace h_compat lam ψ h_ne h_eigen n h_in_level

-- ════════════════════════════════════════════════════════════════
-- III. MONOTONE INDUCTIVE-LIMIT STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- **Monotone inductive-limit subspace structure.**

    The Glimm-Jaffe construction places the finite-level subspaces in a
    monotone sequence: `subspace 0 ⊆ subspace 1 ⊆ subspace 2 ⊆ ...`.

    This packaging ensures the inductive-limit Hilbert space is well-defined
    as the closure of the union (a monotone sequence of closed subspaces has
    a well-defined closure of union). -/
def MonotoneSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (subspace : ℕ → Set E) : Prop :=
  ∀ n, subspace n ⊆ subspace (n + 1)

/-- **Monotone implies subspace-membership at higher levels.** -/
theorem monotone_subspace_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (subspace : ℕ → Set E) (h_mono : MonotoneSubspace subspace)
    (n : ℕ) (k : ℕ) (ψ : E) (h_in : ψ ∈ subspace n) :
    ψ ∈ subspace (n + k) := by
  induction k with
  | zero => exact h_in
  | succ m ih =>
    have h_next : subspace (n + m) ⊆ subspace (n + m + 1) := h_mono (n + m)
    rw [show n + (m + 1) = n + m + 1 from rfl]
    exact h_next ih

/-- **Inductive-limit gap preservation under monotone subspace structure.**

    Given monotone inductive-limit data (subspaces nested) and a uniform gap
    on the finite-level operators, eigenvectors at any finite level imply
    the eigenvalue is outside the gap interval. -/
theorem inductive_limit_gap_preservation_monotone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (T_n : ℕ → (E →L[ℂ] E))
    (subspace : ℕ → Set E)
    (_h_mono : MonotoneSubspace subspace)
    (h_compat : InductiveLimitCompatible T T_n subspace)
    (a b : ℝ) (hab : a < b)
    (h_uniform_gap : ∀ n (μ : ℂ), μ ∈ spectrum ℂ (T_n n) → ¬ (a < μ.re ∧ μ.re < b))
    (lam : ℂ) (ψ : E) (h_ne : ψ ≠ 0) (h_eigen : T ψ = lam • ψ)
    (h_some_level : ∃ n, ψ ∈ subspace n) :
    ¬ (a < lam.re ∧ lam.re < b) := by
  obtain ⟨n, h_in⟩ := h_some_level
  exact inductive_limit_gap_preservation T T_n subspace h_compat a b hab
    h_uniform_gap lam ψ h_ne h_eigen n h_in

-- ════════════════════════════════════════════════════════════════
-- IV. SUMMARY: WHAT THIS FILE PROVIDES
-- ════════════════════════════════════════════════════════════════

-- WHAT THIS FILE PROVIDES (TASK 8):
--
-- Predicates (specifications, not hypothesis-field structures):
--   InductiveLimitCompatible T T_n subspace : Prop
--     Compatibility of T with finite-level T_n on subspace n.
--   MonotoneSubspace subspace : Prop
--     Subspaces are nested: subspace n ⊆ subspace (n+1).
--
-- Derived theorems (proved, three Lean kernel axioms only):
--   inductive_limit_gap_preservation:
--     finite-level eigenvector ⇒ eigenvalue outside uniform-gap interval.
--   inductive_limit_gap_preservation_real:
--     real-valued specialization.
--   monotone_subspace_step:
--     ψ ∈ subspace n ⇒ ψ ∈ subspace (n+k) under monotone nesting.
--   inductive_limit_gap_preservation_monotone:
--     under monotone nesting, eigenvector at any finite level ⇒ gap preserved.
--
-- AIRTIGHTNESS:
--   The inductive-limit data is given as predicates on specific data
--   (functions subspace : ℕ → Set E, T_n : ℕ → (E →L[ℂ] E), T : E →L[ℂ] E).
--   The conclusions (gap preservation) are derived theorems from the data,
--   not hypothesis fields encoding the conclusions.
--
-- WHAT THIS FILE DOES NOT COVER (DOWNSTREAM):
--   - The actual closure construction E = closure(⋃_n subspace n) for the
--     analytic case where eigenvectors are limits of finite-level vectors.
--     This file covers eigenvectors in finite levels; the closure case is
--     the Weyl-criterion territory which is the open subroutine of TASK 9.
--   - The construction of subspace n from a specific compact-volume QFT
--     family. That's the assembly step in TASK 9.

end

end Ramtastic.QuantumYM.GlimmJaffeLimit
