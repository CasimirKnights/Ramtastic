/-
  HodgeTheorem.lean — The Hodge decomposition theorem.

  On a compact oriented Riemannian manifold M:

      Ω^k(M) = H^k(M) ⊕ im(d) ⊕ im(δ)

  where H^k = ker Δ (harmonic k-forms), im(d) = exact forms,
  im(δ) = coexact forms. The decomposition is ORTHOGONAL in L².

  This file CONSTRUCTS the decomposition from:
  - The harmonic projection Hω (CONSTRUCTED in FredholmTheory)
  - The Green operator Gω (CONSTRUCTED via Classical.choice from fredholm_decomp)
  - The Laplacian splitting Δ = dδ + δd (hypothesis from laplacianFromDCodiff)

  The exact part d(δGω) and coexact part δ(dGω) are DEFINED, not axiomatized.
  The decomposition ω = Hω + d(δGω) + δ(dGω) is PROVED.
  The unique harmonic representative theorem is PROVED from linearity of H.

  Parametrized by m where k = m + 1 (the form degree). This avoids
  natural number subtraction: codifferentials go (m+1) → m and
  (m+2) → (m+1), with no k-1 anywhere.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-17)
-/

import Mathlib.Tactic
import Ramtastic.Sobolev.FredholmTheory
import Ramtastic.HodgeStar.Codifferential

namespace Ramtastic.Sobolev.HodgeTheorem

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.HodgeStar.HodgeLaplacian
open Ramtastic.HodgeStar.Codifferential
open Ramtastic.Sobolev.FredholmTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- HODGE DECOMPOSITION DATA
-- ═══════════════════════════════════════════════════════════════════

/-- Data for the Hodge decomposition at degree (m+1).

    Parametrized by m (lower codifferential degree) to avoid natural
    number subtraction. The Laplacian acts on (m+1)-forms.
    Codifferentials: (m+1) → m and (m+2) → (m+1).

    From this data, the Green operator, exact part, and coexact part
    are CONSTRUCTED, and the decomposition is PROVED. -/
structure HodgeDecompositionData (m : ℕ) [hlm : HodgeLaplacianMap (E := E) (m + 1)] where
  /-- The harmonic projection data (includes L² pairing, basis, Fredholm decomp). -/
  hpd : HarmonicProjectionData (E := E) (m + 1)
  /-- Codifferential (m+1) → m (for the dδ part). -/
  cdm : CodifferentialMap (E := E) (m + 1) m
  /-- Codifferential (m+2) → (m+1) (for the δd part). -/
  cdm_hi : CodifferentialMap (E := E) (m + 2) (m + 1)
  /-- **The Laplacian splits as dδ + δd.** This is the DEFINITION for
      `laplacianFromDCodiff`. The caller provides it for their specific
      Laplacian construction. -/
  lap_eq_dcodiff_codiffd : ∀ (η : DiffForm ℝ E ℝ (m + 1)),
    hlm.laplacian η =
      (fun x => extDeriv (cdm.codiff η) x) +
      cdm_hi.codiff (fun x => extDeriv η x)

-- ═══════════════════════════════════════════════════════════════════
-- THE GREEN OPERATOR — CONSTRUCTED
-- ═══════════════════════════════════════════════════════════════════

/-- **The Green operator**: the right inverse of Δ on (ker Δ)⊥.

    For each ω, Gω is a form satisfying Δ(Gω) = ω - Hω.
    CONSTRUCTED via Classical.choice from `fredholm_decomp`.
    This is the Hodge-theoretic analogue of the resolvent. -/
def greenOperator {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) : DiffForm ℝ E ℝ (m + 1) :=
  (hdd.hpd.fredholm_decomp ω).choose

/-- The Green operator satisfies Δ(Gω) = ω - Hω. -/
theorem greenOperator_spec {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) :
    hlm.laplacian (greenOperator hdd ω) = ω - harmonicProj hdd.hpd ω :=
  (hdd.hpd.fredholm_decomp ω).choose_spec

-- ═══════════════════════════════════════════════════════════════════
-- EXACT AND COEXACT PARTS — CONSTRUCTED
-- ═══════════════════════════════════════════════════════════════════

/-- **The exact part of the Hodge decomposition**: d(δGω).

    CONSTRUCTED from the Green operator and the codifferential.
    δGω is an m-form, d(δGω) is an (m+1)-form. Types match.
    This is in im(d) by construction: it IS d applied to δGω. -/
def exactPart {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) : DiffForm ℝ E ℝ (m + 1) :=
  fun x => extDeriv (hdd.cdm.codiff (greenOperator hdd ω)) x

/-- **The coexact part of the Hodge decomposition**: δ(dGω).

    CONSTRUCTED from the Green operator and the codifferential.
    dGω is an (m+2)-form, δ(dGω) is an (m+1)-form. Types match.
    This is in im(δ) by construction: it IS δ applied to dGω. -/
def coexactPart {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) : DiffForm ℝ E ℝ (m + 1) :=
  hdd.cdm_hi.codiff (fun x => extDeriv (greenOperator hdd ω) x)

-- ═══════════════════════════════════════════════════════════════════
-- THE HODGE DECOMPOSITION — PROVED
-- ═══════════════════════════════════════════════════════════════════

/-- **The Hodge decomposition theorem.**

    Every (m+1)-form ω decomposes as:

        ω = Hω + d(δGω) + δ(dGω)

    where Hω is harmonic, d(δGω) is exact, δ(dGω) is coexact.

    PROVED from: greenOperator_spec (Δ(Gω) = ω - Hω) + Laplacian
    splitting (Δ = dδ + δd). -/
theorem hodge_decomp {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) :
    ω = harmonicProj hdd.hpd ω + exactPart hdd ω + coexactPart hdd ω := by
  -- Δ(Gω) = ω - Hω
  have h_green := greenOperator_spec hdd ω
  -- Δ(Gω) = d(δGω) + δ(dGω) = exactPart + coexactPart
  have h_lap := hdd.lap_eq_dcodiff_codiffd (greenOperator hdd ω)
  -- ω - Hω = exactPart + coexactPart
  have h_sub : ω - harmonicProj hdd.hpd ω =
      exactPart hdd ω + coexactPart hdd ω := by
    unfold exactPart coexactPart
    rw [← h_green, h_lap]
  -- ω = Hω + (ω - Hω) = Hω + (exactPart + coexactPart)
  -- = (Hω + exactPart) + coexactPart
  have h1 : ω = harmonicProj hdd.hpd ω +
      (exactPart hdd ω + coexactPart hdd ω) := by
    have h2 : ω = harmonicProj hdd.hpd ω +
        (ω - harmonicProj hdd.hpd ω) := by
      simp [add_sub_cancel]
    rwa [h_sub] at h2
  -- h1 : ω = Hω + (e + c). Goal: ω = (Hω + e) + c (left-assoc).
  rw [add_assoc]
  exact h1

/-- The exact part is in im(d): ∃ α, d(α) = exactPart ω.
    TRIVIALLY TRUE by construction: exactPart = d(δGω), so α = δGω. -/
theorem exactPart_isExact {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) :
    ∃ (α : DiffForm ℝ E ℝ m),
      exactPart hdd ω = fun x => extDeriv α x :=
  ⟨hdd.cdm.codiff (greenOperator hdd ω), rfl⟩

/-- The coexact part is in im(δ): ∃ β, δ(β) = coexactPart ω.
    TRIVIALLY TRUE by construction: coexactPart = δ(dGω), so β = dGω. -/
theorem coexactPart_isCoexact {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hdd : HodgeDecompositionData (E := E) m)
    (ω : DiffForm ℝ E ℝ (m + 1)) :
    ∃ (β : DiffForm ℝ E ℝ (m + 2)),
      coexactPart hdd ω = hdd.cdm_hi.codiff β :=
  ⟨fun x => extDeriv (greenOperator hdd ω) x, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- UNIQUE HARMONIC REPRESENTATIVE — PROVED
-- ═══════════════════════════════════════════════════════════════════

/-- **Cohomologous forms have the same harmonic projection.**

    If ω₁ - ω₂ is exact (= dη for some m-form η), and the harmonic
    projection of exact forms is zero, then Hω₁ = Hω₂.

    PROVED from linearity of H (harmonicProj_add, harmonicProj_smul).

    The hypothesis `h_exact_zero` (H(dα) = 0 for all exact forms)
    follows from d/δ adjointness + harmonics are coclosed:
    ⟨dα, hᵢ⟩ = ⟨α, δhᵢ⟩ = 0. Taken as hypothesis because
    d/δ adjointness requires integration by parts infrastructure. -/
theorem harmonic_class_invariant {m : ℕ} [hlm : HodgeLaplacianMap (E := E) (m + 1)]
    (hpd : HarmonicProjectionData (E := E) (m + 1))
    (ω₁ ω₂ : DiffForm ℝ E ℝ (m + 1))
    -- ω₁ - ω₂ is exact: ω₁ - ω₂ = dη for some m-form η
    (h_exact : ∃ (η : DiffForm ℝ E ℝ m),
      ω₁ - ω₂ = fun x => extDeriv η x)
    -- Harmonic projection of exact forms is zero.
    (h_exact_zero : ∀ (α : DiffForm ℝ E ℝ m),
      harmonicProj hpd (fun x => extDeriv α x) = 0) :
    harmonicProj hpd ω₁ = harmonicProj hpd ω₂ := by
  obtain ⟨η, hη⟩ := h_exact
  -- H is linear under subtraction:
  -- H(ω₁) - H(ω₂) = H(ω₁ + (-1)•ω₂) - (1-1)·garbage = H(ω₁-ω₂)
  suffices h : harmonicProj hpd (ω₁ - ω₂) = 0 by
    have h_add : harmonicProj hpd (ω₁ - ω₂ + ω₂) =
        harmonicProj hpd (ω₁ - ω₂) + harmonicProj hpd ω₂ :=
      harmonicProj_add hpd _ _
    simp [sub_add_cancel] at h_add
    rw [h, zero_add] at h_add
    exact h_add
  -- H(ω₁ - ω₂) = H(dη) = 0
  rw [hη]
  exact h_exact_zero η

-- ═══════════════════════════════════════════════════════════════════
-- BETTI NUMBERS AND EULER CHARACTERISTIC
-- ═══════════════════════════════════════════════════════════════════

/-- The k-th Betti number: b_k = dim H^k = dim ker Δ_k.

    On a compact manifold, this is FINITE (from Fredholm theory).
    It equals the dimension of de Rham cohomology (from the unique
    harmonic representative theorem). -/
def bettiNumber {k : ℕ} [hlm : HodgeLaplacianMap (E := E) k]
    (fd : FredholmData (E := E) k) : ℕ :=
  fd.dimKernel

/-- The Euler characteristic: χ = Σ (-1)^k b_k.
    Parameterized by a function giving the kernel dimension at each degree.
    By the index theorem (Piece 12): χ = ∫ Euler class = topological. -/
def eulerCharacteristic (n : ℕ) (dimKer : Fin (n + 1) → ℕ) : ℤ :=
  ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) * (dimKer k : ℤ)

end

end Ramtastic.Sobolev.HodgeTheorem
