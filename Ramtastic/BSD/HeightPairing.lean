/-
  HeightPairing.lean - Neron-Tate canonical height and regulator vocabulary.

  The canonical height ĥ : E(ℚ) → ℝ satisfies:
  - ĥ(P) ≥ 0 for all P
  - ĥ(P) = 0 iff P is torsion (Néron 1965)
  - ĥ(mP) = m² ĥ(P) (quadraticity)
  - The associated bilinear form ⟨P,Q⟩ = ½(ĥ(P+Q) - ĥ(P) - ĥ(Q))
    is positive definite on E(ℚ)/torsion

  The regulator R = det(⟨P_i, P_j⟩) where P_1,...,P_r are
  generators of E(ℚ)/torsion. R > 0 when rank > 0.
  R appears in the BSD leading coefficient formula.

  This file is Tower-side arithmetic vocabulary for height and regulator data.
-/

import Mathlib.Tactic
import Ramtastic.BSD.MordellWeil

namespace Ramtastic.BSD.HeightPairing

open Ramtastic.BSD.MordellWeil

noncomputable section

-- ================================================================
-- I. THE CANONICAL HEIGHT
-- ================================================================

/-- **Néron-Tate canonical height data.**
    The quadratic form on E(ℚ) that detects torsion.
    Néron (1965), Tate (parallel construction). -/
structure CanonicalHeight (mw : MordellWeilGroup) where
  /-- The canonical height function ĥ : E(ℚ) → ℝ. -/
  height : mw.Point → ℝ
  /-- Non-negativity. -/
  height_nonneg : ∀ P, 0 ≤ height P
  /-- Zero iff torsion (Néron). -/
  height_zero_iff : ∀ P, height P = 0 ↔
    ∃ n : ℕ, 0 < n ∧ (n : ℤ) • P = 0
  /-- Quadraticity: ĥ(nP) = n² ĥ(P). -/
  height_quadratic : ∀ (n : ℤ) (P : mw.Point),
    height (n • P) = n ^ 2 * height P

-- ================================================================
-- II. THE BILINEAR PAIRING
-- ================================================================

/-- **The Néron-Tate bilinear pairing.**
    ⟨P,Q⟩ = ½(ĥ(P+Q) - ĥ(P) - ĥ(Q)).
    Positive definite on E(ℚ)/torsion. -/
def pairing {mw : MordellWeilGroup} (ch : CanonicalHeight mw)
    (P Q : mw.Point) : ℝ :=
  (ch.height (P + Q) - ch.height P - ch.height Q) / 2

-- ================================================================
-- III. THE REGULATOR
-- ================================================================

/-- **The regulator.**
    R = det(⟨P_i, P_j⟩) where P_1,...,P_r are free generators.
    R > 0 when rank > 0. R = 1 when rank = 0 (empty determinant). -/
structure Regulator (mw : MordellWeilGroup) extends CanonicalHeight mw where
  /-- The Gram matrix of the height pairing on free generators. -/
  gram_matrix : Fin mw.rank → Fin mw.rank → ℝ
  gram_is_pairing : ∀ i j,
    gram_matrix i j = pairing toCanonicalHeight (mw.free_generators i) (mw.free_generators j)
  /-- The regulator value. -/
  regulator : ℝ
  /-- Regulator is positive when rank > 0. -/
  regulator_pos : 0 < mw.rank → 0 < regulator
  /-- Regulator is 1 when rank = 0 (convention). -/
  regulator_zero_rank : mw.rank = 0 → regulator = 1

end

end Ramtastic.BSD.HeightPairing
