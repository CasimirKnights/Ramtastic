/-
  TateShafarevich.lean - Tate-Shafarevich, Tamagawa, and period vocabulary.

  Sha(E/ℚ) = ker(H¹(ℚ, E) → Π_v H¹(ℚ_v, E))

  The elements of Sha are torsors (principal homogeneous spaces)
  for E that have points everywhere locally but not globally.
  Sha measures the failure of the local-global principle.

  BSD strong form requires |Sha| < ∞ (conjecturally true).
  The order |Sha| appears in the leading coefficient formula.

  Tate (1962), Shafarevich (1962). Cassels proved Sha has
  alternating pairing → |Sha| is a perfect square (when finite).

  This file records Tower-side arithmetic invariant structures for BSD
  statement surfaces.
-/

import Mathlib.Tactic
import Ramtastic.BSD.EllipticCurve

namespace Ramtastic.BSD.TateShafarevich

open Ramtastic.BSD.EllipticCurve

noncomputable section

-- ================================================================
-- I. THE TATE-SHAFAREVICH GROUP
-- ================================================================

/-- **Tate-Shafarevich data.**
    The group Sha(E/ℚ) and its properties.

    Sha measures the obstruction to the local-global principle:
    torsors with points everywhere locally but not globally.

    Finiteness of Sha is conjectural (part of strong BSD).
    When finite: |Sha| is a perfect square (Cassels).

    Fields are hypotheses from the finiteness conjecture. -/
structure ShaData where
  /-- Order of Sha (assumed finite for BSD). -/
  sha_order : ℕ
  sha_pos : 0 < sha_order
  /-- Sha order is a perfect square (Cassels' alternating pairing). -/
  sha_square : ∃ m : ℕ, sha_order = m ^ 2

-- ================================================================
-- II. TAMAGAWA NUMBERS
-- ================================================================

/-- **Tamagawa data at bad primes.**
    For each bad prime p, the Tamagawa number c_p = [E(ℚ_p) : E₀(ℚ_p)]
    counts connected components of the Néron model's special fiber.
    c_p = 1 for good reduction primes.

    The product ∏ c_p appears in the BSD formula.

    Néron (1964), Ogg-Shafarevich formula. -/
structure TamagawaData extends ArithmeticECData where
  /-- Product of Tamagawa numbers ∏ c_p. -/
  tamagawa_product : ℕ
  tamagawa_product_pos : 0 < tamagawa_product
  /-- Bad primes: those with non-good reduction. All divide conductor. -/
  bad_primes : Finset ℕ
  /-- The product equals the product of local Tamagawa numbers at bad primes. -/
  tamagawa_is_product : tamagawa_product =
    bad_primes.prod (fun p => (toArithmeticECData.local_data p).tamagawa)
  /-- Good primes have Tamagawa number 1 (don't contribute to product). -/
  good_tamagawa_one : ∀ p, p ∉ bad_primes →
    (toArithmeticECData.local_data p).tamagawa = 1

-- ================================================================
-- III. THE REAL PERIOD
-- ================================================================

/-- **The real period Ω.**
    Ω = ∫_{E(ℝ)} |ω| where ω = dx/(2y+a₁x+a₃) is the Néron
    differential. Ω > 0.

    The period appears in the BSD formula as the archimedean
    local factor.

    Published: standard, see Silverman AEC Ch. V. -/
structure PeriodData where
  /-- The real period. -/
  omega : ℝ
  omega_pos : 0 < omega

end

end Ramtastic.BSD.TateShafarevich
