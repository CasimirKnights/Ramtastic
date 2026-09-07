/-
  EllipticCurve.lean - elliptic curves over Q: base Tower data.

  An elliptic curve E/ℚ is a smooth projective curve of genus 1 with
  a distinguished rational point O. In Weierstrass form:
    y² = x³ + ax + b,  Δ = -16(4a³ + 27b²) ≠ 0.

  Mathlib provides: WeierstrassCurve, the group law on E(F),
  affine/projective/Jacobian coordinates, division polynomials,
  reduction modulo primes, j-invariant classification.

  This file records the BSD Tower vocabulary for curve coefficients,
  conductors, and local data.
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Basic

namespace Ramtastic.BSD.EllipticCurve

noncomputable section

-- ================================================================
-- I. ELLIPTIC CURVE DATA
-- ================================================================

/-- **Elliptic curve over ℚ in short Weierstrass form.**
    y² = x³ + ax + b with Δ = -16(4a³ + 27b²) ≠ 0.

    This is the starting point for BSD. Every elliptic curve
    over ℚ has a short Weierstrass model (after coordinate change).

    Published: Weierstrass (1882), standardized form. -/
structure EllipticCurveData where
  /-- Coefficient a in y² = x³ + ax + b. -/
  a : ℚ
  /-- Coefficient b in y² = x³ + ax + b. -/
  b : ℚ
  /-- Non-singularity: Δ ≠ 0. -/
  disc_ne_zero : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0

/-- **The discriminant.** -/
def discriminant (E : EllipticCurveData) : ℚ :=
  -(16 * (4 * E.a ^ 3 + 27 * E.b ^ 2))

/-- **Discriminant is nonzero.** -/
theorem disc_nonzero (E : EllipticCurveData) : discriminant E ≠ 0 := by
  unfold discriminant
  intro h
  have : 4 * E.a ^ 3 + 27 * E.b ^ 2 = 0 := by linarith
  exact E.disc_ne_zero this

-- ================================================================
-- II. LOCAL DATA AT PRIMES
-- ================================================================

/-- **Reduction type at a prime p.**
    Good: E has good reduction at p (E mod p is smooth).
    Multiplicative: E has multiplicative reduction (node).
    Additive: E has additive reduction (cusp). -/
inductive ReductionType
  | good
  | multiplicative_split
  | multiplicative_nonsplit
  | additive

/-- **Local data at each prime.**
    For each prime p: the reduction type, the trace of Frobenius a_p,
    and the local Tamagawa number c_p. -/
structure LocalData where
  /-- Trace of Frobenius: a_p = p + 1 - #E(𝔽_p) for good reduction. -/
  trace_frobenius : ℤ
  /-- Reduction type at this prime. -/
  reduction : ReductionType
  /-- Tamagawa number c_p (= 1 for good reduction). -/
  tamagawa : ℕ
  tamagawa_pos : 0 < tamagawa

/-- **Full arithmetic data for an elliptic curve.**
    Bundles the curve with its local data at every prime. -/
structure ArithmeticECData extends EllipticCurveData where
  /-- Local data at each prime. -/
  local_data : ℕ → LocalData
  /-- Conductor: product of bad primes with exponents. -/
  conductor : ℕ
  conductor_pos : 0 < conductor
  /-- Hasse bound at good primes: |a_p| ≤ 2√p. -/
  hasse_bound : ∀ p : ℕ, Nat.Prime p →
    (local_data p).reduction = ReductionType.good →
    ((local_data p).trace_frobenius : ℝ) ^ 2 ≤ 4 * (p : ℝ)

end

end Ramtastic.BSD.EllipticCurve
