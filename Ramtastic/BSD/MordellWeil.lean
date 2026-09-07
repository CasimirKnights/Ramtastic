/-
  MordellWeil.lean - Mordell-Weil group vocabulary.

  Mordell (1922): E(ℚ) is finitely generated for curves y² = x³ + k.
  Weil (1928): E(K) is finitely generated for any number field K.

  E(ℚ) ≅ ℤʳ ⊕ T where r = rank, T = torsion (finite).

  This file provides Tower-side algebraic structures for rank and torsion data.
-/

import Mathlib.Tactic
import Ramtastic.BSD.EllipticCurve

namespace Ramtastic.BSD.MordellWeil

open Ramtastic.BSD.EllipticCurve

noncomputable section

-- ================================================================
-- I. THE MORDELL-WEIL GROUP
-- ================================================================

/-- **Mordell-Weil data.**
    The group of rational points, its rank, its torsion.
    Finitely generated: Mordell 1922, Weil 1928.

    This is the ALGEBRAIC side of BSD. The rank r lives here.
    The L-function (ANALYTIC side) lives elsewhere.
    BSD says they agree. -/
structure MordellWeilGroup where
  /-- The type of rational points E(ℚ). -/
  Point : Type*
  [instACG : AddCommGroup Point]
  /-- The rank of the free part. -/
  rank : ℕ
  /-- Torsion subgroup order. Mazur (1977): |T| ∈ {1..10, 12}. -/
  torsion_order : ℕ
  torsion_order_pos : 0 < torsion_order
  /-- Generators: r free generators + torsion generators. -/
  free_generators : Fin rank → Point
  /-- Free generators are independent: no nontrivial ℤ-relation. -/
  free_independent : ∀ (coeffs : Fin rank → ℤ),
    Finset.univ.sum (fun i => coeffs i • free_generators i) = 0 →
    ∀ i, coeffs i = 0
  /-- Free generators and torsion span E(ℚ). -/
  spans : ∀ p : Point, ∃ (coeffs : Fin rank → ℤ) (t : Point),
    (∃ n : ℕ, 0 < n ∧ (n : ℤ) • t = 0) ∧
    p = Finset.univ.sum (fun i => coeffs i • free_generators i) + t

attribute [instance] MordellWeilGroup.instACG

-- ================================================================
-- II. RANK PROPERTIES
-- ================================================================

/-- **Rank zero: all points are torsion.** -/
theorem rank_zero_all_torsion (mw : MordellWeilGroup) (h : mw.rank = 0) :
    ∀ p : mw.Point, ∃ n : ℕ, 0 < n ∧ (n : ℤ) • p = 0 := by
  intro p
  obtain ⟨coeffs, t, ⟨n, hn, ht⟩, hp⟩ := mw.spans p
  -- With rank = 0, Fin mw.rank is empty → Finset.univ is empty → sum is 0
  have hempty : Finset.univ (α := Fin mw.rank) = ∅ := by
    rw [Finset.univ_eq_empty_iff]; exact h ▸ Fin.isEmpty
  have hsum : Finset.univ.sum (fun i : Fin mw.rank => coeffs i • mw.free_generators i) = 0 := by
    rw [hempty, Finset.sum_empty]
  rw [hsum, zero_add] at hp
  rw [hp]
  exact ⟨n, hn, ht⟩

-- ================================================================
-- III. THE BSD ALGEBRAIC RANK
-- ================================================================

/-- **The algebraic rank.** This is what BSD equates to the analytic rank. -/
def algebraic_rank (mw : MordellWeilGroup) : ℕ := mw.rank

end

end Ramtastic.BSD.MordellWeil
