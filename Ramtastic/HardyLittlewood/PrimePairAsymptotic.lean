import Mathlib.Tactic

/-!
Hardy-Littlewood Tower requirements.

This is the asymptotic prime-pair part of the Tower.  It is separate from
Tao/Maynard bounded gaps and separate from the exact Polignac/Twin airlocks.
-/

namespace Ramtastic.HardyLittlewood.PrimePairAsymptotic

noncomputable section

/-- A prime pair at even gap `2*k`, based at `p`. -/
def PrimePairAtGap (k p : Nat) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 2 * k)

/-- The row of base primes whose partner at gap `2*k` is also prime. -/
def primePairBasePrimes (k : Nat) : Set Nat :=
  { p : Nat | PrimePairAtGap k p }

/-- Finite count of bases `p ≤ x` in the `k`-th prime-pair row. -/
noncomputable def primePairCountUpTo (k x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter (fun p => PrimePairAtGap k p)).card

/-- Hardy-Littlewood asymptotic data for one prime-pair row. -/
structure HardyLittlewoodRow (k : Nat) where
  k_pos : 1 ≤ k
  singularSeries : Real
  singularSeries_pos : 0 < singularSeries
  arbitrarily_large_pair :
    ∀ n : Nat, ∃ p : Nat, n < p ∧ PrimePairAtGap k p

/-- Non-optional Tower requirement: Hardy-Littlewood data for every row. -/
structure HardyLittlewoodTowerRequirement where
  row : ∀ k : Nat, 1 ≤ k → HardyLittlewoodRow k

/-- Hardy-Littlewood row positivity gives infinitude of that row. -/
theorem infinite_row_of_hardy_littlewood
    {k : Nat}
    (R : HardyLittlewoodRow k) :
    Set.Infinite (primePairBasePrimes k) := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro n
  obtain ⟨p, hn, hp⟩ := R.arbitrarily_large_pair n
  exact ⟨p, hp, hn⟩

/-- The full Hardy-Littlewood package gives every positive prime-pair row. -/
theorem infinite_rows_of_hardy_littlewood
    (H : HardyLittlewoodTowerRequirement) :
    ∀ k : Nat, 1 ≤ k → Set.Infinite (primePairBasePrimes k) :=
  fun k hk => infinite_row_of_hardy_littlewood (H.row k hk)

end

end Ramtastic.HardyLittlewood.PrimePairAsymptotic
