import Mathlib.Tactic
import Ramtastic.HardyLittlewood.PrimePairAsymptotic

/-!
Tao/Maynard bounded-prime-gap Tower requirements.

This is the bounded-gap part of the Tower.  It is not the Hardy-Littlewood
asymptotic layer and not the exact Polignac/Twin airlock.
-/

namespace Ramtastic.Tao.BoundedPrimeGaps

open Ramtastic.HardyLittlewood.PrimePairAsymptotic

noncomputable section

/-- A prime `p` begins a prime gap of size at most `K`. -/
def BoundedPrimeGapAtMost (K p : Nat) : Prop :=
  Nat.Prime p ∧ ∃ q : Nat, Nat.Prime q ∧ p < q ∧ q - p ≤ K

/-- Tao/Maynard bounded gaps statement. -/
def BoundedGapsStatement : Prop :=
  ∃ K : Nat, 0 < K ∧ Set.Infinite { p : Nat | BoundedPrimeGapAtMost K p }

/-- Non-optional Tower requirement for bounded prime gaps. -/
structure TaoBoundedGapTowerRequirement where
  K : Nat
  K_pos : 0 < K
  infinitely_many_bounded_gaps :
    Set.Infinite { p : Nat | BoundedPrimeGapAtMost K p }

/-- A Tower requirement reads as the public bounded-gap statement. -/
theorem boundedGapsStatement_of_requirement
    (T : TaoBoundedGapTowerRequirement) :
    BoundedGapsStatement :=
  ⟨T.K, T.K_pos, T.infinitely_many_bounded_gaps⟩

/-- Exact infinitude of one prime-pair row gives bounded gaps with bound `2*k`. -/
theorem boundedGaps_of_infinite_exact_row
    {k : Nat}
    (hk : 1 ≤ k)
    (hrow : Set.Infinite (primePairBasePrimes k)) :
    BoundedGapsStatement := by
  refine ⟨2 * k, by omega, ?_⟩
  refine hrow.mono ?_
  intro p hp
  simp only [Set.mem_setOf_eq]
  unfold primePairBasePrimes PrimePairAtGap at hp
  exact ⟨hp.1, p + 2 * k, hp.2, by omega, by omega⟩

end

end Ramtastic.Tao.BoundedPrimeGaps
