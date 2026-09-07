import Mathlib.Tactic
import Ramtastic.HardyLittlewood.PrimePairAsymptotic
import Ramtastic.Tao.BoundedPrimeGaps
import Ramtastic.TwinPrimes.Statement

/-!
Polignac Tower airlock requirement.

Polignac is the exact-row requirement: every positive even gap has infinitely
many prime pairs.  Twin primes are a separate Tower requirement, and also the
`k = 1` row of Polignac.
-/

namespace Ramtastic.Polignac.Statement

open Ramtastic.HardyLittlewood.PrimePairAsymptotic
open Ramtastic.Tao.BoundedPrimeGaps
open Ramtastic.TwinPrimes.Statement

noncomputable section

/-- Polignac: every positive even gap has infinitely many prime pairs. -/
def PolignacStatement : Prop :=
  ∀ k : Nat, 1 ≤ k → Set.Infinite (primePairBasePrimes k)

/-- Non-optional Tower requirement for Polignac. -/
structure PolignacTowerRequirement where
  polignac : PolignacStatement

/-- Polignac implies the twin-prime Tower statement. -/
theorem twinPrime_of_polignac
    (h : PolignacStatement) :
    TwinPrimeStatement :=
  h 1 (by norm_num)

/-- Polignac implies Tao/Maynard bounded gaps. -/
theorem boundedGaps_of_polignac
    (h : PolignacStatement) :
    BoundedGapsStatement :=
  boundedGaps_of_infinite_exact_row (k := 1) (by norm_num)
    (twinPrime_of_polignac h)

/-- A Polignac Tower requirement exposes the separate twin-prime requirement. -/
def PolignacTowerRequirement.toTwinPrimeRequirement
    (P : PolignacTowerRequirement) :
    TwinPrimeTowerRequirement where
  twin_primes := twinPrime_of_polignac P.polignac

end

end Ramtastic.Polignac.Statement
