import Mathlib.Tactic
import Ramtastic.HardyLittlewood.PrimePairAsymptotic

/-!
Twin-prime Tower airlock requirement.
-/

namespace Ramtastic.TwinPrimes.Statement

open Ramtastic.HardyLittlewood.PrimePairAsymptotic

noncomputable section

/-- Twin primes are the `k = 1` exact prime-pair row. -/
def TwinPrimeStatement : Prop :=
  Set.Infinite (primePairBasePrimes 1)

/-- Non-optional Tower requirement for the twin-prime row. -/
structure TwinPrimeTowerRequirement where
  twin_primes : TwinPrimeStatement

end

end Ramtastic.TwinPrimes.Statement
