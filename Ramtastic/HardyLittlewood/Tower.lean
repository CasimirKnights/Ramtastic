import Ramtastic.HardyLittlewood.PrimePairAsymptotic

/-!
Hardy-Littlewood Tower surface.

This file is Tower-side only. It packages the prime-pair asymptotic requirement
as a non-optional manifest entry and exposes the qualitative row infinitude
that downstream exact-gap airlocks can compare against.
-/

namespace Ramtastic.HardyLittlewood.Tower

open Ramtastic.HardyLittlewood.PrimePairAsymptotic

noncomputable section

/-- Non-optional Tower manifest for the Hardy-Littlewood prime-pair layer. -/
structure HardyLittlewoodTowerManifest where
  requirement : HardyLittlewoodTowerRequirement

/-- The manifest exposes the row data without weakening it. -/
def HardyLittlewoodTowerManifest.row
    (H : HardyLittlewoodTowerManifest)
    (k : Nat)
    (hk : 1 <= k) :
    HardyLittlewoodRow k :=
  H.requirement.row k hk

/-- The manifest entails qualitative infinitude in every positive row. -/
theorem allRowsInfinite
    (H : HardyLittlewoodTowerManifest) :
    forall k : Nat, 1 <= k -> Set.Infinite (primePairBasePrimes k) :=
  infinite_rows_of_hardy_littlewood H.requirement

end

end Ramtastic.HardyLittlewood.Tower
