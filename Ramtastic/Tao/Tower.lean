import Ramtastic.Tao.BoundedPrimeGaps

/-!
Tao/Maynard bounded-gap Tower surface.

This file is Tower-side only. It keeps bounded prime gaps separate from
Hardy-Littlewood asymptotics and from the exact Twin/Polignac rows.
-/

namespace Ramtastic.Tao.Tower

open Ramtastic.Tao.BoundedPrimeGaps

noncomputable section

/-- Non-optional Tower manifest for the bounded-gap layer. -/
structure TaoTowerManifest where
  requirement : TaoBoundedGapTowerRequirement

/-- The manifest exposes the public bounded-gap statement. -/
theorem boundedGaps
    (T : TaoTowerManifest) :
    BoundedGapsStatement :=
  boundedGapsStatement_of_requirement T.requirement

end

end Ramtastic.Tao.Tower
