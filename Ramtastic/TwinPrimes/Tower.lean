import Ramtastic.TwinPrimes.Statement

/-!
Twin-prime Tower surface.

This file is Tower-side only. It keeps the exact `k = 1` prime-pair row as its
own airlock instead of burying it inside Polignac or Cascade machinery.
-/

namespace Ramtastic.TwinPrimes.Tower

open Ramtastic.TwinPrimes.Statement

noncomputable section

/-- Non-optional Tower manifest for the twin-prime row. -/
structure TwinPrimeTowerManifest where
  requirement : TwinPrimeTowerRequirement

/-- The manifest exposes the public twin-prime statement. -/
theorem twinPrimes
    (T : TwinPrimeTowerManifest) :
    TwinPrimeStatement :=
  T.requirement.twin_primes

end

end Ramtastic.TwinPrimes.Tower
