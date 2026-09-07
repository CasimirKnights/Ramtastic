import Ramtastic.BSD.ArithmeticGAGA
import Ramtastic.BSD.BSDFormula

/-!
BSD public statement surface.

This is Tower-side statement vocabulary.  It names the weak and strong BSD
targets in the arithmetic objects already used by the Tower.
-/

namespace Ramtastic.BSD.Statement

open Ramtastic.BSD.ArithmeticGAGA
open Ramtastic.BSD.BSDFormula

noncomputable section

/-- The weak BSD rank equality in Tower arithmetic vocabulary. -/
def WeakRankStatement (A : BSDArithmeticGAGAComparison) : Prop :=
  A.mordellWeil.mw.rank = A.curve.analytic.analytic_rank

/-- The analytic leading coefficient at the central point. -/
def analyticLeadingCoefficient (A : BSDArithmeticGAGAComparison) : Real :=
  iteratedDeriv A.curve.analytic.analytic_rank A.curve.analytic.L 1 /
    (Nat.factorial A.curve.analytic.analytic_rank : Real)

/-- The Tower-side BSD product read from arithmetic invariants. -/
def arithmeticBSDProduct
    (A : BSDArithmeticGAGAComparison)
    (sha_order : Nat)
    (period : Real)
    (tamagawa_product : Nat) : Real :=
  (period * A.mordellWeil.regulator.regulator * (sha_order : Real) *
    (tamagawa_product : Real)) /
    ((A.mordellWeil.mw.torsion_order : Real) ^ 2)

/--
Strong BSD statement surface in Tower vocabulary.  The precise period and
Sha-order witnesses are explicit inputs so the statement cannot hide them in a
definition.
-/
def StrongLeadingCoefficientStatement
    (A : BSDArithmeticGAGAComparison) : Prop :=
  WeakRankStatement A ∧
    ∃ sha_order : Nat, ∃ period : Real, ∃ tamagawa_product : Nat,
      0 < sha_order ∧ 0 < period ∧ 0 < tamagawa_product ∧
        analyticLeadingCoefficient A =
          arithmeticBSDProduct A sha_order period tamagawa_product

/-- Convert the Tower weak statement to the existing `weak_BSD` vocabulary. -/
theorem weakBSD_of_weakRankStatement
    (A : BSDArithmeticGAGAComparison)
    (h : WeakRankStatement A) :
    weak_BSD
      { mw := A.mordellWeil.mw
        ar := A.curve.analytic } := by
  exact h

/-- The Tower endpoint structure for the weak BSD statement. -/
structure WeakBSDTowerStatement where
  arithmetic : BSDArithmeticGAGAComparison
  proof : WeakRankStatement arithmetic

/-- The Tower endpoint structure for the strong BSD leading coefficient form. -/
structure StrongBSDTowerStatement where
  arithmetic : BSDArithmeticGAGAComparison
  proof : StrongLeadingCoefficientStatement arithmetic

end

end Ramtastic.BSD.Statement
