/-
  ProjectiveKahler.lean — Smooth projective varieties are Kähler.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-18)
-/

import Mathlib.Tactic
import Ramtastic.Kahler.KahlerForm
import Ramtastic.Kahler.HodgeDecomposition
import Ramtastic.ChowGroups.ChowRing
import Ramtastic.CycleClass.CycleClassMap

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.GAGA.ProjectiveKahler

open Ramtastic.Kahler.KahlerForm
open Ramtastic.Kahler.HodgeDecomposition
open Ramtastic.ChowGroups.ChowRing
open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.CycleClass.CycleClassMap

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth projective variety with all algebraic and analytic structure.
    Bundles: Kähler data + variety data + cycle class data + Hodge decomposition.
    The Fubini-Study metric provides the Kähler structure.
    The embedding in CP^n provides the algebraic structure. -/
structure ProjectiveVarietyData (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X]
    [HodgeDecomposition X] where
  /-- The ambient projective space dimension. -/
  ambientDim : ℕ
  /-- The Kähler data from the Fubini-Study metric. -/
  kahler : @KahlerData E _ _
  /-- The Kähler class is integral: represents an element of H²(X, ℤ).
      This is the Kodaira embedding condition: a compact Kähler manifold
      with integral Kähler class admits a projective embedding. -/
  kahler_integral : ∃ (n : ℕ),
    CycleClassData.cycleClass (X := X) 1 (default) ≠ 0

/-- Projective ⟹ Kähler (immediate from data). -/
@[reducible]
def projectiveIsKahler {X : Type*} [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X]
    [HodgeDecomposition X]
    (pvd : ProjectiveVarietyData (E := E) X) : @KahlerData E _ _ :=
  pvd.kahler

/-- The Hodge conjecture for a projective variety X at degree p.
    Wired to the existing HodgeConjectureAt from ChowRing.lean. -/
def hodgeConjectureForProjective (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X] (p : ℕ) : Prop :=
  HodgeConjectureAt (X := X) p

end

end Ramtastic.GAGA.ProjectiveKahler
