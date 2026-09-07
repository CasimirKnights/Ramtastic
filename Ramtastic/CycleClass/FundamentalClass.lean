/-
  FundamentalClass.lean — The fundamental class [Z] of a subvariety Z ⊂ X.

  For a codimension-p subvariety Z ⊂ X, the fundamental class
    [Z] ∈ H^{2p}(X, ℤ)
  is the cohomology class Poincaré-dual to the homology class of Z.

  Construction: via tubular neighborhood + Thom class of normal bundle of Z in X.
  - Z has a tubular neighborhood ν(Z) ≅ N_{Z/X} (normal bundle)
  - τ_{N_{Z/X}} ∈ H^{2p}(Th(N), Th(N)\Z) is the Thom class
  - Excision + tubular neighborhood gives H^{2p}(X, X\Z) ≅ H^{2p}(Th(N), Th(N)\Z)
  - Then map H^{2p}(X, X\Z) → H^{2p}(X) gives [Z]

  Key properties:
  - Linear: [Z₁ + Z₂] = [Z₁] + [Z₂] (for cycles in the same codimension)
  - Multiplicative: [Z₁ ∩ Z₂] = [Z₁] ⌣ [Z₂] (when intersection is transverse)

  In our abstract setup: take the fundamental class as data, with the
  required additivity over algebraic cycles.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Ramtastic.ChowGroups.ChowRing
import Ramtastic.CycleClass.ThomClass

namespace Ramtastic.CycleClass.FundamentalClass

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.ChowGroups.ChowGroup
open Ramtastic.ChowGroups.ChowRing
open Ramtastic.CycleClass.ThomClass

noncomputable section

variable {X : Type*} [VarietyData X] [RatEquivData X]

-- ═══════════════════════════════════════════════════════════════════
-- FUNDAMENTAL CLASS DATA
-- ═══════════════════════════════════════════════════════════════════

/-- Data carrying the fundamental class of subvarieties.
    For each subvariety Z (with given codimension p), provides [Z] ∈ Cohom (2p).
    Linearity over the additive group of cycles is required, plus invariance
    under rational equivalence (so the class descends to A^p). -/
class FundamentalClassData (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] where
  /-- The fundamental class on cycles. For each p, sends a cycle to [Z] ∈ H^{2p}. -/
  fundClass : ∀ p, CycleGroup X p →+ CycleClassData.Cohom (X := X) (p + p)
  /-- Rationally trivial cycles have zero fundamental class.
      This is the precondition for descending to A^p(X). -/
  fundClass_ratTrivial : ∀ p (z : CycleGroup X p),
    z ∈ RatEquivData.ratTrivial p → fundClass p z = 0

-- ═══════════════════════════════════════════════════════════════════
-- DESCEND TO CHOW GROUP
-- ═══════════════════════════════════════════════════════════════════

/-- The fundamental class descends to a map A^p(X) → H^{2p}(X) on the
    Chow group (since it sends rationally-trivial cycles to zero). -/
noncomputable def fundClassOnChow [IntersectionData X] [CycleClassData X]
    [fcd : FundamentalClassData X] (p : ℕ) :
    Chow X p →+ CycleClassData.Cohom (X := X) (p + p) :=
  QuotientAddGroup.lift _ (fcd.fundClass p) (fcd.fundClass_ratTrivial p)

end

end Ramtastic.CycleClass.FundamentalClass
