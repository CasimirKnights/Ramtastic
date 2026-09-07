/-
  CycleClassMap.lean — The cycle class map cl : A^p(X) → H^{2p}(X).

  The cycle class map is the central bridge between algebraic geometry
  (Chow groups, A^p(X)) and topology/Hodge theory (cohomology, H^{2p}(X)).

  Construction (abstract):
    A cycle Σ nᵢ Zᵢ in CycleGroup X p maps to Σ nᵢ [Zᵢ] in H^{2p}(X)
  where [Zᵢ] is the fundamental class of Zᵢ (from FundamentalClassData).

  This is FundamentalClass.fundClassOnChow viewed as the cycle class map.

  The cycle class map is the cycleClass field of CycleClassData.
  We prove that fundClassOnChow satisfies the structural properties needed.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Ramtastic.CycleClass.FundamentalClass

namespace Ramtastic.CycleClass.CycleClassMap

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.ChowGroups.ChowGroup
open Ramtastic.ChowGroups.ChowRing
open Ramtastic.CycleClass.FundamentalClass

noncomputable section

variable {X : Type*} [VarietyData X] [RatEquivData X] [IntersectionData X]

-- ═══════════════════════════════════════════════════════════════════
-- THE CYCLE CLASS MAP (from FundamentalClassData)
-- ═══════════════════════════════════════════════════════════════════

/-- The cycle class map cl : A^p(X) → H^{2p}(X) — derived from the fundamental
    class map descending to the Chow quotient. This is the function that
    instantiates `CycleClassData.cycleClass`. -/
noncomputable def cycleClassMap [CycleClassData X] [FundamentalClassData X] (p : ℕ) :
    Chow X p →+ CycleClassData.Cohom (X := X) (p + p) :=
  fundClassOnChow p

-- ═══════════════════════════════════════════════════════════════════
-- BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- cl(0) = 0 (additive structure). -/
theorem cycleClassMap_zero [CycleClassData X] [FundamentalClassData X] (p : ℕ) :
    cycleClassMap (X := X) p 0 = 0 := map_zero _

/-- cl(α + β) = cl(α) + cl(β) (additivity). -/
theorem cycleClassMap_add [CycleClassData X] [FundamentalClassData X] (p : ℕ)
    (α β : Chow X p) :
    cycleClassMap (X := X) p (α + β) =
      cycleClassMap (X := X) p α + cycleClassMap (X := X) p β := map_add _ _ _

/-- cl(-α) = -cl(α) (negation). -/
theorem cycleClassMap_neg [CycleClassData X] [FundamentalClassData X] (p : ℕ)
    (α : Chow X p) :
    cycleClassMap (X := X) p (-α) = -cycleClassMap (X := X) p α := map_neg _ _

/-- The image of the cycle class map. The Hodge conjecture is the statement
    that this image, after ℚ-tensoring, contains all (p,p)-Hodge classes. -/
def cycleClassImage [CycleClassData X] [FundamentalClassData X] (p : ℕ) :
    Set (CycleClassData.Cohom (X := X) (p + p)) :=
  Set.range (cycleClassMap (X := X) p)

/-- The image always contains 0. -/
theorem zero_mem_cycleClassImage [CycleClassData X] [FundamentalClassData X] (p : ℕ) :
    (0 : CycleClassData.Cohom (X := X) (p + p)) ∈ cycleClassImage (X := X) p :=
  ⟨0, cycleClassMap_zero p⟩

end

end Ramtastic.CycleClass.CycleClassMap
