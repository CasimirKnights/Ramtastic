/-
  ChowRing.lean — The Chow ring A^*(X) = ⊕_p A^p(X).

  The direct sum of all Chow groups, with the intersection product,
  forms a graded commutative ring. This is the algebraic side of
  the Hodge conjecture — the cycle class map cl : A^* → H^* sends
  this ring to the cohomology ring.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ChowGroups.IntersectionProduct

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.ChowGroups.ChowRing

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.ChowGroup
open Ramtastic.ChowGroups.IntersectionProduct

noncomputable section

variable {X : Type*} [vd : VarietyData X] [req : RatEquivData X]
  [idata : IntersectionData X] {p q : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- THE CHOW RING AS A GRADED STRUCTURE
-- ═══════════════════════════════════════════════════════════════════

/-- The degree-p component of the Chow ring is A^p. -/
def chowRingComponent (p : ℕ) : Type _ := Chow X p

instance (p : ℕ) : AddCommGroup (chowRingComponent (X := X) p) :=
  inferInstanceAs (AddCommGroup (Chow X p))

/-- The product of degree-p and degree-q elements lives in degree p+q. -/
def gradedMul (a : chowRingComponent (X := X) p) (b : chowRingComponent (X := X) q) :
    chowRingComponent (X := X) (p + q) :=
  interChow a b

-- ═══════════════════════════════════════════════════════════════════
-- THE CYCLE CLASS MAP TARGET
-- ═══════════════════════════════════════════════════════════════════

/-- The cycle class map data: sends Chow classes to cohomology.
    This is the bridge between the algebraic side (Chow groups)
    and the analytic side (de Rham/Hodge cohomology).
    The Hodge conjecture: the image spans all Hodge classes. -/
class CycleClassData (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] where
  /-- The target cohomology groups H^{2p}. -/
  Cohom : (k : ℕ) → Type*
  [cohom_addCommGroup : ∀ k, AddCommGroup (Cohom k)]
  [cohom_module : ∀ k, Module ℚ (Cohom k)]
  /-- The cycle class map cl : A^p → H^{2p}. -/
  cycleClass : ∀ p, Chow X p →+ Cohom (p + p)
  /-- cl is nonzero: there exist nontrivial cycle classes. -/
  cl_nontrivial : ∃ (p : ℕ) (a : Chow X p), cycleClass p a ≠ 0

attribute [reducible, instance] CycleClassData.cohom_addCommGroup CycleClassData.cohom_module

-- ═══════════════════════════════════════════════════════════════════
-- THE HODGE CONJECTURE CONNECTION
-- ═══════════════════════════════════════════════════════════════════

/-- A Hodge class (in the abstract sense): an element of H^{2p}
    that lies in the (p,p)-component of the Hodge decomposition.
    This is what the Generator's HodgeClass structure captures. -/
class HodgeClassData (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] where
  /-- The set of Hodge classes in H^{2p}. -/
  isHodge : ∀ p, Set (CycleClassData.Cohom (X := X) (p + p))
  /-- Cycle classes are Hodge: im(cl) ⊆ Hodge classes. -/
  cl_is_hodge : ∀ p (a : Chow X p),
    CycleClassData.cycleClass p a ∈ isHodge p

/-- **The Hodge Conjecture at degree p** (rational form): every Hodge class
    in H^{2p}(X, ℚ) lies in the ℚ-linear span of cycle class images.

    UPDATED 2026-04-16: Changed from set-level containment
    `h ∈ Set.range (cycleClass p)` (which would be the INTEGER Hodge conjecture)
    to `h ∈ Submodule.span ℚ (Set.range (cycleClass p))` (the rational form).
    This is the standard Hodge conjecture for varieties over ℚ. -/
def HodgeConjectureAt [CycleClassData X] [HodgeClassData X] (p : ℕ) : Prop :=
  ∀ h ∈ HodgeClassData.isHodge (X := X) p,
    h ∈ Submodule.span ℚ (Set.range (CycleClassData.cycleClass (X := X) p))

/-- **The full Hodge Conjecture**: holds at all degrees. -/
def HodgeConjecture [CycleClassData X] [HodgeClassData X] : Prop :=
  ∀ p, HodgeConjectureAt (X := X) p

/-- If the cycle class map is surjective at degree p, Hodge holds at p. -/
theorem surjective_implies_hodge [CycleClassData X] [HodgeClassData X] (p : ℕ)
    (h : Function.Surjective (CycleClassData.cycleClass (X := X) p)) :
    HodgeConjectureAt (X := X) p := by
  intro α _
  exact Submodule.subset_span (h α)

end

end Ramtastic.ChowGroups.ChowRing
