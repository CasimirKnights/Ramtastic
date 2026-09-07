/-
  RationalEquivalence.lean — Rational equivalence of algebraic cycles.

  Two cycles Z₁, Z₂ ∈ Z^p(X) are rationally equivalent if Z₁ - Z₂
  is a sum of divisors of rational functions on codimension-(p-1) subvarieties.

  Formally: Z ~ 0 if Z = Σ div(fᵢ) where fᵢ are rational functions
  on codimension-(p-1) subvarieties Wᵢ.

  The Chow group A^p = Z^p / ~_rat.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ChowGroups.AlgebraicCycle

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.ChowGroups.RationalEquivalence

open Ramtastic.ChowGroups.AlgebraicCycle

noncomputable section

variable {X : Type*} [vd : VarietyData X]

-- ═══════════════════════════════════════════════════════════════════
-- RATIONAL EQUIVALENCE DATA
-- ═══════════════════════════════════════════════════════════════════

/-- The data of rational equivalence on a variety.
    For each codimension p, specifies which cycles are rationally
    equivalent to zero: the "principal divisors."

    A cycle Z ∈ Z^p is rationally trivial if Z = Σ div(fᵢ) for
    rational functions fᵢ on codimension-(p-1) subvarieties.

    We axiomatize the subgroup of rationally trivial cycles. -/
class RatEquivData (X : Type*) [VarietyData X] where
  /-- The subgroup of rationally trivial p-cycles.
      R^p ⊆ Z^p: cycles that are sums of principal divisors. -/
  ratTrivial : (p : ℕ) → AddSubgroup (CycleGroup X p)


variable [req : RatEquivData X] {p : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- RATIONAL EQUIVALENCE RELATION
-- ═══════════════════════════════════════════════════════════════════

/-- Two cycles are rationally equivalent if their difference is
    rationally trivial: Z₁ ~ Z₂ iff Z₁ - Z₂ ∈ R^p. -/
def RatEquiv (Z₁ Z₂ : CycleGroup X p) : Prop :=
  Z₁ - Z₂ ∈ req.ratTrivial p

/-- Rational equivalence is reflexive: Z ~ Z (since Z - Z = 0 ∈ R^p). -/
theorem ratEquiv_refl (Z : CycleGroup X p) : RatEquiv Z Z := by
  simp [RatEquiv, sub_self, (req.ratTrivial p).zero_mem]

/-- Rational equivalence is symmetric. -/
theorem ratEquiv_symm {Z₁ Z₂ : CycleGroup X p} (h : RatEquiv Z₁ Z₂) :
    RatEquiv Z₂ Z₁ := by
  simp only [RatEquiv] at h ⊢
  rw [show Z₂ - Z₁ = -(Z₁ - Z₂) from by abel]
  exact (req.ratTrivial p).neg_mem h

/-- Rational equivalence is transitive. -/
theorem ratEquiv_trans {Z₁ Z₂ Z₃ : CycleGroup X p}
    (h₁₂ : RatEquiv Z₁ Z₂) (h₂₃ : RatEquiv Z₂ Z₃) :
    RatEquiv Z₁ Z₃ := by
  simp only [RatEquiv] at h₁₂ h₂₃ ⊢
  rw [show Z₁ - Z₃ = (Z₁ - Z₂) + (Z₂ - Z₃) from by abel]
  exact (req.ratTrivial p).add_mem h₁₂ h₂₃

/-- Rational equivalence is an equivalence relation. -/
theorem ratEquiv_equivalence : Equivalence (@RatEquiv X _ _ p) :=
  ⟨ratEquiv_refl, fun h => ratEquiv_symm h, fun h₁ h₂ => ratEquiv_trans h₁ h₂⟩

/-- The setoid from rational equivalence. -/
instance ratEquivSetoid : Setoid (CycleGroup X p) :=
  ⟨RatEquiv, ratEquiv_equivalence⟩

-- ═══════════════════════════════════════════════════════════════════
-- PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- Rational equivalence respects addition: if Z₁ ~ Z₁' and Z₂ ~ Z₂',
    then Z₁ + Z₂ ~ Z₁' + Z₂'. -/
theorem ratEquiv_add {Z₁ Z₁' Z₂ Z₂' : CycleGroup X p}
    (h₁ : RatEquiv Z₁ Z₁') (h₂ : RatEquiv Z₂ Z₂') :
    RatEquiv (Z₁ + Z₂) (Z₁' + Z₂') := by
  simp only [RatEquiv] at h₁ h₂ ⊢
  rw [show (Z₁ + Z₂) - (Z₁' + Z₂') = (Z₁ - Z₁') + (Z₂ - Z₂') from by abel]
  exact (req.ratTrivial p).add_mem h₁ h₂

/-- The zero cycle is rationally equivalent to any rationally trivial cycle. -/
theorem zero_ratEquiv_of_mem {Z : CycleGroup X p}
    (h : Z ∈ req.ratTrivial p) : RatEquiv 0 Z := by
  simp [RatEquiv, h, (req.ratTrivial p).neg_mem h]

/-- The trivial rational equivalence: only zero is rationally trivial.
    This gives A^p = Z^p (no identifications). The simplest instance. -/
@[reducible]
def trivialRatEquiv : RatEquivData X where
  ratTrivial := fun _ => ⊥

/-- The maximal rational equivalence: everything is rationally trivial.
    This gives A^p = 0 (everything identified). -/
@[reducible]
def maximalRatEquiv : RatEquivData X where
  ratTrivial := fun _ => ⊤

end

end Ramtastic.ChowGroups.RationalEquivalence
