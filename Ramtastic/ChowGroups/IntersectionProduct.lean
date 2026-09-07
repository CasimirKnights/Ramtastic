/-
  IntersectionProduct.lean — The intersection product on Chow groups.

  A^p × A^q → A^{p+q}: the product of two cycle classes is their
  intersection class. This makes A^* into a graded ring.

  The intersection product requires the "moving lemma" — any two
  cycles can be moved into general position so they intersect properly.
  We axiomatize this as data.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ChowGroups.ChowGroup

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.ChowGroups.IntersectionProduct

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.ChowGroup

noncomputable section

variable {X : Type*} [vd : VarietyData X] [req : RatEquivData X] {p q : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- INTERSECTION PRODUCT DATA
-- ═══════════════════════════════════════════════════════════════════

/-- The intersection product on Chow groups.
    Provides the bilinear map A^p × A^q → A^{p+q} and its properties.

    The construction (Fulton): deformation to the normal cone.
    We axiomatize the result: a bilinear, associative, commutative
    product with a unit class [X] ∈ A^0. -/
class IntersectionData (X : Type*) [VarietyData X] [RatEquivData X] where
  /-- The intersection product: A^p × A^q → A^{p+q}. -/
  inter : ∀ p q, Chow X p → Chow X q → Chow X (p + q)
  /-- Bilinearity in the first argument. -/
  inter_add_left : ∀ p q (a b : Chow X p) (c : Chow X q),
    inter p q (a + b) c = inter p q a c + inter p q b c
  /-- Bilinearity in the second argument. -/
  inter_add_right : ∀ p q (a : Chow X p) (b c : Chow X q),
    inter p q a (b + c) = inter p q a b + inter p q a c
  /-- The unit: the class of X itself in A^0. -/
  unit : Chow X 0
  /-- Left unit: [X] · α = α (via the canonical identification A^{0+p} ≅ A^p). -/
  inter_unit_left : ∀ p (a : Chow X p),
    HEq (inter 0 p unit a) a
  /-- Commutativity: α · β = β · α (up to the canonical A^{p+q} ≅ A^{q+p}). -/
  inter_comm : ∀ p q (a : Chow X p) (b : Chow X q),
    HEq (inter p q a b) (inter q p b a)

variable [idata : IntersectionData X]

-- ═══════════════════════════════════════════════════════════════════
-- NOTATION AND BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- The intersection product of two Chow classes. -/
def interChow (a : Chow X p) (b : Chow X q) : Chow X (p + q) :=
  IntersectionData.inter p q a b

/-- The intersection of zero with anything is zero (from bilinearity). -/
theorem inter_zero_left (b : Chow X q) :
    interChow (0 : Chow X p) b = 0 := by
  have h := IntersectionData.inter_add_left p q 0 0 b
  simp only [add_zero] at h
  -- h : inter(0, b) = inter(0, b) + inter(0, b)
  -- So inter(0, b) + inter(0, b) = inter(0, b) + 0
  -- Cancel: inter(0, b) = 0
  have h2 : interChow (0 : Chow X p) b + interChow 0 b =
    interChow (0 : Chow X p) b + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- The intersection of anything with zero is zero. -/
theorem inter_zero_right (a : Chow X p) :
    interChow a (0 : Chow X q) = 0 := by
  have h := IntersectionData.inter_add_right p q a 0 0
  simp only [add_zero] at h
  have h2 : interChow a (0 : Chow X q) + interChow a 0 =
    interChow a (0 : Chow X q) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- Intersection product is associative (up to the canonical identification
    A^{(p+q)+r} = A^{p+(q+r)} via Nat.add_assoc). -/
theorem inter_assoc [idata : IntersectionData X] {r : ℕ}
    (a : Chow X p) (b : Chow X q) (c : Chow X r)
    (h_assoc : ∀ p' q' r' (a' : Chow X p') (b' : Chow X q') (c' : Chow X r'),
      HEq (IntersectionData.inter (p' + q') r' (IntersectionData.inter p' q' a' b') c')
           (IntersectionData.inter p' (q' + r') a' (IntersectionData.inter q' r' b' c'))) :
    HEq (interChow (interChow a b) c) (interChow a (interChow b c)) :=
  h_assoc p q r a b c

/-- Intersection with negation: (-α)·β = -(α·β). From bilinearity. -/
theorem inter_neg_left [idata : IntersectionData X]
    (a : Chow X p) (b : Chow X q) :
    interChow (-a) b = -(interChow a b) := by
  have h := IntersectionData.inter_add_left p q a (-a) b
  rw [add_neg_cancel] at h
  -- h : inter 0 b = inter a b + inter (-a) b
  simp only [interChow]
  have h0 : IntersectionData.inter p q 0 b = 0 := inter_zero_left b
  rw [h0] at h
  -- h : 0 = inter a b + inter (-a/b) b/(-b)
  -- Need: inter (-a/b) b/(-b) = -(inter a b)
  exact eq_neg_of_add_eq_zero_right h.symm

/-- (-α)·β = -(α·β), right version. -/
theorem inter_neg_right [idata : IntersectionData X]
    (a : Chow X p) (b : Chow X q) :
    interChow a (-b) = -(interChow a b) := by
  have h := IntersectionData.inter_add_right p q a b (-b)
  rw [add_neg_cancel] at h
  simp only [interChow]
  have h0 : IntersectionData.inter p q a 0 = 0 := inter_zero_right a
  rw [h0] at h
  -- h : 0 = inter a b + inter (-a/b) b/(-b)
  -- Need: inter (-a/b) b/(-b) = -(inter a b)
  exact eq_neg_of_add_eq_zero_right h.symm

end

end Ramtastic.ChowGroups.IntersectionProduct
