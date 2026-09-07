/-
  RingHomomorphism.lean — The cycle class map is a ring homomorphism.

  Statement: cl(α · β) = cl(α) ⌣ cl(β)
  where:
  - · is the intersection product on Chow groups (CHOW ring multiplication)
  - ⌣ is the cup product on cohomology

  Mathematically: this says the cycle class map is COMPATIBLE with the ring
  structures on both sides — Chow ring and cohomology ring. It's why the
  cycle class map factors through the Chow ring.

  In our abstract setup: parameterized by a `cup` operation on cohomology
  + a hypothesis that cl is multiplicative for it.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Ramtastic.CycleClass.CycleClassMap

namespace Ramtastic.CycleClass.RingHomomorphism

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.ChowGroups.ChowGroup
open Ramtastic.ChowGroups.ChowRing
open Ramtastic.CycleClass.FundamentalClass
open Ramtastic.CycleClass.CycleClassMap

noncomputable section

variable {X : Type*} [VarietyData X] [RatEquivData X] [IntersectionData X]

-- ═══════════════════════════════════════════════════════════════════
-- CUP PRODUCT STRUCTURE ON COHOMOLOGY
-- ═══════════════════════════════════════════════════════════════════

/-- Cup product structure on the cohomology groups H^*(X).
    Bilinear, sends (Hᵏ, Hˡ) to H^{k+l}. -/
class CupProductData (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] where
  /-- The cup product. -/
  cup : ∀ {k l : ℕ}, CycleClassData.Cohom (X := X) k →
    CycleClassData.Cohom (X := X) l →
    CycleClassData.Cohom (X := X) (k + l)
  /-- Bilinearity in the first argument. -/
  cup_add_left : ∀ {k l : ℕ} (α₁ α₂ : CycleClassData.Cohom (X := X) k)
    (β : CycleClassData.Cohom (X := X) l),
    cup (α₁ + α₂) β = cup α₁ β + cup α₂ β
  /-- Bilinearity in the second argument. -/
  cup_add_right : ∀ {k l : ℕ} (α : CycleClassData.Cohom (X := X) k)
    (β₁ β₂ : CycleClassData.Cohom (X := X) l),
    cup α (β₁ + β₂) = cup α β₁ + cup α β₂

-- ═══════════════════════════════════════════════════════════════════
-- THE RING HOMOMORPHISM PROPERTY
-- ═══════════════════════════════════════════════════════════════════

/-- The cycle class map is a ring homomorphism: cl(α · β) = cl(α) ⌣ cl(β).
    Stated as a class so different constructions can prove this differently
    (e.g., via topological intersection theory, sheaf-theoretic methods, etc.). -/
class CycleClassRingHom (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [FundamentalClassData X]
    [CupProductData X] where
  /-- cl(α · β) = cl(α) ⌣ cl(β). The HEq accounts for `(p+q)+(p+q) = (p+p)+(q+q)`
      arithmetic equality (different syntactic forms via Nat.add_comm/assoc). -/
  cl_mul_eq_cup : ∀ (p q : ℕ) (α : Chow X p) (β : Chow X q),
    HEq (cycleClassMap (p + q) (IntersectionData.inter p q α β))
        (CupProductData.cup (cycleClassMap p α) (cycleClassMap q β))

end

end Ramtastic.CycleClass.RingHomomorphism
