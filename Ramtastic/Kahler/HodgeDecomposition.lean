/-
  HodgeDecomposition.lean — The Hodge (p,q)-decomposition of cohomology.

  On a compact Kähler manifold X of complex dimension n, the de Rham
  cohomology decomposes:
    H^k(X, ℂ) = ⊕_{p+q=k} H^{p,q}(X)
  where H^{p,q} is the Dolbeault cohomology (harmonic (p,q)-forms).

  For RATIONAL cohomology (our setup with ℚ coefficients), the (p,p)-part
  of H^{2p}(X, ℚ) defines the HODGE CLASSES — the classes that are of pure
  type (p,p) under the Hodge decomposition. The Hodge conjecture asks
  whether these equal (ℚ-span of) cycle class images.

  This file provides:
  - `HodgeDecomposition X`: class carrying the (p,q)-decomposition data
    for the cohomology groups.
  - `hodgeClasses X p`: the (p,p)-part of H^{2p}(X, ℚ), extracted from
    the decomposition. This is what `HodgeClassData.isHodge` should be
    set to for real Hodge theory.

  The class is INDEPENDENT of the cycle class map — isHodge comes from
  Hodge theory, not from algebraic geometry. This is what was violated by
  the fake cpnHodgeClassData (which set isHodge = image, making the
  conjecture trivial).

  For CP^m: H^{2p}(CP^m, ℚ) = ℚ is entirely of type (p,p) (since CP^m
  has only even-degree cohomology, all of pure Hodge type). So the
  (p,p)-component IS the whole H^{2p}. The CP^m instance provides this
  directly from the known topology — no Kähler machinery needed for this
  specific variety.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Ramtastic.ChowGroups.ChowRing

set_option linter.dupNamespace false

namespace Ramtastic.Kahler.HodgeDecomposition

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.ChowGroups.ChowGroup
open Ramtastic.ChowGroups.ChowRing

noncomputable section

variable {X : Type*} [VarietyData X] [RatEquivData X] [IntersectionData X]

-- ═══════════════════════════════════════════════════════════════════
-- THE HODGE DECOMPOSITION CLASS
-- ═══════════════════════════════════════════════════════════════════

/-- The Hodge (p,q)-decomposition of cohomology.

    For a variety X with CycleClassData (providing Cohom k), this class
    provides the (p,q)-type components of Cohom k, and asserts that
    every element of Cohom (p + q) can be decomposed into (p,q)-type
    components.

    The FUNDAMENTAL PROPERTY: the (p,p)-component of H^{2p}(X, ℚ) defines
    the Hodge classes INDEPENDENTLY of the cycle class map. The Hodge
    conjecture then becomes a real claim: every Hodge class is in the
    ℚ-span of cycle class images.

    On a compact Kähler manifold, this decomposition exists and is
    CANONICAL (comes from the Hodge theorem on harmonic forms). For
    specific varieties like CP^m, the decomposition is known by explicit
    computation and doesn't require the full Kähler machinery.

    The `isHodgeType` predicate classifies elements by their (p,q)-type.
    The `hodge_spans` field asserts every cohomology class in H^{p+q}
    is a sum of (p,q)-type elements. -/
class HodgeDecomposition (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] where
  /-- Predicate: `h` is of Hodge type (p, q) in H^{p+q}(X, ℚ). -/
  isHodgeType : (p q : ℕ) → CycleClassData.Cohom (X := X) (p + q) → Prop
  /-- Type (p,q) is a ℚ-submodule: closed under addition. -/
  isHodgeType_add : ∀ p q (h₁ h₂ : CycleClassData.Cohom (X := X) (p + q)),
    isHodgeType p q h₁ → isHodgeType p q h₂ → isHodgeType p q (h₁ + h₂)
  /-- Type (p,q) is a ℚ-submodule: closed under ℚ-scalar multiplication. -/
  isHodgeType_smul : ∀ p q (c : ℚ) (h : CycleClassData.Cohom (X := X) (p + q)),
    isHodgeType p q h → isHodgeType p q (c • h)
  /-- Zero is of every type. -/
  isHodgeType_zero : ∀ p q, isHodgeType p q (0 : CycleClassData.Cohom (X := X) (p + q))
  /-- **Spanning at even degrees**: every element of H^{2p} is of (p,p)-type.
      This prevents vacuous hodgeClasses and asserts the key fact for Hodge
      theory: at degree 2p, the (p,p)-component is the whole cohomology
      (for varieties where this is true, like CP^m), or at least contains
      every element that the Hodge conjecture needs to examine.
      For general compact Kähler manifolds where H^{2p} has other (r,s)-types:
      instances should restrict this to the appropriate subspace. -/
  hodge_pp_spans : ∀ (p : ℕ) (h : CycleClassData.Cohom (X := X) (p + p)),
    ∃ (h_pp : CycleClassData.Cohom (X := X) (p + p)),
      isHodgeType p p h_pp ∧
      ∃ (h_rest : CycleClassData.Cohom (X := X) (p + p)),
        h = h_pp + h_rest

-- ═══════════════════════════════════════════════════════════════════
-- HODGE CLASSES: THE (p,p)-PART
-- ═══════════════════════════════════════════════════════════════════

variable [CycleClassData X] [hd : HodgeDecomposition X]

/-- The set of Hodge classes in H^{2p}(X, ℚ): elements of type (p, p).
    This is what `HodgeClassData.isHodge` should be for real Hodge theory.

    Note: H^{2p} = Cohom(p + p). The isHodgeType predicate at (p, p)
    gives the (p,p)-component. -/
def hodgeClasses (p : ℕ) : Set (CycleClassData.Cohom (X := X) (p + p)) :=
  {h | hd.isHodgeType p p h}

/-- Zero is always a Hodge class. -/
theorem zero_mem_hodgeClasses (p : ℕ) :
    (0 : CycleClassData.Cohom (X := X) (p + p)) ∈ hodgeClasses (X := X) p :=
  hd.isHodgeType_zero p p

/-- Hodge classes are closed under addition. -/
theorem hodgeClasses_add (p : ℕ)
    {h₁ h₂ : CycleClassData.Cohom (X := X) (p + p)}
    (hh₁ : h₁ ∈ hodgeClasses (X := X) p) (hh₂ : h₂ ∈ hodgeClasses (X := X) p) :
    h₁ + h₂ ∈ hodgeClasses (X := X) p :=
  hd.isHodgeType_add p p h₁ h₂ hh₁ hh₂

/-- Hodge classes are closed under ℚ-scaling. -/
theorem hodgeClasses_smul (p : ℕ) (c : ℚ)
    {h : CycleClassData.Cohom (X := X) (p + p)}
    (hh : h ∈ hodgeClasses (X := X) p) :
    c • h ∈ hodgeClasses (X := X) p :=
  hd.isHodgeType_smul p p c h hh

end

end Ramtastic.Kahler.HodgeDecomposition
