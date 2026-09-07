/-
  RationalHodgeStructure.lean — The ℚ-structure on cohomology.

  On a smooth projective variety X, the cohomology carries:
  1. A ℚ-structure from singular cohomology
  2. A Hodge decomposition H^k = ⊕ H^{p,q} from the Kähler structure
  3. Hodge symmetry: h^{p,q} = h^{q,p}

  A Hodge class is a rational (p,p)-class: an element of
  H^{p,p}(X) ∩ H^{2p}(X, ℚ).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-18)
-/

import Mathlib.Tactic
import Ramtastic.GAGA.ChowToHodge

namespace Ramtastic.GAGA.RationalHodgeStructure

open Ramtastic.Kahler.HodgeDecomposition
open Ramtastic.ChowGroups.ChowRing
open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.CycleClass.CycleClassMap

noncomputable section

/-- A rational Hodge structure: Hodge numbers with symmetry and
    the Hodge-de Rham relation connecting to Betti numbers.

    h^{p,q} = dim H^{p,q}(X). The Hodge conjecture lives in the
    (p,p)-component of this structure. -/
structure RationalHodgeStructureData (n : ℕ) where
  /-- The Hodge numbers h^{p,q} for 0 ≤ p,q ≤ n. -/
  hodgeNumbers : Fin (n + 1) → Fin (n + 1) → ℕ
  /-- Hodge symmetry: h^{p,q} = h^{q,p}.
      From complex conjugation: H^{p,q} ≅ overline{H^{q,p}}. -/
  hodge_symmetry : ∀ (p q : Fin (n + 1)),
    hodgeNumbers p q = hodgeNumbers q p
  /-- Betti numbers: b_k = Σ_{p+q=k} h^{p,q}. -/
  betti : ℕ → ℕ
  /-- Hodge-de Rham: b_k = sum of Hodge numbers at degree k. -/
  hodge_deRham : ∀ (k : ℕ), k ≤ 2 * n →
    betti k = ∑ p ∈ Finset.range (k + 1),
      hodgeNumbers ⟨min p n, by omega⟩ ⟨min (k - p) n, by omega⟩

/-- A rational (p,p)-class on a variety with Hodge decomposition.
    This is the TYPE of object the Hodge conjecture is about. -/
structure RationalHodgeClass (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X]
    [HodgeDecomposition X] where
  /-- The degree p. -/
  p : ℕ
  /-- The cohomology class. -/
  cls : CycleClassData.Cohom (X := X) (p + p)
  /-- The class is of type (p,p) in the Hodge decomposition. -/
  is_pp : HodgeDecomposition.isHodgeType p p cls
  /-- The class is a Hodge class (in the Hodge class set). -/
  is_hodge : cls ∈ HodgeClassData.isHodge (X := X) p

/-- The Hodge conjecture: every RationalHodgeClass is algebraic.
    For any rational (p,p)-class, it is in the ℚ-span of cycle classes. -/
theorem hodge_conjecture_for_class (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X]
    [HodgeDecomposition X]
    (h_hodge : HodgeConjecture (X := X))
    (rhc : RationalHodgeClass X) :
    rhc.cls ∈ Submodule.span ℚ (Set.range (CycleClassData.cycleClass rhc.p)) :=
  h_hodge rhc.p rhc.cls rhc.is_hodge

end

end Ramtastic.GAGA.RationalHodgeStructure
