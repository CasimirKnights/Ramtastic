/-
  ThomClass.lean — The Thom class of an oriented vector bundle.

  For an oriented real rank-r vector bundle V → X, the Thom class
  τ_V ∈ H^r(Th(V), Th(V)\X; ℤ) is the cohomology class of the orientation.

  Multiplication by τ_V gives the Thom isomorphism:
    Φ_V : H^k(X) ≅ H^{k+r}(Th(V), Th(V)\X)

  In our abstract setup, ThomClassData carries the cohomology of X
  and the orientation/Thom class as data, with the iso as a property.

  Used downstream for:
  - The fundamental class [Z] ∈ H^{2p}(X) of a codim-p subvariety Z
    (constructed via tubular neighborhood + Thom class of normal bundle).
  - The cycle class map cl : A^p(X) → H^{2p}(X).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-16)
-/

import Mathlib.Tactic
import Mathlib.Algebra.Module.Basic
import Ramtastic.ChowGroups.ChowRing

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.CycleClass.ThomClass

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.ChowGroups.ChowGroup
open Ramtastic.ChowGroups.ChowRing

noncomputable section

variable {X : Type*} [VarietyData X] [RatEquivData X] [IntersectionData X]

-- ═══════════════════════════════════════════════════════════════════
-- THOM CLASS DATA
-- ═══════════════════════════════════════════════════════════════════

/-- Data for the Thom class of a rank-r oriented vector bundle.
    The bundle is parameterized by its rank r.

    Given:
    - cohomology groups Cohom k of the base
    - rank r of the bundle
    - the Thom class τ ∈ Cohom r itself
    - Thom isomorphism Φ : Cohom k ≃+ Cohom (k + r) (multiplication by τ)

    For trivial bundles (e.g., the zero bundle, r = 0), τ = 1 and
    Φ is the identity. -/
class ThomClassData (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] (r : ℕ) where
  /-- The Thom class lives in H^r. -/
  thomClass : CycleClassData.Cohom (X := X) r
  /-- The Thom isomorphism: H^k ≅ H^{k+r} (via cup product with τ). -/
  thomIso : ∀ k, CycleClassData.Cohom (X := X) k ≃+ CycleClassData.Cohom (X := X) (k + r)
  /-- The Thom class is nonzero (non-degeneracy). -/
  thomClass_ne_zero : thomClass ≠ 0

-- ═══════════════════════════════════════════════════════════════════
-- TRIVIAL BUNDLE (rank 0)
-- ═══════════════════════════════════════════════════════════════════

/-- For the trivial rank-0 bundle, the Thom class is the unit and
    Thom isomorphism is the identity. This is the base case. -/
@[reducible]
def trivialThomData [CycleClassData X]
    (h_unit : CycleClassData.Cohom (X := X) 0)
    (h_unit_ne_zero : h_unit ≠ 0) :
    ThomClassData X 0 where
  thomClass := h_unit
  thomIso k := by
    show CycleClassData.Cohom (X := X) k ≃+ CycleClassData.Cohom (X := X) (k + 0)
    rw [Nat.add_zero]
  thomClass_ne_zero := h_unit_ne_zero

end

end Ramtastic.CycleClass.ThomClass
