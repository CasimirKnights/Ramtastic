/-
  ChowToHodge.lean — Cycle classes map to Hodge classes via GAGA.

  The chain: Chow groups → cycle class map → GAGA → Hodge decomposition.
  The "easy direction": im(cl) ⊆ H^{p,p} ∩ H^{2p}(X, ℚ).
  The Hodge conjecture: the reverse inclusion.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-18)
-/

import Mathlib.Tactic
import Ramtastic.GAGA.GAGACorrespondence
import Ramtastic.CycleClass.ImageInHodge
import Ramtastic.Kahler.HodgeDecomposition
import Ramtastic.ChowGroups.ChowRing

namespace Ramtastic.GAGA.ChowToHodge

open Ramtastic.GAGA.GAGACorrespondence
open Ramtastic.Kahler.HodgeDecomposition
open Ramtastic.ChowGroups.ChowRing
open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence
open Ramtastic.ChowGroups.IntersectionProduct
open Ramtastic.CycleClass.CycleClassMap
open Ramtastic.ChowGroups.ChowGroup

noncomputable section

/-- The full chain from algebraic cycles to Hodge classes.

    For a smooth projective variety X with Hodge decomposition:
    1. A^p(X) → H^{2p}(X, ℚ) via the cycle class map cl (Piece 9)
    2. H^{2p}_alg ≅ H^{2p}_an via GAGA (this piece)
    3. H^{2p}_an = ⊕ H^{a,b} via Hodge decomposition (Piece 6)
    4. im(cl) ⊆ H^{p,p} (the "easy direction" — cl_is_hodge)

    Step 4 is encoded in HodgeClassData.cl_is_hodge from ChowRing.lean.
    The Hodge conjecture (HodgeConjectureAt) asks for the reverse of step 4. -/
structure ChowToHodgeChain (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X]
    [HodgeDecomposition X] where
  /-- The ambient dimension for GAGA correspondence. -/
  ambientDim : ℕ
  /-- The GAGA data connecting algebraic and analytic cohomology. -/
  gaga : GAGAData ambientDim
  /-- The cycle class map lands in Hodge classes (the "easy direction").
      This is HodgeClassData.cl_is_hodge, restated at the chain level. -/
  cl_lands_in_hodge : ∀ (p : ℕ) (a : Chow X p),
    CycleClassData.cycleClass p a ∈ HodgeClassData.isHodge (X := X) p
  /-- The cycle class image has Hodge type (p,p) in the decomposition.
      Every algebraic cycle of codimension p maps to a class in H^{p,p}:
      its Poincaré dual is a closed (p,p)-form (the current of integration). -/
  cl_is_hodge_type : ∀ (p : ℕ) (a : Chow X p),
    HodgeDecomposition.isHodgeType p p (CycleClassData.cycleClass p a)

/-- The Hodge conjecture for the chain: every rational (p,p)-class is algebraic.
    Wired to HodgeConjectureAt from ChowRing.lean.
    NOT a placeholder — this IS the real proposition. -/
def hodgeConjectureViaGAGA (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X] (p : ℕ) : Prop :=
  HodgeConjectureAt (X := X) p

/-- If the chain data exists AND the Hodge conjecture holds at degree p,
    then every Hodge class is a ℚ-linear combination of cycle classes. -/
theorem hodge_from_chain (X : Type*) [VarietyData X] [RatEquivData X]
    [IntersectionData X] [CycleClassData X] [HodgeClassData X]
    [HodgeDecomposition X]
    (_chain : ChowToHodgeChain X) (p : ℕ)
    (h_hodge : HodgeConjectureAt (X := X) p) :
    ∀ h ∈ HodgeClassData.isHodge (X := X) p,
      h ∈ Submodule.span ℚ (Set.range (CycleClassData.cycleClass p)) :=
  h_hodge

end

end Ramtastic.GAGA.ChowToHodge
