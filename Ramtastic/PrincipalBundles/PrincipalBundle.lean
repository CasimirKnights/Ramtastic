/-
  PrincipalBundle.lean — Principal G-bundles.

  A principal G-bundle P → M is a fiber bundle where each fiber is a
  copy of the Lie group G, and G acts freely and transitively on fibers.

  For gauge theory: G is the gauge group (SU(N), SO(N), U(1), etc.).
  The bundle P encodes the "internal symmetry space" at each point of M.

  This module defines:
  - GaugeGroupData: the abstract structure of a principal bundle
  - The gauge group G with its Lie algebra 𝔤
  - The adjoint representation Ad : G → Aut(𝔤)
  - The fiber action (free, transitive)

  The Lie bracket is carried as raw data with axioms, and LieRing +
  LieAlgebra instances are constructed externally to share the
  AddCommGroup from NormedAddCommGroup (no diamond).

  Uses Mathlib's LieAlgebra and Group.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Algebra.Lie.Basic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.PrincipalBundles.PrincipalBundle

noncomputable section

-- ═══════════════════════════════════════════════════════════════════
-- THE GAUGE GROUP AND ITS LIE ALGEBRA
-- ═══════════════════════════════════════════════════════════════════

/-- Data for a gauge theory: a Lie group G with its Lie algebra 𝔤.

    The Lie algebra is the tangent space at the identity of G.
    The Lie bracket [X,Y] encodes the infinitesimal group structure.

    The normed structure on 𝔤 is PRIMARY (from NormedAddCommGroup).
    The Lie bracket is given as raw data with axioms. The LieRing
    and LieAlgebra instances are constructed below, sharing the
    AddCommGroup from NormedAddCommGroup. This avoids the diamond
    where LieRing and NormedAddCommGroup provide conflicting
    AddCommGroup instances.

    For the standard model: G = SU(3) × SU(2) × U(1).
    For Yang-Mills: G = SU(N) for some N.
    For Seiberg-Witten: G = U(1). -/
class GaugeGroupData where
  /-- The gauge group G. -/
  G : Type*
  [group : Group G]
  /-- The Lie algebra 𝔤 of G. -/
  𝔤 : Type*
  [normedAddCommGroup : NormedAddCommGroup 𝔤]
  [normedSpace : NormedSpace ℝ 𝔤]
  /-- The Lie bracket on 𝔤. -/
  lie : 𝔤 → 𝔤 → 𝔤
  /-- Bracket distributes over addition on the right. -/
  lie_add : ∀ x y z : 𝔤, lie x (y + z) = lie x y + lie x z
  /-- Bracket distributes over addition on the left. -/
  add_lie : ∀ x y z : 𝔤, lie (x + y) z = lie x z + lie y z
  /-- [X, X] = 0. -/
  lie_self : ∀ x : 𝔤, lie x x = 0
  /-- The Jacobi identity (Leibniz form). -/
  leibniz_lie : ∀ x y z : 𝔤,
    lie x (lie y z) = lie (lie x y) z + lie y (lie x z)
  /-- Scalar compatibility: [X, tY] = t[X, Y]. -/
  lie_smul : ∀ (t : ℝ) (x y : 𝔤), lie x (t • y) = t • lie x y
  /-- The adjoint representation: G acts on 𝔤 by conjugation.
      Ad(g)(X) = gXg⁻¹ at the infinitesimal level. -/
  Ad : G → 𝔤 →ₗ[ℝ] 𝔤
  /-- Ad is a group homomorphism: Ad(gh) = Ad(g) ∘ Ad(h). -/
  Ad_mul : ∀ g h : G, Ad (g * h) = (Ad g).comp (Ad h)
  /-- Ad(1) = id. -/
  Ad_one : Ad 1 = LinearMap.id
  /-- Ad preserves the Lie bracket: Ad(g)[X,Y] = [Ad(g)X, Ad(g)Y]. -/
  Ad_bracket : ∀ (g : G) (X Y : 𝔤),
    Ad g (lie X Y) = lie (Ad g X) (Ad g Y)
  /-- The bracket as a continuous bilinear map.
      Any finite-dimensional Lie algebra has a bounded bracket. -/
  lieBilin : 𝔤 →L[ℝ] 𝔤 →L[ℝ] 𝔤
  /-- The continuous bracket agrees with the raw bracket. -/
  lieBilin_eq : ∀ X Y : 𝔤, lieBilin X Y = lie X Y

attribute [reducible, instance] GaugeGroupData.group
  GaugeGroupData.normedAddCommGroup GaugeGroupData.normedSpace

variable [ggd : GaugeGroupData]

/-- Bracket notation for the Lie bracket on 𝔤. -/
instance : Bracket ggd.𝔤 ggd.𝔤 := ⟨ggd.lie⟩

/-- LieRing instance for 𝔤, using the AddCommGroup from NormedAddCommGroup. -/
instance : LieRing ggd.𝔤 where
  add_lie := ggd.add_lie
  lie_add := ggd.lie_add
  lie_self := ggd.lie_self
  leibniz_lie := ggd.leibniz_lie

/-- LieAlgebra instance for 𝔤 over ℝ. -/
instance : LieAlgebra ℝ ggd.𝔤 where
  lie_smul := ggd.lie_smul

-- ═══════════════════════════════════════════════════════════════════
-- THE PRINCIPAL BUNDLE
-- ═══════════════════════════════════════════════════════════════════

/-- A principal G-bundle over a base space M.

    The total space P fibers over M with fiber G.
    G acts on P freely (no fixed points) and transitively on fibers
    (any two points in the same fiber are related by a unique g ∈ G).

    The projection π : P → M sends each point to its base point.
    For each x ∈ M, the fiber π⁻¹(x) ≅ G. -/
class PrincipalBundleData (M : Type*) where
  /-- The total space of the bundle. -/
  P : Type*
  /-- The projection π : P → M. -/
  proj : P → M
  /-- The right action of G on P: p ↦ p · g. -/
  act : P → ggd.G → P
  /-- The action is associative: (p·g)·h = p·(g·h). -/
  act_assoc : ∀ (p : P) (g h : ggd.G), act (act p g) h = act p (g * h)
  /-- The identity acts trivially: p·1 = p. -/
  act_one : ∀ (p : P), act p 1 = p
  /-- The action is free: p·g = p ⟹ g = 1. -/
  act_free : ∀ (p : P) (g : ggd.G), act p g = p → g = 1
  /-- The action preserves fibers: π(p·g) = π(p). -/
  act_fiber : ∀ (p : P) (g : ggd.G), proj (act p g) = proj p
  /-- The action is transitive on fibers:
      if π(p) = π(q), then ∃ g, p·g = q. -/
  act_transitive : ∀ (p q : P), proj p = proj q → ∃ g : ggd.G, act p g = q

-- ═══════════════════════════════════════════════════════════════════
-- PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

variable {M : Type*} [pb : PrincipalBundleData M]

/-- The fiber over a point x ∈ M: all p ∈ P with π(p) = x. -/
def fiber (x : M) : Set pb.P := {p | pb.proj p = x}

/-- The action by g maps a fiber to itself. -/
theorem act_preserves_fiber (x : M) (p : pb.P) (g : ggd.G)
    (hp : p ∈ fiber x) : pb.act p g ∈ fiber x := by
  unfold fiber at *; simp at *; rw [pb.act_fiber]; exact hp

/-- The unique group element relating two points in the same fiber. -/
theorem fiber_transitive (x : M) (p q : pb.P)
    (hp : p ∈ fiber x) (hq : q ∈ fiber x) :
    ∃ g : ggd.G, pb.act p g = q := by
  unfold fiber at *; simp at *
  exact pb.act_transitive p q (by rw [hp, hq])

end

end Ramtastic.PrincipalBundles.PrincipalBundle
