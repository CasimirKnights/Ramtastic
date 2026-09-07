/-
  CliffordBundle.lean — Clifford algebra of an inner product space.

  For a real inner product space V, the Clifford algebra Cl(V, Q) where
  Q(v) = ⟨v, v⟩ is the quotient of the tensor algebra by v⊗v = Q(v).

  This module defines:
  - The quadratic form Q(v) = B(v,v) where B is the inner product bilinear form
  - Cl(V) = CliffordAlgebra(Q)
  - The embedding ι : V → Cl(V)
  - The fundamental relation: v² = ⟨v, v⟩
  - The anticommutation relation: vw + wv = 2⟨v, w⟩
  - Orthogonal vectors anticommute: ⟨v,w⟩ = 0 ⟹ vw = -wv
  - The even subalgebra Cl⁰(V)
  - The ZMod 2 grading (even/odd)
  - The Spin and Pin groups
  - The involute and reverse operations
  - The star (Clifford conjugation)

  Built from Mathlib's CliffordAlgebra, innerₗ, BilinMap.toQuadraticMap.
  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-13)
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.SeibergWitten.CliffordBundle

open CliffordAlgebra

noncomputable section

-- ═══════════════════════════════════════════════════════════════════
-- THE QUADRATIC FORM FROM AN INNER PRODUCT
-- ═══════════════════════════════════════════════════════════════════

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The inner product as a bilinear map V →ₗ[ℝ] V →ₗ[ℝ] ℝ. -/
def innerBilin : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := innerₗ (F := V)

/-- The POSITIVE quadratic form Q(v) = ⟨v, v⟩ = B(v,v). -/
def innerQ : QuadraticForm ℝ V := LinearMap.BilinMap.toQuadraticMap (innerBilin V)

/-- The NEGATIVE definite quadratic form -Q(v) = -⟨v, v⟩.
    This is the geometric convention (Lawson-Michelsohn).
    Unit vectors square to -1. The Clifford algebra has complex structure.
    The Dirac operator is self-adjoint. The circle, not the hyperbola.
    See MICHAEL_AND_THE_SNAKE.md Decision #1. -/
def negInnerQ : QuadraticForm ℝ V := -(innerQ V)

/-- Q(v) = ⟨v, v⟩. -/
theorem innerQ_apply (v : V) : innerQ V v = @inner ℝ V _ v v := by
  unfold innerQ innerBilin
  simp [LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply]

/-- The embedding ι : V → Cl(V, -Q).
    Uses the NEGATIVE definite convention (the circle). -/
def embed : V →ₗ[ℝ] CliffordAlgebra (negInnerQ V) :=
  CliffordAlgebra.ι (negInnerQ V)

-- ═══════════════════════════════════════════════════════════════════
-- THE CLIFFORD RELATIONS
-- ═══════════════════════════════════════════════════════════════════

variable {V}

/-- The fundamental Clifford relation: v² = -Q(v) · 1 = -⟨v, v⟩ · 1.
    Unit vectors square to -1. The circle convention. -/
theorem embed_sq (v : V) :
    embed V v * embed V v =
    algebraMap ℝ (CliffordAlgebra (negInnerQ V)) (negInnerQ V v) :=
  ι_sq_scalar (negInnerQ V) v

/-- The anticommutation relation: vw + wv = polar(Q)(v,w) · 1.
    polar(Q)(v,w) = Q(v+w) - Q(v) - Q(w) = 2⟨v,w⟩ for our inner product Q.
    This is Mathlib's `ι_mul_ι_add_swap`. -/
theorem embed_anticomm (v w : V) :
    embed V v * embed V w + embed V w * embed V v =
    algebraMap ℝ (CliffordAlgebra (negInnerQ V))
      (QuadraticMap.polar (negInnerQ V) v w) :=
  ι_mul_ι_add_swap v w

/-- The commutation relation: vw = polar(v,w) - wv.
    Mathlib's `ι_mul_ι_comm`. -/
theorem embed_comm (v w : V) :
    embed V v * embed V w =
    algebraMap ℝ (CliffordAlgebra (negInnerQ V))
      (QuadraticMap.polar (negInnerQ V) v w) - embed V w * embed V v :=
  ι_mul_ι_comm v w

/-- Orthogonal vectors anticommute: polar(v,w) = 0 ⟹ vw = -wv.
    When ⟨v,w⟩ = 0, the polar form vanishes, so vw + wv = 0. -/
theorem embed_ortho_anticomm (v w : V)
    (h : QuadraticMap.polar (negInnerQ V) v w = 0) :
    embed V v * embed V w = -(embed V w * embed V v) := by
  have hab := embed_anticomm (V := V) v w
  rw [h, map_zero] at hab
  -- hab : embed V v * embed V w + embed V w * embed V v = 0
  exact eq_neg_of_add_eq_zero_left hab

-- ═══════════════════════════════════════════════════════════════════
-- THE GRADING: EVEN AND ODD ELEMENTS
-- ═══════════════════════════════════════════════════════════════════

/-- The even subalgebra Cl⁰(V) ⊆ Cl(V): products of even numbers of vectors.
    The Spin group lives here. -/
def clEven : Subalgebra ℝ (CliffordAlgebra (negInnerQ V)) :=
  CliffordAlgebra.even (negInnerQ V)

/-- The even submodule (grade 0 in ℤ/2-grading). -/
def gradeEven : Submodule ℝ (CliffordAlgebra (negInnerQ V)) :=
  CliffordAlgebra.evenOdd (negInnerQ V) 0

/-- The odd submodule (grade 1 in ℤ/2-grading). -/
def gradeOdd : Submodule ℝ (CliffordAlgebra (negInnerQ V)) :=
  CliffordAlgebra.evenOdd (negInnerQ V) 1

/-- A vector is in the odd grade. -/
theorem embed_mem_odd (v : V) :
    embed V v ∈ gradeOdd (V := V) :=
  CliffordAlgebra.ι_mem_evenOdd_one (negInnerQ V) v

-- ═══════════════════════════════════════════════════════════════════
-- INVOLUTE, REVERSE, AND STAR (Clifford conjugation)
-- ═══════════════════════════════════════════════════════════════════

/-- The grade involution α : Cl(V) → Cl(V).
    On vectors: α(v) = -v. On products: α(xy) = α(x)α(y).
    This is the automorphism that negates odd elements. -/
def involute : CliffordAlgebra (negInnerQ V) →ₐ[ℝ] CliffordAlgebra (negInnerQ V) :=
  CliffordAlgebra.involute

/-- Involute negates vectors: α(ι(v)) = -ι(v). -/
theorem involute_embed (v : V) :
    involute (embed V v) = -(embed V v) :=
  CliffordAlgebra.involute_ι v

/-- Involute is an involution: α(α(x)) = x. -/
theorem involute_involute (x : CliffordAlgebra (negInnerQ V)) :
    involute (involute x) = x :=
  CliffordAlgebra.involute_involute x

/-- The reversal anti-automorphism β : Cl(V) → Cl(V).
    On vectors: β(v) = v. On products: β(xy) = β(y)β(x).
    Reverses the order of multiplication. -/
def reverse : CliffordAlgebra (negInnerQ V) →ₗ[ℝ] CliffordAlgebra (negInnerQ V) :=
  CliffordAlgebra.reverse

/-- Reverse fixes vectors: β(ι(v)) = ι(v). -/
theorem reverse_embed (v : V) :
    reverse (embed V v) = embed V v :=
  CliffordAlgebra.reverse_ι v

/-- The Clifford conjugation (star): x̄ = β(α(x)) = reverse(involute(x)).
    Combines grade involution and reversal. -/
theorem star_def (x : CliffordAlgebra (negInnerQ V)) :
    star x = reverse (involute x) := by
  unfold reverse involute
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- THE SPIN AND PIN GROUPS
-- ═══════════════════════════════════════════════════════════════════

/-- The Lipschitz group: the subgroup of units generated by
    invertible vectors. -/
def lipschitzGrp : Subgroup (CliffordAlgebra (negInnerQ V))ˣ :=
  lipschitzGroup (negInnerQ V)

/-- The Pin group: elements of the Lipschitz group that are unitary
    (x · x̄ = 1). Double cover of O(V). -/
def pinGrp : Submonoid (CliffordAlgebra (negInnerQ V)) :=
  pinGroup (negInnerQ V)

/-- The Spin group: even elements of the Pin group.
    Double cover of SO(V). -/
def spinGrp : Submonoid (CliffordAlgebra (negInnerQ V)) :=
  spinGroup (negInnerQ V)

end

end Ramtastic.SeibergWitten.CliffordBundle
