/-
  ChowGroup.lean — The Chow group A^p = Z^p / ~_rat.

  The quotient of algebraic p-cycles by rational equivalence.
  A^p(X) is an abelian group (quotient of Z^p by the subgroup R^p).
  After tensoring with ℚ: a ℚ-vector space.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Ramtastic.ChowGroups.RationalEquivalence

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.ChowGroups.ChowGroup

open Ramtastic.ChowGroups.AlgebraicCycle
open Ramtastic.ChowGroups.RationalEquivalence

noncomputable section

variable {X : Type*} [vd : VarietyData X] [req : RatEquivData X] {p : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- THE CHOW GROUP
-- ═══════════════════════════════════════════════════════════════════

/-- The Chow group A^p(X) = Z^p(X) / R^p(X).
    The quotient of the cycle group by rational equivalence.
    This is the fundamental object of algebraic intersection theory. -/
abbrev Chow (X : Type*) [VarietyData X] [RatEquivData X] (p : ℕ) : Type _ :=
  (CycleGroup X p) ⧸ (RatEquivData.ratTrivial (X := X) p)

instance (p : ℕ) : AddCommGroup (Chow X p) :=
  inferInstanceAs (AddCommGroup ((CycleGroup X p) ⧸ _))

-- ═══════════════════════════════════════════════════════════════════
-- THE QUOTIENT MAP
-- ═══════════════════════════════════════════════════════════════════

/-- The quotient map cl : Z^p → A^p sending a cycle to its class. -/
def chowClass (p : ℕ) : CycleGroup X p →+ Chow X p :=
  QuotientAddGroup.mk' (RatEquivData.ratTrivial (X := X) p)

/-- The class of a subvariety [V] in A^p. -/
def chowOf (V : VarietyData.Subvariety (X := X) p) : Chow X p :=
  chowClass p (cycle V)

/-- Rationally equivalent cycles have the same Chow class. -/
theorem chowClass_eq_of_ratEquiv {Z₁ Z₂ : CycleGroup X p}
    (h : RatEquiv Z₁ Z₂) : chowClass p Z₁ = chowClass p Z₂ := by
  simp only [chowClass]
  exact QuotientAddGroup.eq.mpr (by
    rw [show -Z₁ + Z₂ = -(Z₁ - Z₂) from by abel]
    exact (RatEquivData.ratTrivial p).neg_mem h)

/-- The class of the zero cycle is zero. -/
theorem chowClass_zero : chowClass p (0 : CycleGroup X p) = 0 :=
  map_zero _

/-- The class map is surjective: every element of A^p has a cycle representative. -/
theorem chowClass_surjective (p : ℕ) : Function.Surjective (chowClass (X := X) p) :=
  QuotientAddGroup.mk'_surjective _

-- ═══════════════════════════════════════════════════════════════════
-- ℤ-MODULE STRUCTURE
-- ═══════════════════════════════════════════════════════════════════

instance (p : ℕ) : Module ℤ (Chow X p) :=
  inferInstanceAs (Module ℤ ((CycleGroup X p) ⧸ _))

/-- The class map is ℤ-linear. -/
theorem chowClass_int_linear (p : ℕ) (n : ℤ) (Z : CycleGroup X p) :
    chowClass p (n • Z) = n • chowClass p Z :=
  map_zsmul _ n Z

end

-- ═══════════════════════════════════════════════════════════════════
-- RATIONAL CHOW GROUP: A^p ⊗ ℚ (CONSTRUCTED)
-- ═══════════════════════════════════════════════════════════════════

noncomputable section

open scoped TensorProduct

variable {X : Type*} [vd : VarietyData X] [req : RatEquivData X]

/-- The rational Chow group: A^p ⊗_ℤ ℚ. CONSTRUCTED via TensorProduct. -/
abbrev ChowQ (X : Type*) [VarietyData X] [RatEquivData X] (p : ℕ) : Type _ :=
  (Chow X p) ⊗[ℤ] ℚ

instance chowQ_acg (p : ℕ) : AddCommGroup (ChowQ X p) :=
  inferInstanceAs (AddCommGroup ((Chow X p) ⊗[ℤ] ℚ))

-- ℚ-module on ChowQ: constructed via the ℤ-module structure of
-- the tensor product and the ℤ-algebra structure of ℚ.
-- Since ℚ is a ℤ-algebra, ℤ embeds into ℚ, and the ℤ-action on
-- M ⊗[ℤ] ℚ extends to a ℚ-action via q • (m ⊗ r) = m ⊗ (q * r).
-- The ℚ-module instance exists in Mathlib as the right-module
-- structure of the tensor product with a commutative ring.
-- We access it via the Algebra ℤ ℚ structure.
-- Module ℚ on M ⊗[ℤ] ℚ: ℚ acts via the right factor.
-- q • (m ⊗ r) = m ⊗ (q * r).
-- ℚ-multiplication on ℚ is ℤ-linear: (q * ·) : ℚ →ₗ[ℤ] ℚ.
private def qMulLin (q : ℚ) : ℚ →ₗ[ℤ] ℚ where
  toFun r := q * r
  map_add' a b := mul_add q a b
  map_smul' n r := by simp [mul_comm, zsmul_eq_mul, Int.cast_mul, mul_assoc]

noncomputable instance chowQ_mod (p : ℕ) : Module ℚ (ChowQ X p) where
  smul q x := TensorProduct.map LinearMap.id (qMulLin q) x
  one_smul x := by
    show TensorProduct.map LinearMap.id (qMulLin 1) x = x
    have : qMulLin 1 = LinearMap.id := by ext; simp [qMulLin]
    rw [this, TensorProduct.map_id]; rfl
  mul_smul q r x := by
    simp only [HSMul.hSMul, SMul.smul]
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul m s => simp [TensorProduct.map_tmul, qMulLin, mul_assoc]
    | add x y hx hy => simp [map_add, hx, hy]
  smul_zero q := map_zero _
  smul_add q x y := map_add _ x y
  add_smul q r x := by
    show TensorProduct.map LinearMap.id (qMulLin (q + r)) x =
      TensorProduct.map LinearMap.id (qMulLin q) x +
      TensorProduct.map LinearMap.id (qMulLin r) x
    have h : qMulLin (q + r) = qMulLin q + qMulLin r := by
      ext a; simp [qMulLin, add_mul]
    rw [h, TensorProduct.map_add_right]; rfl
  zero_smul x := by
    show TensorProduct.map LinearMap.id (qMulLin 0) x = 0
    have h : qMulLin 0 = 0 := by ext; simp [qMulLin]
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul m s => simp [TensorProduct.map_tmul, qMulLin]
    | add x y hx hy =>
      rw [h] at hx hy ⊢; simp [map_add, hx, hy]

/-- The rationalization map: A^p → A^p ⊗ ℚ. Sends a to a ⊗ 1. -/
def toChowQ (p : ℕ) (a : Chow X p) : ChowQ X p :=
  TensorProduct.tmul ℤ a (1 : ℚ)

/-- Scalar multiplication on `ChowQ` multiplies the rational tensor factor. -/
theorem chowQ_smul_tmul (p : ℕ) (q : ℚ) (a : Chow X p) (r : ℚ) :
    q • (TensorProduct.tmul ℤ a r : ChowQ X p) =
      TensorProduct.tmul ℤ a (q * r) := by
  change TensorProduct.map LinearMap.id (qMulLin q)
      (TensorProduct.tmul ℤ a r) =
    TensorProduct.tmul ℤ a (q * r)
  simp [qMulLin]

end

end Ramtastic.ChowGroups.ChowGroup
