/-
  BSDFormula.lean - public BSD statement vocabulary.

  This file defines weak/strong BSD statement surfaces and standard parity and
  leading-coefficient helper facts used by the Tower layer.
-/

import Mathlib.Tactic
import Ramtastic.BSD.MordellWeil
import Ramtastic.BSD.HeightPairing
import Ramtastic.BSD.LFunction
import Ramtastic.BSD.TateShafarevich

namespace Ramtastic.BSD.BSDFormula

open Ramtastic.BSD.MordellWeil
open Ramtastic.BSD.HeightPairing
open Ramtastic.BSD.LFunction
open Ramtastic.BSD.TateShafarevich

noncomputable section

-- ================================================================
-- I. DATA STRUCTURES
-- ================================================================

/-- Weak BSD data package. -/
structure WeakBSDData where
  mw : MordellWeilGroup
  ar : AnalyticRank

/-- Strong BSD data package. -/
structure StrongBSDData extends WeakBSDData where
  reg : Regulator mw
  tam : TamagawaData
  per : PeriodData

-- ================================================================
-- II. CONJECTURE STATEMENTS (Prop, not theorems)
-- ================================================================

/-- **Weak BSD (statement).** rank E(ℚ) = ord_{s=1} L(E, s). -/
def weak_BSD (V : WeakBSDData) : Prop :=
  V.mw.rank = V.ar.analytic_rank

/-- **The BSD product, parameterized by Sha order.** -/
def bsd_product (V : StrongBSDData) (sha_order : ℕ) : ℝ :=
  (V.per.omega * V.reg.regulator * (sha_order : ℝ) *
   (V.tam.tamagawa_product : ℝ)) /
  ((V.mw.torsion_order : ℝ) ^ 2)

/-- **Strong BSD (statement).** The leading coefficient formula.
    Sha finiteness is part of the statement, not the structure. -/
def strong_BSD (V : StrongBSDData) : Prop :=
  weak_BSD V.toWeakBSDData ∧
  ∃ (sha_order : ℕ), 0 < sha_order ∧
    (iteratedDeriv V.ar.analytic_rank V.ar.L 1 : ℝ) /
      (Nat.factorial V.ar.analytic_rank : ℝ) = bsd_product V sha_order

-- ================================================================
-- III. DERIVED THEOREMS
-- ================================================================

/-- **Parity BSD data.** Extends WeakBSDData with root number
    parity information. Published: Dokchitser-Dokchitser (2010). -/
structure ParityBSDData extends WeakBSDData where
  /-- The algebraic rank parity matches the root number.
      (-1)^rank = root_number.
      Published: Dokchitser-Dokchitser 2010. -/
  algebraic_parity : (-1 : ℤ) ^ mw.rank = ar.root_number
  /-- The completed L-function Λ is smooth. -/
  Lambda_differentiable : Differentiable ℝ ar.Lambda
  /-- Λ^{(r)}(1) ≠ 0. The leading derivative of the completed
      L-function is nonzero. From the relationship between L and Λ
      (they differ by a nonvanishing Gamma factor at s = 1)
      combined with leading_nonzero. Published: standard. -/
  Lambda_leading_nonzero : iteratedDeriv ar.analytic_rank ar.Lambda 1 ≠ 0

-- Iterated derivative of the functional equation.
-- From Λ(s) = w · Λ(2-s), differentiating k times at s = 1:
-- Λ^{(k)}(1) = w · (-1)^k · Λ^{(k)}(1).
-- The chain rule for Λ(2-s) is iteratedDeriv_comp_const_sub from Mathlib.

-- Step 1-3 combined: the functional equation differentiated k times at s = 1.
-- Uses: iteratedDeriv_comp_const_sub (chain rule for f(c-x))
--       iteratedDeriv_const_mul_field (chain rule for c*f)
-- Both from Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas.
-- The composition requires careful type matching with Mathlib's API.
/-- Functional equation differentiated k times at the central point. -/
lemma func_eq_at_one (V : ParityBSDData) (k : ℕ) :
    iteratedDeriv k V.ar.Lambda 1 =
    (V.ar.root_number : ℝ) * ((-1 : ℝ) ^ k * iteratedDeriv k V.ar.Lambda 1) := by
  have hfe : V.ar.Lambda = fun s => (V.ar.root_number : ℝ) * V.ar.Lambda (2 - s) :=
    funext V.ar.func_eq
  conv_lhs => rw [hfe]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_sub, smul_eq_mul]
  norm_num

lemma root_times_parity_eq_one (V : ParityBSDData) :
    (V.ar.root_number : ℝ) * (-1 : ℝ) ^ V.ar.analytic_rank = 1 := by
  have h := func_eq_at_one V V.ar.analytic_rank
  have h_nz := V.Lambda_leading_nonzero
  -- h : a = w * ((-1)^r * a), a ≠ 0
  -- So a * (1 - w * (-1)^r) = 0, a ≠ 0, so 1 - w * (-1)^r = 0
  have h1 : iteratedDeriv V.ar.analytic_rank V.ar.Lambda 1 *
    (1 - (V.ar.root_number : ℝ) * (-1 : ℝ) ^ V.ar.analytic_rank) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 h_nz
  · linarith

/-- **Step 5: w = ±1 and w·m = 1 → m = w.** -/
theorem analytic_parity (V : ParityBSDData) :
    (-1 : ℝ) ^ V.ar.analytic_rank = (V.ar.root_number : ℝ) := by
  have h_wm := root_times_parity_eq_one V
  -- w * m = 1, w² = 1, m² = 1 → m = w
  have h_wsq : (V.ar.root_number : ℝ) ^ 2 = 1 := by
    have := V.ar.root_number_sq; exact_mod_cast this
  have h_msq : ((-1 : ℝ) ^ V.ar.analytic_rank) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨V.ar.analytic_rank, by ring⟩
  -- w * m = 1 and both square to 1 → m = w
  nlinarith [sq_nonneg ((V.ar.root_number : ℝ) - (-1 : ℝ) ^ V.ar.analytic_rank)]

/-- Parity comparison between algebraic and analytic rank. -/
theorem parity_BSD (V : ParityBSDData) :
    (-1 : ℝ) ^ V.mw.rank = (-1 : ℝ) ^ V.ar.analytic_rank := by
  have h_alg : (-1 : ℝ) ^ V.mw.rank = (V.ar.root_number : ℝ) := by
    have := V.algebraic_parity  -- (-1 : ℤ)^rank = root_number
    exact_mod_cast this
  have h_an := analytic_parity V
  -- h_alg : (-1)^rank = w, h_an : (-1)^analytic_rank = w
  linarith

-- ================================================================
-- IV. MORE DERIVED RESULTS
-- ================================================================

/-- Positivity of the BSD product under the stated positivity hypotheses. -/
theorem bsd_product_pos (V : StrongBSDData)
    (sha_order : ℕ) (sha_pos : 0 < sha_order)
    (h_rank : 0 < V.mw.rank) :
    0 < bsd_product V sha_order := by
  unfold bsd_product
  apply div_pos
  · apply mul_pos; apply mul_pos; apply mul_pos
    exact V.per.omega_pos
    exact V.reg.regulator_pos h_rank
    exact Nat.cast_pos.mpr sha_pos
    exact Nat.cast_pos.mpr V.tam.tamagawa_product_pos
  · exact pow_pos (Nat.cast_pos.mpr V.mw.torsion_order_pos) 2

end

end Ramtastic.BSD.BSDFormula
