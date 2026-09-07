/-
  SchurTest.lean — The general Schur test for bilinear forms.

  TOWER FILE. No polynomial. No K. No domain-specific content.
  Pure functional analysis: row/col bounds → bilinear form bound.

  PROVES: |Σᵢⱼ wᵢⱼ aᵢ bⱼ|² ≤ R·C·(Σaᵢ²)·(Σbⱼ²)
  from: ∀ i, Σⱼ |wᵢⱼ| ≤ R and ∀ j, Σᵢ |wᵢⱼ| ≤ C.

  Two Cauchy-Schwarz applications. No n factor.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6)
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.SchurTest

open Finset

noncomputable section

/-- **The Schur test for bilinear forms. PROVED. No n factor.**

    For w : Fin n → Fin n → ℝ with:
    - Row bound: ∀ i, Σⱼ |wᵢⱼ| ≤ R
    - Col bound: ∀ j, Σᵢ |wᵢⱼ| ≤ C

    Then: |Σᵢⱼ wᵢⱼ aᵢ bⱼ|² ≤ R · C · (Σ aᵢ²) · (Σ bⱼ²).

    Proof (two Cauchy-Schwarz, no √, no DFT):
    |B|² ≤ (Σaᵢ²) · Σᵢ(Σⱼ|wᵢⱼ||bⱼ|)²  [outer C-S]
    Σᵢ(Σⱼ|wᵢⱼ||bⱼ|)² ≤ Σᵢ (Σⱼ|wᵢⱼ|)(Σⱼ|wᵢⱼ|bⱼ²)  [inner C-S per row]
    ≤ R · Σⱼ bⱼ²(Σᵢ|wᵢⱼ|) ≤ RC · Σbⱼ²  [row bound + col bound]
    Combined: |B|² ≤ RC · (Σaᵢ²)(Σbⱼ²). -/
theorem schur_test {n : ℕ} (w : Fin n → Fin n → ℝ)
    (a b : Fin n → ℝ) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (row_bound : ∀ i, ∑ j, |w i j| ≤ R)
    (col_bound : ∀ j, ∑ i, |w i j| ≤ C) :
    (∑ i, ∑ j, w i j * a i * b j) ^ 2 ≤
    R * C * (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  set c : Fin n → ℝ := fun i => ∑ j, |w i j| * |b j| with hc_def
  have h_triangle : |∑ i, ∑ j, w i j * a i * b j| ≤ ∑ i, |a i| * c i := by
    calc |∑ i, ∑ j, w i j * a i * b j|
        ≤ ∑ i, |∑ j, w i j * a i * b j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a i| * c i := by
          gcongr with i _
          calc |∑ j, w i j * a i * b j|
              = |a i| * |∑ j, w i j * b j| := by
                rw [show ∑ j, w i j * a i * b j = a i * ∑ j, w i j * b j from by
                  rw [Finset.mul_sum]; congr 1; ext j; ring]
                exact abs_mul _ _
            _ ≤ |a i| * ∑ j, |w i j * b j| := by
                gcongr; exact abs_sum_le_sum_abs _ _
            _ = |a i| * c i := by
                congr 1; congr 1; ext j; exact abs_mul _ _
  have h_cs_outer : (∑ i, |a i| * c i) ^ 2 ≤
      (∑ i, a i ^ 2) * (∑ i, c i ^ 2) := by
    calc (∑ i, |a i| * c i) ^ 2
        = (∑ i ∈ univ, |a i| * c i) ^ 2 := by simp
      _ ≤ (∑ i ∈ univ, |a i| ^ 2) * (∑ i ∈ univ, c i ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => |a i|) c
      _ = (∑ i, a i ^ 2) * (∑ i, c i ^ 2) := by simp [sq_abs]
  have h_c_sq_bound : ∑ i, c i ^ 2 ≤ R * C * ∑ j, b j ^ 2 := by
    have h_inner_cs : ∀ i, c i ^ 2 ≤ (∑ j, |w i j|) * (∑ j, |w i j| * b j ^ 2) := by
      intro i
      have h := Finset.sum_mul_sq_le_sq_mul_sq univ
        (fun j => Real.sqrt (|w i j|)) (fun j => Real.sqrt (|w i j|) * |b j|)
      have h_lhs : ∑ j ∈ univ, Real.sqrt (|w i j|) * (Real.sqrt (|w i j|) * |b j|) =
          ∑ j ∈ univ, |w i j| * |b j| := by
        congr 1; ext j; rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
      have h_f2 : ∑ j ∈ univ, Real.sqrt (|w i j|) ^ 2 = ∑ j ∈ univ, |w i j| := by
        congr 1; ext j; exact Real.sq_sqrt (abs_nonneg _)
      have h_g2 : ∑ j ∈ univ, (Real.sqrt (|w i j|) * |b j|) ^ 2 =
          ∑ j ∈ univ, |w i j| * b j ^ 2 := by
        congr 1; ext j; rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
      rw [h_lhs, h_f2, h_g2] at h
      convert h using 1 <;> simp
    have h_each : ∀ i, c i ^ 2 ≤ R * ∑ j, |w i j| * b j ^ 2 := by
      intro i; exact le_trans (h_inner_cs i) (by gcongr; exact row_bound i)
    have h_sum : ∑ i, c i ^ 2 ≤ R * ∑ i, ∑ j, |w i j| * b j ^ 2 := by
      calc ∑ i, c i ^ 2 ≤ ∑ i, R * ∑ j, |w i j| * b j ^ 2 :=
            Finset.sum_le_sum fun i _ => h_each i
        _ = R * ∑ i, ∑ j, |w i j| * b j ^ 2 := by rw [← Finset.mul_sum]
    have h_swap : ∑ i, ∑ j, |w i j| * b j ^ 2 ≤ C * ∑ j, b j ^ 2 := by
      rw [Finset.sum_comm]
      calc ∑ j, ∑ i, |w i j| * b j ^ 2
          = ∑ j, b j ^ 2 * ∑ i, |w i j| := by
            congr 1; ext j; rw [← Finset.sum_mul]; ring_nf
        _ ≤ ∑ j, b j ^ 2 * C := by
            gcongr with j _; exact col_bound j
        _ = C * ∑ j, b j ^ 2 := by rw [← Finset.sum_mul]; ring
    linarith [mul_le_mul_of_nonneg_left h_swap hR]
  calc (∑ i, ∑ j, w i j * a i * b j) ^ 2
      ≤ |∑ i, ∑ j, w i j * a i * b j| ^ 2 := le_of_eq (sq_abs _).symm
    _ ≤ (∑ i, |a i| * c i) ^ 2 := by gcongr
    _ ≤ (∑ i, a i ^ 2) * (∑ i, c i ^ 2) := h_cs_outer
    _ ≤ (∑ i, a i ^ 2) * (R * C * ∑ j, b j ^ 2) := by gcongr
    _ = R * C * (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by ring

end

end Ramtastic.SchurTest
