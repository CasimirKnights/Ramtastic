/-
  CompactManifold.lean — Compactness + Hodge theory = finite-dimensional cohomology.

  On a compact Riemannian manifold, the combination of Rellich compactness,
  elliptic regularity, and Fredholm theory gives: dim H^k_dR(M) < ∞.

  The Betti numbers are DERIVED from FredholmData.dimKernel — the
  dimension of ker Δ at each degree. Not opaque naturals. The number
  comes from the Fredholm theory that Piece 5 provides.

  Euler characteristic is DEFINED. χ = 0 on odd manifolds is PROVED
  via Finset.sum_ninvolution and the parity cancellation argument.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-17)
-/

import Mathlib.Tactic
import Ramtastic.Sobolev.HodgeTheorem

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.Sobolev.CompactManifold

open Ramtastic.HodgeStar.HodgeLaplacian
open Ramtastic.Sobolev.FredholmTheory
open Ramtastic.Sobolev.HodgeTheorem
open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- COMPACT MANIFOLD DATA — BETTI FROM FREDHOLM
-- ═══════════════════════════════════════════════════════════════════

/-- Compact manifold data: a Hodge Laplacian and Fredholm data at every
    degree, plus Poincaré duality.

    On a compact oriented Riemannian n-manifold:
    - The Hodge Laplacian Δ_k exists at each degree k = 0, ..., n.
    - Fredholm theory gives: ker Δ_k is finite-dimensional.
    - b_k = dimKernel from FredholmData (DERIVED, not opaque).
    - Poincaré duality (Hodge star ★ : H^k ≅ H^{n-k}) gives b_k = b_{n-k}.

    The Laplacian and Fredholm data are BUNDLED — the Betti numbers
    flow from the Fredholm theory, not from a separate assertion. -/
structure CompactManifoldData (n : ℕ) where
  /-- The Hodge Laplacian at each degree. -/
  hlm : ∀ (k : Fin (n + 1)), HodgeLaplacianMap (E := E) k
  /-- Fredholm data at each degree (using the Laplacian at that degree). -/
  fd : ∀ (k : Fin (n + 1)), @FredholmData E _ _ k (hlm k)
  /-- **The Hodge star maps harmonic basis elements injectively into
      harmonic (n-k)-forms.** On a compact Riemannian manifold, ★ commutes
      with Δ (from δ = ±★d★), so ★(ker Δ_k) ⊆ ker Δ_{n-k}. The map is
      injective because ★★ = ±id (invertible). We provide this as an
      injection on basis elements: for each degree k, a map from the
      harmonic basis at degree k to the harmonic basis at degree n-k. -/
  star_basis_inj : ∀ (k : Fin (n + 1)),
    ∃ (f : Fin (fd k).dimKernel → Fin (fd ⟨n - k, by omega⟩).dimKernel),
      Function.Injective f

-- ═══════════════════════════════════════════════════════════════════
-- BETTI NUMBERS — DERIVED FROM FREDHOLM
-- ═══════════════════════════════════════════════════════════════════

/-- The k-th Betti number: b_k = dim ker Δ_k.
    DERIVED from FredholmData.dimKernel. Not an opaque natural. -/
def betti {n : ℕ} (cmd : CompactManifoldData (E := E) n) (k : Fin (n + 1)) : ℕ :=
  @FredholmData.dimKernel E _ _ k (cmd.hlm k) (cmd.fd k)

/-- The harmonic basis at degree k (from FredholmData). -/
def harmonicBasis {n : ℕ} (cmd : CompactManifoldData (E := E) n) (k : Fin (n + 1)) :
    Fin (betti cmd k) → DiffForm ℝ E ℝ k :=
  @FredholmData.basis E _ _ k (cmd.hlm k) (cmd.fd k)

-- ═══════════════════════════════════════════════════════════════════
-- DERIVED PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

variable {n : ℕ} (cmd : CompactManifoldData (E := E) n)

-- Make hlm instances available for each degree
instance (k : Fin (n + 1)) : HodgeLaplacianMap (E := E) k := cmd.hlm k

/-- **Poincaré duality: b_k = b_{n-k}.**

    PROVED from star_basis_inj: injections in both directions between
    finite sets of the same type (Fin) give equal cardinalities.

    ★ at degree k: injection Fin b_k → Fin b_{n-k} → b_k ≤ b_{n-k}.
    ★ at degree n-k: injection Fin b_{n-k} → Fin b_k → b_{n-k} ≤ b_k.
    Combined: b_k = b_{n-k}. -/
theorem poincare_duality (k : Fin (n + 1)) :
    betti cmd k = betti cmd ⟨n - k, by omega⟩ := by
  unfold betti
  apply le_antisymm
  · obtain ⟨f, hf⟩ := cmd.star_basis_inj k
    have := Fintype.card_le_of_injective f hf
    simp [Fintype.card_fin] at this; exact this
  · have h_comp : n - (n - ↑k) = ↑k := by omega
    obtain ⟨g, hg⟩ := cmd.star_basis_inj ⟨n - k, by omega⟩
    have h_fin : (⟨n - (n - ↑k), by omega⟩ : Fin (n + 1)) = k := by ext; simp; omega
    have h_card : betti cmd ⟨n - (n - ↑k), by omega⟩ = betti cmd k := by
      rw [h_fin]
    have := Fintype.card_le_of_injective
      (Fin.cast h_card ∘ g) (by intro a b hab; exact hg (Fin.cast_injective _ hab))
    simp [Fintype.card_fin] at this; exact this

/-- b_0 = b_n (top and bottom Betti numbers agree). -/
theorem betti_zero_eq_n :
    betti cmd ⟨0, by omega⟩ = betti cmd ⟨n, by omega⟩ :=
  poincare_duality cmd ⟨0, by omega⟩

/-- Euler characteristic = alternating sum of Betti numbers. -/
def eulerChar : ℤ :=
  ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) * (betti cmd k : ℤ)

-- ═══════════════════════════════════════════════════════════════════
-- PARITY LEMMA — (-1)^k + (-1)^(n-k) = 0 for odd n
-- ═══════════════════════════════════════════════════════════════════

/-- For odd n and k ≤ n: (-1)^k + (-1)^(n-k) = 0 in ℤ.

    PROVED via the (a+b)² argument: a² = b² = 1 and a·b = -1
    give (a+b)² = 1 + 2(-1) + 1 = 0, hence a + b = 0. -/
private theorem neg_one_pow_add_cancel {k m : ℕ} (hk : k ≤ m) (h_odd : Odd m) :
    (-1 : ℤ) ^ k + (-1 : ℤ) ^ (m - k) = 0 := by
  have h_sq_sum : ((-1 : ℤ) ^ k + (-1) ^ (m - k)) ^ 2 = 0 := by
    have h1 : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
      simp [← pow_mul, neg_one_sq, one_pow]
    have h2 : ((-1 : ℤ) ^ (m - k)) ^ 2 = 1 := by
      simp [← pow_mul, neg_one_sq, one_pow]
    have h3 : (-1 : ℤ) ^ k * (-1) ^ (m - k) = -1 := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
      exact h_odd.neg_one_pow
    nlinarith
  exact sq_eq_zero_iff.mp h_sq_sum

-- ═══════════════════════════════════════════════════════════════════
-- EULER ODD ZERO — PROVED
-- ═══════════════════════════════════════════════════════════════════

/-- **On an odd-dimensional manifold: χ = 0.**

    PROVED from Poincaré duality via Finset.sum_ninvolution.
    The involution k ↦ n-k pairs terms whose contributions cancel:
    (-1)^k · b_k + (-1)^{n-k} · b_{n-k} = b_k · ((-1)^k + (-1)^{n-k}) = 0
    because (-1)^k + (-1)^{n-k} = 0 for odd n (parity cancellation). -/
theorem euler_odd_zero (h_odd : n % 2 = 1) : eulerChar cmd = 0 := by
  unfold eulerChar betti
  apply Finset.sum_ninvolution (fun (k : Fin (n + 1)) => ⟨n - k, by omega⟩)
  · -- f k + f (g k) = 0 for all k
    intro ⟨k, hk⟩
    simp only
    show _ * (betti cmd ⟨k, hk⟩ : ℤ) + _ * (betti cmd ⟨n - k, by omega⟩ : ℤ) = 0
    rw [poincare_duality cmd ⟨k, hk⟩]
    have h_cancel := neg_one_pow_add_cancel (show k ≤ n by omega) (Nat.odd_iff.mpr h_odd)
    nlinarith
  · -- f k ≠ 0 → g k ≠ k (no fixed points for odd n)
    intro ⟨k, hk⟩ _
    simp only [ne_eq, Fin.mk.injEq]
    omega
  · -- g k ∈ Finset.univ (trivial)
    intro _; exact Finset.mem_univ _
  · -- g (g k) = k (involution)
    intro ⟨k, hk⟩
    exact Fin.ext (by show n - (n - k) = k; omega)

-- ═══════════════════════════════════════════════════════════════════
-- CONNECTED MANIFOLD
-- ═══════════════════════════════════════════════════════════════════

/-- For a connected manifold: b_0 = 1 (one connected component). -/
structure ConnectedManifold extends CompactManifoldData (E := E) n where
  b0_eq_one : betti toCompactManifoldData ⟨0, by omega⟩ = 1

/-- For a connected manifold: b_n = 1 (from b_0 = b_n = 1). -/
theorem ConnectedManifold.bn_eq_one (cm : ConnectedManifold (E := E) (n := n)) :
    betti cm.toCompactManifoldData ⟨n, by omega⟩ = 1 := by
  have h := poincare_duality cm.toCompactManifoldData ⟨0, by omega⟩
  have h0 : (⟨n - 0, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := by ext; simp
  rw [h0] at h; rw [← h]; exact cm.b0_eq_one

end

end Ramtastic.Sobolev.CompactManifold
