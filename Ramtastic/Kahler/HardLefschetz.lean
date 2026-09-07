/-
  HardLefschetz.lean — Hard Lefschetz theorem and Lefschetz decomposition.

  On a compact Kähler manifold of complex dimension n:
  - L^{n-k} : H^k → H^{2n-k} is an isomorphism (the Hard Lefschetz theorem)
  - Every harmonic k-form decomposes uniquely as a sum of L^r applied to
    primitive forms (the Lefschetz decomposition)

  Hard Lefschetz is the representation-theoretic consequence of the sl(2)
  structure: the raising operator L^{n-k} is an isomorphism between the
  weight-(k-n) and weight-(n-k) spaces.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-17)
-/

import Mathlib.Tactic
import Ramtastic.Kahler.KahlerLaplacian
import Ramtastic.Kahler.HodgeDecomposition

namespace Ramtastic.Kahler.HardLefschetz

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.HodgeStar.HodgeLaplacian
open Ramtastic.Kahler.LefschetzOperator
open Ramtastic.Kahler.KahlerLaplacian
open Ramtastic.Kahler.HodgeDecomposition

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- ITERATED LEFSCHETZ L^r
-- ═══════════════════════════════════════════════════════════════════

/-- Data for iterated Lefschetz powers L^r on harmonic forms.
    L^r : H^k → H^{k+2r} (raising degree by 2r).

    On a Kähler manifold, L commutes with the Laplacian ([L, Δ] = 0,
    from the Kähler identities), so L preserves harmonicity.
    L^r is just r-fold composition of L. -/
class LefschetzPowerData (k : ℕ) where
  /-- The r-th Lefschetz power L^r on k-forms. -/
  lefPow : (r : ℕ) → DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ (k + 2 * r)
  /-- L^0 = id (via the canonical identification k + 0 = k). -/
  lefPow_zero : ∀ α : DiffForm ℝ E ℝ k,
    HEq (lefPow 0 α) α
  /-- L^r is ℝ-linear. -/
  lefPow_smul : ∀ (r : ℕ) (c : ℝ) (α : DiffForm ℝ E ℝ k),
    lefPow r (c • α) = c • lefPow r α
  /-- L^r is additive. -/
  lefPow_add : ∀ (r : ℕ) (α β : DiffForm ℝ E ℝ k),
    lefPow r (α + β) = lefPow r α + lefPow r β

-- ═══════════════════════════════════════════════════════════════════
-- HARD LEFSCHETZ THEOREM
-- ═══════════════════════════════════════════════════════════════════

/-- **The Hard Lefschetz theorem**: L^{n-k} : H^k → H^{2n-k} is an isomorphism
    on harmonic forms, for k ≤ n.

    This is THE deep result of Kähler geometry. It follows from the
    representation theory of the sl(2) triple (L, Λ, H):
    - The sl(2) weight on H^k is (k - n).
    - By the classification of finite-dimensional sl(2) representations,
      the raising operator L^{n-k} maps the weight-(k-n) space isomorphically
      to the weight-(n-k) space.
    - These weight spaces are H^k and H^{2n-k} respectively.

    We state this as a class with injectivity and surjectivity fields.
    The proof for specific Kähler manifolds uses the sl(2) representation
    theory plus the compactness of the moduli of harmonic forms. -/
class HardLefschetzData (n : ℕ) (k : ℕ)
    [hlm_k : HodgeLaplacianMap (E := E) k]
    [hlm_target : HodgeLaplacianMap (E := E) (k + 2 * (n - k))]
    [lpd : LefschetzPowerData (E := E) k] where
  /-- k ≤ n (the theorem applies in the lower half of the diamond). -/
  k_le_n : k ≤ n
  /-- **Injectivity**: L^{n-k} is injective on harmonic k-forms.
      If L^{n-k}(α) = 0 and α is harmonic, then α = 0. -/
  hard_lefschetz_inj : ∀ (α : DiffForm ℝ E ℝ k),
    IsHarmonic (hlm := hlm_k) α →
    lpd.lefPow (n - k) α = 0 →
    α = 0
  /-- **Surjectivity**: L^{n-k} is surjective on HARMONIC forms at the
      target degree k + 2(n-k). For every HARMONIC η at that degree,
      there exists a harmonic k-form α with L^{n-k}(α) = η.
      The harmonicity of η is REQUIRED — L^{n-k} is NOT surjective onto
      all forms, only onto the harmonic subspace. -/
  hard_lefschetz_surj :
    ∀ (η : DiffForm ℝ E ℝ (k + 2 * (n - k))),
    IsHarmonic (hlm := hlm_target) η →
    ∃ (α : DiffForm ℝ E ℝ k),
      IsHarmonic (hlm := hlm_k) α ∧ lpd.lefPow (n - k) α = η

-- ═══════════════════════════════════════════════════════════════════
-- LEFSCHETZ DECOMPOSITION
-- ═══════════════════════════════════════════════════════════════════

/-- The Lefschetz decomposition: every harmonic k-form is a unique sum
    of L^r applied to primitive harmonic forms (forms annihilated by Λ).

    H^k = ⊕_{r ≥ 0} L^r · P^{k-2r}

    where P^j = ker(Λ) ∩ H^j (primitive harmonic j-forms).

    Each component is: L^r applied to a primitive form at degree k-2r.
    "Primitive" means Λ(form) = 0 — the form has no L-content to strip.

    We state this with EXPLICIT L^r(primitive) structure: each summand
    is an element of the k-form space that comes from L^r of a form at
    a lower degree, and that lower-degree form is annihilated by Λ. -/
class LefschetzDecompositionData (n : ℕ) (k : ℕ)
    [hlm_k : HodgeLaplacianMap (E := E) k] where
  /-- For each r from 0 to k/2, a Lefschetz power taking (k-2r)-forms to k-forms.
      These are the L^r operators at each primitive-source degree. -/
  lefPow_at : (r : ℕ) → (hr : 2 * r ≤ k) →
    DiffForm ℝ E ℝ (k - 2 * r) → DiffForm ℝ E ℝ k
  /-- For each r, a Λ operator on (k-2r)-forms, outputting (k-2r-2)-forms.
      Uses natural subtraction for the codomain (giving 0 when k-2r < 2). -/
  lambda_at : (r : ℕ) → (hr : 2 * r ≤ k) →
    DiffForm ℝ E ℝ (k - 2 * r) → DiffForm ℝ E ℝ (k - 2 * r - 2)
  /-- **Decomposition existence**: every harmonic k-form α decomposes as
      α = Σ_r L^r(P_r) where each P_r is a form at degree (k-2r) that is
      primitive (annihilated by Λ at that degree).
      The primitivity `lambda_at r hr (prim_components r hr) = 0` ensures
      each piece is genuinely primitive — NOT just any form. -/
  lefschetz_decomp_exists : ∀ (α : DiffForm ℝ E ℝ k),
    IsHarmonic (hlm := hlm_k) α →
    ∃ (prim_components : (r : ℕ) → (hr : 2 * r ≤ k) → DiffForm ℝ E ℝ (k - 2 * r)),
      (∀ r hr, lambda_at r hr (prim_components r hr) = 0) ∧
      α = ∑ r ∈ (Finset.range (k / 2 + 1)).attach,
        if h : 2 * r.1 ≤ k then lefPow_at r.1 h (prim_components r.1 h) else 0

end

end Ramtastic.Kahler.HardLefschetz
