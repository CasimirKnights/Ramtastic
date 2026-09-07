/-
  WilsonActionConstruction.lean — explicit Wilson action + non-negativity (AIRTIGHT).

  TASK 6 of the YM ℝ⁴ tower interlocks (per
  `__production_steps/2026_04_28_AIRTIGHT_INTERLOCK_DIRECTIVE.md`).

  Replaces the placeholder `WilsonLatticeYM.wilson_action_nonneg : True`
  in `Craft/YM/LatticeYM.lean:92` with explicit constructive content:
  the actual Wilson action `S_W = β · Σ_□ (1 - Re tr(U_□) / N)`,
  the per-plaquette and total non-negativity theorems, and the
  Boltzmann weight bounds `0 < exp(-S_W) ≤ 1`.

  Discipline (per directive 2026-04-28):
    - No new structures. No new hypothesis fields. No `True`. No `sorry`.
    - Tower-side definitions and derived theorems only.
    - Three Lean kernel axioms only.

  AIRTIGHTNESS:
    - The Wilson action `wilsonAction` is an explicit `ℝ`-valued function of
      (β, N, plaquette trace data). No hypothesis field hides the value.
    - Non-negativity is DERIVED from `0 ≤ β` and the unitary trace bound
      `Re tr(U) ≤ N` (classical fact about unitary matrices in dim N).
    - The trace bound is taken as a hypothesis on the input data (the
      craft side for a specific gauge group like SU(N) supplies the bound
      from the actual unitarity / matrix-norm chain).

  Imports: Mathlib.Tactic, Mathlib.Analysis.SpecialFunctions.Exp,
  Mathlib.Algebra.BigOperators.Basic. No tower or craft dependencies
  yet (TASKS 7, 8, 9 will build on this).

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.7, 2026-04-28)
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Ramtastic.QuantumYM.WilsonActionConstruction

noncomputable section

-- ════════════════════════════════════════════════════════════════
-- I. THE PER-PLAQUETTE WILSON ACTION
-- ════════════════════════════════════════════════════════════════

/-- **The per-plaquette Wilson action:** `β · (1 - Re tr(U_□) / N)`.

    For a compact simple gauge group G ⊂ U(N) and a plaquette `U_□` in G:
    Re tr(U_□) is bounded above by N (each of the N eigenvalues of a unitary
    has modulus 1, so |tr(U)| ≤ N, hence Re tr(U) ≤ N).

    The per-plaquette action is non-negative when β ≥ 0 and the trace bound holds.
    The minimum (= 0) is achieved when U_□ = identity (Re tr = N → action = 0).
    The maximum (= 2β) is achieved when Re tr(U_□) = -N (impossible for SU(2N+1)
    but possible for SU(2N), e.g. -id ∈ SU(2)).

    Reference: Wilson 1974, "Confinement of quarks", Phys. Rev. D 10, 2445. -/
def wilsonPlaquetteAction (β : ℝ) (N : ℕ) (reTrU : ℝ) : ℝ :=
  β * (1 - reTrU / N)

/-- **The per-plaquette Wilson action is non-negative.**

    Conditions:
    - `0 ≤ β` (coupling constant non-negative; in physics β = 2N/g² > 0)
    - `0 < N` (representation dimension is positive)
    - `reTrU ≤ N` (Re tr(U_□) ≤ N for any U_□ in U(N), classical)

    Proof: `1 - reTrU/N ≥ 0` from `reTrU ≤ N` and `0 < N`.
    Times `β ≥ 0` gives non-negative product. -/
theorem wilsonPlaquetteAction_nonneg
    (β : ℝ) (N : ℕ) (reTrU : ℝ)
    (hβ : 0 ≤ β) (hN : 0 < N) (h_bound : reTrU ≤ N) :
    0 ≤ wilsonPlaquetteAction β N reTrU := by
  unfold wilsonPlaquetteAction
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_ratio_le_one : reTrU / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN']
    exact h_bound
  have h_diff_nonneg : 0 ≤ 1 - reTrU / (N : ℝ) := by linarith
  exact mul_nonneg hβ h_diff_nonneg

/-- **The per-plaquette Wilson action vanishes at the identity.**
    When `Re tr(id_N) = N`, the per-plaquette action is exactly 0. -/
theorem wilsonPlaquetteAction_at_identity (β : ℝ) (N : ℕ) (hN : 0 < N) :
    wilsonPlaquetteAction β N (N : ℝ) = 0 := by
  unfold wilsonPlaquetteAction
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  field_simp
  ring

-- ════════════════════════════════════════════════════════════════
-- II. THE TOTAL WILSON ACTION (sum over plaquettes)
-- ════════════════════════════════════════════════════════════════

/-- **The total Wilson action:** sum of per-plaquette actions over all plaquettes.

    `S_W[U] = β · Σ_□ (1 - Re tr(U_□) / N) = Σ_□ wilsonPlaquetteAction β N (Re tr(U_□))`.

    On a finite hypercubic lattice in dimension d with N^d sites: the number of
    plaquettes is d(d-1)/2 · N^d (each site has d(d-1)/2 plaquette types).
    For d = 4, N sites per direction: 6 · N⁴ plaquettes. -/
def wilsonAction (β : ℝ) (N : ℕ) (nPlaq : ℕ)
    (reTrUOfPlaq : Fin nPlaq → ℝ) : ℝ :=
  ∑ i : Fin nPlaq, wilsonPlaquetteAction β N (reTrUOfPlaq i)

/-- **The total Wilson action is non-negative.**

    From `wilsonPlaquetteAction_nonneg` per plaquette, plus `Finset.sum_nonneg`. -/
theorem wilsonAction_nonneg
    (β : ℝ) (N : ℕ) (nPlaq : ℕ) (reTrUOfPlaq : Fin nPlaq → ℝ)
    (hβ : 0 ≤ β) (hN : 0 < N)
    (h_bounds : ∀ i, reTrUOfPlaq i ≤ (N : ℝ)) :
    0 ≤ wilsonAction β N nPlaq reTrUOfPlaq := by
  unfold wilsonAction
  apply Finset.sum_nonneg
  intro i _
  exact wilsonPlaquetteAction_nonneg β N (reTrUOfPlaq i) hβ hN (h_bounds i)

/-- **The total Wilson action vanishes at the identity configuration.**
    When `Re tr(U_□) = N` for every plaquette, the total action is 0. -/
theorem wilsonAction_at_identity_config
    (β : ℝ) (N : ℕ) (nPlaq : ℕ) (hN : 0 < N) :
    wilsonAction β N nPlaq (fun _ => (N : ℝ)) = 0 := by
  unfold wilsonAction
  apply Finset.sum_eq_zero
  intro i _
  exact wilsonPlaquetteAction_at_identity β N hN

-- ════════════════════════════════════════════════════════════════
-- III. THE BOLTZMANN WEIGHT exp(-S_W)
-- ════════════════════════════════════════════════════════════════

/-- **The Boltzmann weight exp(-S_W) is positive.**
    True for any real S_W (exp is strictly positive). -/
theorem wilson_boltzmann_pos (S_W : ℝ) : 0 < Real.exp (-S_W) :=
  Real.exp_pos _

/-- **The Boltzmann weight exp(-S_W) is bounded above by 1 when S_W ≥ 0.**

    Combined with `wilsonAction_nonneg`: for any plaquette configuration with
    bounded traces, the Boltzmann weight is in `(0, 1]`. -/
theorem wilson_boltzmann_le_one (S_W : ℝ) (h : 0 ≤ S_W) :
    Real.exp (-S_W) ≤ 1 := by
  have h_neg : -S_W ≤ 0 := neg_nonpos.mpr h
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  exact Real.exp_le_exp.mpr h_neg

/-- **Boltzmann weight bounds combined.**
    For β ≥ 0, N > 0, and bounded plaquette traces:
    `0 < exp(-S_W) ≤ 1`. -/
theorem wilson_boltzmann_bounds
    (β : ℝ) (N : ℕ) (nPlaq : ℕ) (reTrUOfPlaq : Fin nPlaq → ℝ)
    (hβ : 0 ≤ β) (hN : 0 < N)
    (h_bounds : ∀ i, reTrUOfPlaq i ≤ (N : ℝ)) :
    0 < Real.exp (-wilsonAction β N nPlaq reTrUOfPlaq) ∧
    Real.exp (-wilsonAction β N nPlaq reTrUOfPlaq) ≤ 1 :=
  ⟨wilson_boltzmann_pos _,
   wilson_boltzmann_le_one _
     (wilsonAction_nonneg β N nPlaq reTrUOfPlaq hβ hN h_bounds)⟩

-- ════════════════════════════════════════════════════════════════
-- IV. SUMMARY: WHAT THIS FILE PROVIDES
-- ════════════════════════════════════════════════════════════════

-- WHAT THIS FILE PROVIDES (TASK 6):
--
-- Definitions (explicit, no hypothesis fields):
--   wilsonPlaquetteAction β N reTrU  : ℝ
--   wilsonAction β N nPlaq reTrUOfPlaq : ℝ
--
-- Derived theorems (proved, three Lean kernel axioms only):
--   wilsonPlaquetteAction_nonneg     : per-plaquette ≥ 0 from β≥0 + trace bound
--   wilsonPlaquetteAction_at_identity : per-plaquette = 0 at U_□ = id
--   wilsonAction_nonneg              : total ≥ 0 from per-plaquette ≥ 0
--   wilsonAction_at_identity_config  : total = 0 at U_ℓ = id everywhere
--   wilson_boltzmann_pos             : exp(-S_W) > 0
--   wilson_boltzmann_le_one          : exp(-S_W) ≤ 1 when S_W ≥ 0
--   wilson_boltzmann_bounds          : combined 0 < exp(-S_W) ≤ 1
--
-- NOT INCLUDED in TASK 6 (downstream):
--   - The configuration space G^nLinks with Haar product measure (TASK 8 territory:
--     Glimm-Jaffe inductive limit needs the Haar measure infrastructure).
--   - The partition function Z = ∫ exp(-S_W) dμ as a finite real number
--     (requires Mathlib Haar + finiteness; will be wired in TASK 8 or
--     in the SU(N) craft delivery TASK 10).
--   - The transfer matrix T = exp(-aH) construction (TASK 8 territory).
--
-- WHAT THIS FILE REPLACES:
--   The placeholder field `WilsonLatticeYM.wilson_action_nonneg : True`
--   at `Craft/YM/LatticeYM.lean:92`. The non-negativity is now an explicit
--   theorem about an explicit function, not a hypothesis field.

end

end Ramtastic.QuantumYM.WilsonActionConstruction
