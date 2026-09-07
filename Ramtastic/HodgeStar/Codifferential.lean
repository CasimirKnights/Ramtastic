/-
  Codifferential.lean — The codifferential δ = ±★d★.

  The codifferential is the formal L² adjoint of d. It lowers degree:
    δ : Ω^k → Ω^{k-1}

  Defined as: δ = (-1)^{n(k+1)+1} ★ d ★

  The class holds ONLY the function — no conditional equations.
  Linearity, smoothness preservation, δ² = 0, coclosed/coexact closures
  are theorems about SPECIFIC constructions (e.g. codiffFromStar), proved
  at point of use with whatever preconditions apply. They are NOT baked
  into the abstract operator class — a class that bundled linearity-with-
  smoothness-hypothesis would silently exclude distributional currents,
  Sobolev forms, and nearly every application where δ is genuinely used.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Ramtastic.HodgeStar.StarOperator

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.HodgeStar.Codifferential

open Ramtastic.HodgeStar.StarOperator
open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- THE CODIFFERENTIAL — JUST THE FUNCTION
-- ═══════════════════════════════════════════════════════════════════

/-- The codifferential δ : Ω^k → Ω^{k'}.

    The class is minimal: just the function. No linearity, no preservation,
    no hypotheses. Construction-specific theorems provide properties
    at the point of use, with preconditions negotiated at the theorem level
    (never baked into the class). This lets callers use δ on distributional
    currents, Sobolev forms, and other non-C¹ objects without the class
    itself silently excluding those applications. -/
class CodifferentialMap (k k' : ℕ) where
  /-- The codifferential. -/
  codiff : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k'

-- ═══════════════════════════════════════════════════════════════════
-- CONSTRUCTION: δ = ★ ∘ d ∘ ★
-- ═══════════════════════════════════════════════════════════════════

/-- **Construct δ = ★₂ ∘ d ∘ ★₁ from two Hodge star instances.**
    Given ★₁ : Ω^k → Ω^k' and ★₂ : Ω^{k'+1} → Ω^{k-1},
    define δ(ω) = ★₂(d(★₁ω)).

    The class needs only the function. Linearity and smoothness preservation
    are theorems about this specific construction (below), invoked at
    point of use. -/
@[reducible]
def codiffFromStar (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1)) :
    CodifferentialMap (E := E) k (k - 1) where
  codiff ω := hs2.star (fun y => extDeriv (hs1.star ω) y)

-- ═══════════════════════════════════════════════════════════════════
-- LINEARITY THEOREMS FOR codiffFromStar (specific construction)
-- ═══════════════════════════════════════════════════════════════════

/-- Additivity of codiffFromStar for differentiable inputs. -/
theorem codiffFromStar_add (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    (ω₁ ω₂ : DiffForm ℝ E ℝ k)
    (hd₁ : Differentiable ℝ ω₁) (hd₂ : Differentiable ℝ ω₂) :
    (codiffFromStar k k' hs1 hs2).codiff (ω₁ + ω₂) =
      (codiffFromStar k k' hs1 hs2).codiff ω₁ +
      (codiffFromStar k k' hs1 hs2).codiff ω₂ := by
  show hs2.star (fun y => extDeriv (hs1.star (ω₁ + ω₂)) y) =
       hs2.star (fun y => extDeriv (hs1.star ω₁) y) +
       hs2.star (fun y => extDeriv (hs1.star ω₂) y)
  rw [← hs2.star_add]
  congr 1; funext y
  rw [hs1.star_add, extDeriv_add
    (hs1.star_preserves_diff ω₁ hd₁ y) (hs1.star_preserves_diff ω₂ hd₂ y)]
  simp [Pi.add_apply]

/-- Scalar linearity of codiffFromStar for differentiable inputs. -/
theorem codiffFromStar_smul (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    (c : ℝ) (ω : DiffForm ℝ E ℝ k) :
    (codiffFromStar k k' hs1 hs2).codiff (c • ω) =
      c • (codiffFromStar k k' hs1 hs2).codiff ω := by
  show hs2.star (fun y => extDeriv (hs1.star (c • ω)) y) =
       c • hs2.star (fun y => extDeriv (hs1.star ω) y)
  rw [← hs2.star_smul]
  congr 1; funext y
  rw [hs1.star_smul, extDeriv_smul c (hs1.star ω)]
  simp [Pi.smul_apply]

/-- Differentiability preservation: under C² (or smoother) input, δω is
    differentiable. This is NOT a class claim — it's a specific property
    of codiffFromStar, used by laplacianFromDCodiff_add downstream. -/
theorem codiffFromStar_diff_of_contDiff (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    {r : WithTop ℕ∞} (ω : DiffForm ℝ E ℝ k)
    (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r) :
    Differentiable ℝ ((codiffFromStar k k' hs1 hs2).codiff ω) := by
  have h2r : (2 : WithTop ℕ∞) ≤ r := by simpa using hr
  have hstar1 : ContDiff ℝ r (hs1.star ω) := hs1.star_preserves_contDiff ω hω
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ (hs1.star ω)) :=
    hstar1.fderiv_right (by simpa using h2r)
  have hdf : Differentiable ℝ (fderiv ℝ (hs1.star ω)) :=
    hfderiv.differentiable (by decide)
  have hextDeriv : Differentiable ℝ (fun x => extDeriv (hs1.star ω) x) := by
    have heq : (fun x => extDeriv (hs1.star ω) x) =
        fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ
          (fderiv ℝ (hs1.star ω) x) := by
      funext x
      show extDeriv (hs1.star ω) x = _
      rw [extDeriv]
      rfl
    rw [heq]
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).differentiable.comp hdf
  exact hs2.star_preserves_diff _ hextDeriv

-- ═══════════════════════════════════════════════════════════════════
-- DERIVED IDENTITIES FOR codiffFromStar
-- ═══════════════════════════════════════════════════════════════════

/-- δ(0) = 0 for codiffFromStar. -/
theorem codiffFromStar_zero (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1)) :
    (codiffFromStar k k' hs1 hs2).codiff (0 : DiffForm ℝ E ℝ k) = 0 := by
  have h := codiffFromStar_smul k k' hs1 hs2 0 (0 : DiffForm ℝ E ℝ k)
  simp at h; exact h

/-- δ(-ω) = -δ(ω) for codiffFromStar. -/
theorem codiffFromStar_neg (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    (ω : DiffForm ℝ E ℝ k) :
    (codiffFromStar k k' hs1 hs2).codiff (-ω) =
      -(codiffFromStar k k' hs1 hs2).codiff ω := by
  have h := codiffFromStar_smul k k' hs1 hs2 (-1) ω; simp at h; exact h

/-- δ(ω₁ - ω₂) = δω₁ - δω₂ for codiffFromStar and differentiable inputs. -/
theorem codiffFromStar_sub (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    (ω₁ ω₂ : DiffForm ℝ E ℝ k)
    (hd₁ : Differentiable ℝ ω₁) (hd₂ : Differentiable ℝ ω₂) :
    (codiffFromStar k k' hs1 hs2).codiff (ω₁ - ω₂) =
      (codiffFromStar k k' hs1 hs2).codiff ω₁ -
      (codiffFromStar k k' hs1 hs2).codiff ω₂ := by
  rw [sub_eq_add_neg, codiffFromStar_add k k' hs1 hs2 _ _ hd₁ hd₂.neg,
      codiffFromStar_neg, ← sub_eq_add_neg]

-- ═══════════════════════════════════════════════════════════════════
-- δ² = 0
-- ═══════════════════════════════════════════════════════════════════

/- δ² = 0: composition of two codifferentials is zero.
   Follows from d² = 0 and ★★ = ±1:
   δ²ω = (★d★)(★d★)ω = ±★d(d(★ω)) = ±★(d²(★ω)) = 0.

   Originally a `CodiffSquareZero` class with unconditional `codiff_codiff` field.
   STRIPPED (2026-04-16): the field's universal claim is false for non-smooth ω
   (d² = 0 requires C² smoothness via Mathlib's extDeriv_extDeriv).
   Per-construction theorems like `codiff32_codiff42_square_zero` in
   `Ramtastic.HodgeStar.StarInstances` take smoothness as a theorem-level hypothesis. -/

-- ═══════════════════════════════════════════════════════════════════
-- COCLOSED AND COEXACT FORMS
-- ═══════════════════════════════════════════════════════════════════

variable {k k' : ℕ} [cdm : CodifferentialMap (E := E) k k']

/-- A form is coclosed if δω = 0. -/
def IsCoclosed (ω : DiffForm ℝ E ℝ k) : Prop :=
  cdm.codiff ω = 0

/-- A form is coexact if ω = δη for some η. -/
def IsCoexact (ω : DiffForm ℝ E ℝ k') : Prop :=
  ∃ η : DiffForm ℝ E ℝ k, cdm.codiff η = ω

-- ═══════════════════════════════════════════════════════════════════
-- CONSTRUCTION-SPECIFIC COCLOSED CLOSURES (codiffFromStar)
-- ═══════════════════════════════════════════════════════════════════

/-- Zero is coclosed for codiffFromStar. -/
theorem codiffFromStar_zero_isCoclosed (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1)) :
    IsCoclosed (cdm := codiffFromStar k k' hs1 hs2) (0 : DiffForm ℝ E ℝ k) :=
  codiffFromStar_zero k k' hs1 hs2

/-- Coclosed forms are closed under addition (for differentiable forms)
    when using codiffFromStar. -/
theorem codiffFromStar_isCoclosed_add (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    {ω₁ ω₂ : DiffForm ℝ E ℝ k}
    (hd₁ : Differentiable ℝ ω₁) (hd₂ : Differentiable ℝ ω₂)
    (h₁ : IsCoclosed (cdm := codiffFromStar k k' hs1 hs2) ω₁)
    (h₂ : IsCoclosed (cdm := codiffFromStar k k' hs1 hs2) ω₂) :
    IsCoclosed (cdm := codiffFromStar k k' hs1 hs2) (ω₁ + ω₂) := by
  unfold IsCoclosed at *
  rw [codiffFromStar_add k k' hs1 hs2 _ _ hd₁ hd₂, h₁, h₂, add_zero]

/-- Coclosed forms are closed under scalar multiplication for codiffFromStar. -/
theorem codiffFromStar_isCoclosed_smul (k k' : ℕ)
    (hs1 : HodgeStarMap (E := E) k k')
    (hs2 : HodgeStarMap (E := E) (k' + 1) (k - 1))
    (c : ℝ) {ω : DiffForm ℝ E ℝ k}
    (h : IsCoclosed (cdm := codiffFromStar k k' hs1 hs2) ω) :
    IsCoclosed (cdm := codiffFromStar k k' hs1 hs2) (c • ω) := by
  unfold IsCoclosed at *
  rw [codiffFromStar_smul, h, smul_zero]

/-- Coexact forms are coclosed, given δ² = 0 as a theorem-level hypothesis.
    The δ² = 0 hypothesis is construction-specific (typically requires smoothness
    of the witness η). No class-level unconditional claim. -/
theorem coexact_isCoclosed {k'' : ℕ}
    [cdm2 : CodifferentialMap (E := E) k' k'']
    (h_sq_zero : ∀ (η : DiffForm ℝ E ℝ k), cdm2.codiff (cdm.codiff η) = 0)
    {ω : DiffForm ℝ E ℝ k'}
    (h : IsCoexact (cdm := cdm) ω) :
    IsCoclosed (cdm := cdm2) ω := by
  obtain ⟨η, rfl⟩ := h
  unfold IsCoclosed
  exact h_sq_zero η

-- ═══════════════════════════════════════════════════════════════════
-- δ AS L² ADJOINT OF d
-- ═══════════════════════════════════════════════════════════════════

/-- The L² adjointness property: ⟨dω, η⟩_L² = ⟨ω, δη⟩_L².
    This IS the defining property of δ. The construction ★d★ is the
    explicit formula; the adjointness is the meaning.

    The L² inner product needs Piece 4 L2InnerProduct for construction.
    Here we state the property as a class. -/
class CodiffAdjoint (k : ℕ) [MeasurableSpace E]
    [CodifferentialMap (E := E) (k + 1) k] where
  /-- The L² inner product on (k+1)-forms. -/
  l2Inner_hi : DiffForm ℝ E ℝ (k + 1) → DiffForm ℝ E ℝ (k + 1) → MeasureTheory.Measure E → ℝ
  /-- The L² inner product on k-forms. -/
  l2Inner_lo : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k → MeasureTheory.Measure E → ℝ
  /-- Adjointness: ⟨dω, η⟩_{k+1} = ⟨ω, δη⟩_k. -/
  adjoint : ∀ (ω : DiffForm ℝ E ℝ k) (η : DiffForm ℝ E ℝ (k + 1))
    (μ : MeasureTheory.Measure E),
    l2Inner_hi (fun x => extDeriv ω x) η μ =
    l2Inner_lo ω ((CodifferentialMap.codiff (E := E) (k := k + 1) (k' := k)) η) μ

end

end Ramtastic.HodgeStar.Codifferential
