/-
  HodgeLaplacian.lean — The Hodge Laplacian Δ = dδ + δd.

  The Hodge Laplacian combines d (exterior derivative) and δ (codifferential).
  On k-forms: Δ : Ω^k → Ω^k (preserves degree).

  Key properties:
  - Δ is self-adjoint: ⟨Δω, η⟩ = ⟨ω, Δη⟩
  - Δ is nonneg: ⟨Δω, ω⟩ ≥ 0
  - Harmonic forms: ker(Δ) = ker(d) ∩ ker(δ) (on compact manifolds)
  - Δω = 0 iff dω = 0 and δω = 0

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Ramtastic.HodgeStar.Codifferential

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.HodgeStar.HodgeLaplacian

open Ramtastic.HodgeStar.StarOperator
open Ramtastic.HodgeStar.Codifferential
open Ramtastic.DeRham.DifferentialForms

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- THE HODGE LAPLACIAN
-- ═══════════════════════════════════════════════════════════════════

/-- The Hodge Laplacian Δ = dδ + δd on k-forms.
    d : Ω^k → Ω^{k+1} (exterior derivative)
    δ : Ω^k → Ω^{k-1} (codifferential)
    δd : Ω^k → Ω^k (d raises, δ lowers back)
    dδ : Ω^k → Ω^k (δ lowers, d raises back)
    Δ = dδ + δd : Ω^k → Ω^k (preserves degree).

    The class holds only the function. No restrictions, no conditional
    equations, no hypotheses. The Laplacian is TOTAL on all of DiffForm —
    Mathlib's fderiv is total, so extDeriv is total, so Δ is total.

    Properties like linearity, self-adjointness, harmonic decomposition
    are theorems about specific constructions (e.g. laplacianFromDCodiff),
    proved at point of use with whatever preconditions apply. They are
    NOT baked into the abstract operator class — a class that bundled
    linearity-with-smoothness-hypothesis would silently exclude
    distributional forms, Sobolev spaces, path-integral measures, and
    nearly every application where Δ is genuinely used. -/
class HodgeLaplacianMap (k : ℕ) where
  /-- The Hodge Laplacian. -/
  laplacian : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k

-- ═══════════════════════════════════════════════════════════════════
-- CONSTRUCTION: Δ = dδ + δd
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: `Differentiable ℝ (extDeriv ω)` follows from ContDiff r ω with r ≥ 2.
    extDeriv = alternatizeUncurryFinCLM ∘ fderiv. fderiv preserves ContDiff (dropping 1).
    For r ≥ 2: fderiv ω is ContDiff 1, hence Differentiable. CLM composition preserves. -/
theorem differentiable_extDeriv_of_contDiff {n : ℕ} {r : WithTop ℕ∞}
    (ω : DiffForm ℝ E ℝ n) (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r) :
    Differentiable ℝ (fun x => extDeriv ω x) := by
  have h2r : (2 : WithTop ℕ∞) ≤ r := by simpa using hr
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ ω) := hω.fderiv_right (by simpa using h2r)
  have hdf : Differentiable ℝ (fderiv ℝ ω) := hfderiv.differentiable (by decide)
  have heq : (fun x => extDeriv ω x) =
      fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ (fderiv ℝ ω x) := by
    funext x; show extDeriv ω x = _; rw [extDeriv]; rfl
  rw [heq]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).differentiable.comp hdf

/-- **Construct the Hodge Laplacian from d and δ.**
    Δω = d(δω) + δ(dω).

    The class only needs the function. This construction supplies it.
    Linearity and other properties are proved as separate theorems
    about this specific construction (see laplacianFromDCodiff_add below),
    at the point of use, with whatever preconditions apply. -/
@[reducible]
def laplacianFromDCodiff (m : ℕ)
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1)) :
    HodgeLaplacianMap (E := E) (m + 1) where
  laplacian ω := (fun x => extDeriv (codiff_lo.codiff ω) x) +
                 codiff_hi.codiff (fun x => extDeriv ω x)

-- ═══════════════════════════════════════════════════════════════════
-- LINEARITY THEOREMS FOR laplacianFromDCodiff (specific construction)
-- ═══════════════════════════════════════════════════════════════════

/-- Additivity of laplacianFromDCodiff for C² (or smoother) inputs.

    This theorem takes the linearity + smoothness-preservation properties of
    codiff_lo and codiff_hi as parameters. These properties live at the
    theorem level (not in the CodifferentialMap class itself), so callers
    can use this with codiff operators that do NOT satisfy strict
    differentiability hypotheses (e.g. operators on distributional currents,
    Sobolev forms). Users invoking this with codiffFromStar-based codiffs
    pass `codiffFromStar_add`, `codiffFromStar_smul`, and
    `codiffFromStar_diff_of_contDiff` to discharge the hypotheses. -/
theorem laplacianFromDCodiff_add (m : ℕ)
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_add : ∀ ω₁ ω₂ : DiffForm ℝ E ℝ (m + 1),
      Differentiable ℝ ω₁ → Differentiable ℝ ω₂ →
      codiff_lo.codiff (ω₁ + ω₂) = codiff_lo.codiff ω₁ + codiff_lo.codiff ω₂)
    (lo_diff : ∀ {r : WithTop ℕ∞} (ω : DiffForm ℝ E ℝ (m + 1)),
      ContDiff ℝ r ω → minSmoothness ℝ 2 ≤ r → Differentiable ℝ (codiff_lo.codiff ω))
    (hi_add : ∀ η₁ η₂ : DiffForm ℝ E ℝ (m + 2),
      Differentiable ℝ η₁ → Differentiable ℝ η₂ →
      codiff_hi.codiff (η₁ + η₂) = codiff_hi.codiff η₁ + codiff_hi.codiff η₂)
    (ω₁ ω₂ : DiffForm ℝ E ℝ (m + 1)) (r : WithTop ℕ∞)
    (hω₁ : ContDiff ℝ r ω₁) (hω₂ : ContDiff ℝ r ω₂) (hr : minSmoothness ℝ 2 ≤ r) :
    (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian (ω₁ + ω₂) =
      (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian ω₁ +
      (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian ω₂ := by
  have h2r : (2 : WithTop ℕ∞) ≤ r := by simpa using hr
  have hrne : r ≠ 0 := fun h => by rw [h] at h2r; exact absurd h2r (by decide)
  have hd₁ : Differentiable ℝ ω₁ := hω₁.differentiable hrne
  have hd₂ : Differentiable ℝ ω₂ := hω₂.differentiable hrne
  have hcd₁ : Differentiable ℝ (codiff_lo.codiff ω₁) := lo_diff ω₁ hω₁ hr
  have hcd₂ : Differentiable ℝ (codiff_lo.codiff ω₂) := lo_diff ω₂ hω₂ hr
  have hdω₁ : Differentiable ℝ (fun x => extDeriv ω₁ x) :=
    differentiable_extDeriv_of_contDiff ω₁ hω₁ hr
  have hdω₂ : Differentiable ℝ (fun x => extDeriv ω₂ x) :=
    differentiable_extDeriv_of_contDiff ω₂ hω₂ hr
  have h1 := lo_add ω₁ ω₂ hd₁ hd₂
  have h2 : (fun x => extDeriv (ω₁ + ω₂) x) =
      (fun x => extDeriv ω₁ x) + (fun x => extDeriv ω₂ x) :=
    funext (fun y => extDeriv_add (hd₁ y) (hd₂ y))
  have h3 := hi_add _ _ hdω₁ hdω₂
  have h4 : ∀ x, extDeriv (codiff_lo.codiff ω₁ + codiff_lo.codiff ω₂) x =
      extDeriv (codiff_lo.codiff ω₁) x + extDeriv (codiff_lo.codiff ω₂) x :=
    fun x => extDeriv_add (hcd₁ x) (hcd₂ x)
  show (fun x => extDeriv (codiff_lo.codiff (ω₁ + ω₂)) x) +
        codiff_hi.codiff (fun x => extDeriv (ω₁ + ω₂) x) =
      ((fun x => extDeriv (codiff_lo.codiff ω₁) x) +
        codiff_hi.codiff (fun x => extDeriv ω₁ x)) +
      ((fun x => extDeriv (codiff_lo.codiff ω₂) x) +
        codiff_hi.codiff (fun x => extDeriv ω₂ x))
  rw [h1, h2, h3]
  ext x v
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply, h4 x]
  ring

/-- Scalar linearity of laplacianFromDCodiff for C² (or smoother) inputs.
    Takes linearity of codiff_lo and codiff_hi as theorem-level hypotheses. -/
theorem laplacianFromDCodiff_smul (m : ℕ)
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_smul : ∀ (c : ℝ) (ω : DiffForm ℝ E ℝ (m + 1)),
      codiff_lo.codiff (c • ω) = c • codiff_lo.codiff ω)
    (hi_smul : ∀ (c : ℝ) (η : DiffForm ℝ E ℝ (m + 2)),
      codiff_hi.codiff (c • η) = c • codiff_hi.codiff η)
    (c : ℝ) (ω : DiffForm ℝ E ℝ (m + 1)) (r : WithTop ℕ∞)
    (_hω : ContDiff ℝ r ω) (_hr : minSmoothness ℝ 2 ≤ r) :
    (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian (c • ω) =
      c • (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian ω := by
  have h1 := lo_smul c ω
  have h2 : (fun x => extDeriv (c • ω) x) = c • (fun x => extDeriv ω x) :=
    funext (fun _ => extDeriv_smul c ω)
  have h3 := hi_smul c (fun x => extDeriv ω x)
  show (fun x => extDeriv (codiff_lo.codiff (c • ω)) x) +
        codiff_hi.codiff (fun x => extDeriv (c • ω) x) =
      c • ((fun x => extDeriv (codiff_lo.codiff ω) x) +
        codiff_hi.codiff (fun x => extDeriv ω x))
  rw [h1, h2, h3]
  ext x v
  simp only [Pi.add_apply, Pi.smul_apply, extDeriv_smul,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul]
  ring

variable {k : ℕ} [hlm : HodgeLaplacianMap (E := E) k]

-- ═══════════════════════════════════════════════════════════════════
-- HARMONIC FORMS
-- ═══════════════════════════════════════════════════════════════════

/-- A form is harmonic if Δω = 0. -/
def IsHarmonic (ω : DiffForm ℝ E ℝ k) : Prop :=
  hlm.laplacian ω = 0

-- ═══════════════════════════════════════════════════════════════════
-- CONSTRUCTION-SPECIFIC HARMONIC CLOSURE THEOREMS
-- ═══════════════════════════════════════════════════════════════════
-- These theorems hold for laplacianFromDCodiff specifically, since it
-- provides linearity via laplacianFromDCodiff_add/smul. They are NOT
-- class-level claims — the class only holds the function.

/-- Δ(0) = 0 for laplacianFromDCodiff. Zero is smooth at all levels.
    Takes the scalar-linearity properties of codiff_lo and codiff_hi
    as hypotheses (theorem-level, not class-level). -/
theorem laplacianFromDCodiff_zero {m : ℕ}
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_smul : ∀ (c : ℝ) (ω : DiffForm ℝ E ℝ (m + 1)),
      codiff_lo.codiff (c • ω) = c • codiff_lo.codiff ω)
    (hi_smul : ∀ (c : ℝ) (η : DiffForm ℝ E ℝ (m + 2)),
      codiff_hi.codiff (c • η) = c • codiff_hi.codiff η) :
    (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian
      (0 : DiffForm ℝ E ℝ (m + 1)) = 0 := by
  have h := laplacianFromDCodiff_smul m codiff_lo codiff_hi lo_smul hi_smul 0
    (0 : DiffForm ℝ E ℝ (m + 1)) (minSmoothness ℝ 2) contDiff_const (le_refl _)
  simp at h; exact h

/-- Δ(-ω) = -Δ(ω) for laplacianFromDCodiff and C² inputs. -/
theorem laplacianFromDCodiff_neg {m : ℕ}
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_smul : ∀ (c : ℝ) (ω : DiffForm ℝ E ℝ (m + 1)),
      codiff_lo.codiff (c • ω) = c • codiff_lo.codiff ω)
    (hi_smul : ∀ (c : ℝ) (η : DiffForm ℝ E ℝ (m + 2)),
      codiff_hi.codiff (c • η) = c • codiff_hi.codiff η)
    (r : WithTop ℕ∞) (ω : DiffForm ℝ E ℝ (m + 1))
    (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r) :
    (laplacianFromDCodiff m codiff_lo codiff_hi).laplacian (-ω) =
      -(laplacianFromDCodiff m codiff_lo codiff_hi).laplacian ω := by
  have h := laplacianFromDCodiff_smul m codiff_lo codiff_hi lo_smul hi_smul (-1) ω r hω hr
  simp at h; exact h

/-- Zero is harmonic for laplacianFromDCodiff. -/
theorem laplacianFromDCodiff_zero_isHarmonic {m : ℕ}
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_smul : ∀ (c : ℝ) (ω : DiffForm ℝ E ℝ (m + 1)),
      codiff_lo.codiff (c • ω) = c • codiff_lo.codiff ω)
    (hi_smul : ∀ (c : ℝ) (η : DiffForm ℝ E ℝ (m + 2)),
      codiff_hi.codiff (c • η) = c • codiff_hi.codiff η) :
    IsHarmonic (hlm := laplacianFromDCodiff m codiff_lo codiff_hi)
      (0 : DiffForm ℝ E ℝ (m + 1)) :=
  laplacianFromDCodiff_zero codiff_lo codiff_hi lo_smul hi_smul

/-- Harmonic forms are closed under addition (for C²-smooth forms)
    when using laplacianFromDCodiff. Takes codiff linearity + preservation
    as theorem-level hypotheses. -/
theorem laplacianFromDCodiff_isHarmonic_add {m : ℕ}
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_add : ∀ ω₁ ω₂ : DiffForm ℝ E ℝ (m + 1),
      Differentiable ℝ ω₁ → Differentiable ℝ ω₂ →
      codiff_lo.codiff (ω₁ + ω₂) = codiff_lo.codiff ω₁ + codiff_lo.codiff ω₂)
    (lo_diff : ∀ {r : WithTop ℕ∞} (ω : DiffForm ℝ E ℝ (m + 1)),
      ContDiff ℝ r ω → minSmoothness ℝ 2 ≤ r → Differentiable ℝ (codiff_lo.codiff ω))
    (hi_add : ∀ η₁ η₂ : DiffForm ℝ E ℝ (m + 2),
      Differentiable ℝ η₁ → Differentiable ℝ η₂ →
      codiff_hi.codiff (η₁ + η₂) = codiff_hi.codiff η₁ + codiff_hi.codiff η₂)
    (r : WithTop ℕ∞) {ω₁ ω₂ : DiffForm ℝ E ℝ (m + 1)}
    (hω₁ : ContDiff ℝ r ω₁) (hω₂ : ContDiff ℝ r ω₂) (hr : minSmoothness ℝ 2 ≤ r)
    (h₁ : IsHarmonic (hlm := laplacianFromDCodiff m codiff_lo codiff_hi) ω₁)
    (h₂ : IsHarmonic (hlm := laplacianFromDCodiff m codiff_lo codiff_hi) ω₂) :
    IsHarmonic (hlm := laplacianFromDCodiff m codiff_lo codiff_hi) (ω₁ + ω₂) := by
  unfold IsHarmonic at *
  rw [laplacianFromDCodiff_add m codiff_lo codiff_hi lo_add lo_diff hi_add
    ω₁ ω₂ r hω₁ hω₂ hr, h₁, h₂, add_zero]

/-- Harmonic forms are closed under scalar multiplication (for C²-smooth forms)
    when using laplacianFromDCodiff. -/
theorem laplacianFromDCodiff_isHarmonic_smul {m : ℕ}
    (codiff_lo : CodifferentialMap (E := E) (m + 1) m)
    (codiff_hi : CodifferentialMap (E := E) (m + 2) (m + 1))
    (lo_smul : ∀ (c : ℝ) (ω : DiffForm ℝ E ℝ (m + 1)),
      codiff_lo.codiff (c • ω) = c • codiff_lo.codiff ω)
    (hi_smul : ∀ (c : ℝ) (η : DiffForm ℝ E ℝ (m + 2)),
      codiff_hi.codiff (c • η) = c • codiff_hi.codiff η)
    (r : WithTop ℕ∞) (c : ℝ) {ω : DiffForm ℝ E ℝ (m + 1)}
    (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r)
    (h : IsHarmonic (hlm := laplacianFromDCodiff m codiff_lo codiff_hi) ω) :
    IsHarmonic (hlm := laplacianFromDCodiff m codiff_lo codiff_hi) (c • ω) := by
  unfold IsHarmonic at *
  rw [laplacianFromDCodiff_smul m codiff_lo codiff_hi lo_smul hi_smul c ω r hω hr,
    h, smul_zero]

-- ═══════════════════════════════════════════════════════════════════
-- HARMONIC = CLOSED ∧ COCLOSED
-- ═══════════════════════════════════════════════════════════════════

/-- On compact manifolds, Δω = 0 iff dω = 0 and δω = 0.
    The key fact: ⟨Δω, ω⟩ = ‖dω‖² + ‖δω‖² ≥ 0.
    So Δω = 0 ⟹ dω = 0 and δω = 0.

    This connects harmonic forms to de Rham cohomology:
    every cohomology class has a unique harmonic representative. -/
class HarmonicIffClosedCoclosed (k : ℕ)
    [hlm : HodgeLaplacianMap (E := E) k]
    [cdm : CodifferentialMap (E := E) k (k - 1)] where
  /-- Harmonic implies closed. -/
  harmonic_isClosed : ∀ (ω : DiffForm ℝ E ℝ k),
    IsHarmonic (hlm := hlm) ω → IsClosed ω
  /-- Harmonic implies coclosed. -/
  harmonic_isCoclosed : ∀ (ω : DiffForm ℝ E ℝ k),
    IsHarmonic (hlm := hlm) ω → IsCoclosed (cdm := cdm) ω
  /-- Closed and coclosed implies harmonic. -/
  closedCoclosed_isHarmonic : ∀ (ω : DiffForm ℝ E ℝ k),
    IsClosed ω → IsCoclosed (cdm := cdm) ω → IsHarmonic (hlm := hlm) ω

-- ═══════════════════════════════════════════════════════════════════
-- NONNEG AND SELF-ADJOINTNESS
-- ═══════════════════════════════════════════════════════════════════

/-- The Hodge Laplacian is nonneg: ⟨Δω, ω⟩ ≥ 0.
    This follows from Δ = dδ + δd and ⟨Δω,ω⟩ = ‖dω‖² + ‖δω‖².
    Self-adjointness: ⟨Δω, η⟩ = ⟨ω, Δη⟩.
    Both require the L² inner product (Piece 4: L2InnerProduct). -/
class LaplacianSelfAdjoint (k : ℕ) [MeasurableSpace E]
    [hlm : HodgeLaplacianMap (E := E) k] where
  /-- The L² inner product on k-forms. -/
  l2Inner : DiffForm ℝ E ℝ k → DiffForm ℝ E ℝ k → MeasureTheory.Measure E → ℝ
  /-- Self-adjointness: ⟨Δω, η⟩ = ⟨ω, Δη⟩. -/
  selfAdjoint : ∀ (ω η : DiffForm ℝ E ℝ k) (μ : MeasureTheory.Measure E),
    l2Inner (hlm.laplacian ω) η μ = l2Inner ω (hlm.laplacian η) μ
  /-- Nonnegativity: ⟨Δω, ω⟩ ≥ 0. -/
  nonneg : ∀ (ω : DiffForm ℝ E ℝ k) (μ : MeasureTheory.Measure E),
    0 ≤ l2Inner (hlm.laplacian ω) ω μ

end

end Ramtastic.HodgeStar.HodgeLaplacian
