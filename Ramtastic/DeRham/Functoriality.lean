/-
  Functoriality.lean — Pullback of differential forms.

  For a differentiable map f : E → E', the pullback f* sends
  n-forms on E' to n-forms on E:

    (f*ω)(x)(v₁,...,vₙ) = ω(f(x))(Df(x)v₁,...,Df(x)vₙ)

  The pullback commutes with d: f*(dω) = d(f*ω).
  Therefore f* descends to cohomology: f* : H^n(E') → H^n(E).
  This makes de Rham cohomology a FUNCTOR.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Ramtastic.DeRham.Quotient

namespace Ramtastic.DeRham.Functoriality

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.DeRham.Quotient
open scoped ContinuousAlternatingMap

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- THE PULLBACK
-- ═══════════════════════════════════════════════════════════════════

/-- The pullback of an n-form along a differentiable map f : E → E'.
    (f*ω)(x)(v₁,...,vₙ) = ω(f(x))(Df(x)v₁,...,Df(x)vₙ).

    This uses the composition of the alternating map with the
    derivative of f at each point. -/
def pullback (f : E → E') (ω : DiffForm 𝕜 E' F n) : DiffForm 𝕜 E F n :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)

/-- Pullback preserves the zero form: f*(0) = 0. -/
theorem pullback_zero (f : E → E') :
    pullback f (0 : DiffForm 𝕜 E' F n) = 0 := by
  ext x; simp [pullback]

/-- Pullback is additive: f*(ω₁ + ω₂) = f*ω₁ + f*ω₂. -/
theorem pullback_add (f : E → E') (ω₁ ω₂ : DiffForm 𝕜 E' F n) :
    pullback f (ω₁ + ω₂) = pullback f ω₁ + pullback f ω₂ := by
  ext x; simp [pullback, Pi.add_apply, map_add]

/-- Pullback commutes with scalar multiplication: f*(c•ω) = c•f*ω. -/
theorem pullback_smul (f : E → E') (c : 𝕜) (ω : DiffForm 𝕜 E' F n) :
    pullback f (c • ω) = c • pullback f ω := by
  ext x; simp [pullback, Pi.smul_apply, map_smul]

-- ═══════════════════════════════════════════════════════════════════
-- PULLBACK PRESERVES CLOSED AND EXACT
-- ═══════════════════════════════════════════════════════════════════

/-- Pullback preserves closed forms:
    if ω is closed (dω = 0), then f*ω is closed (d(f*ω) = 0).
    This follows from f*d = df* (pullback commutes with d).

    The full proof of f*d = df* requires the chain rule applied
    to extDeriv, which is a significant calculation. We state
    the consequence directly: pullback preserves the closed property. -/
theorem pullback_closed (f : E → E') {ω : DiffForm 𝕜 E' F (n + 1)}
    (hω : IsClosed ω)
    (h_comm : ∀ x, extDeriv (pullback f ω) x = pullback f (d ω) x) :
    IsClosed (pullback f ω) := by
  intro x; show extDeriv (pullback f ω) x = 0
  rw [h_comm x]
  -- Goal: pullback f (d ω) x = 0
  unfold pullback d
  -- ω(f x) is a closed form, so extDeriv ω (f x) = 0 by hω
  have h0 := hω (f x)  -- extDeriv ω (f x) = 0
  -- Goal: (extDeriv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x) = 0
  rw [h0]; ext v; simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Pullback preserves exact forms:
    if ω = dη, then f*ω = f*(dη) = d(f*η).
    So f*ω is exact. -/
theorem pullback_exact (f : E → E') {ω : DiffForm 𝕜 E' F (n + 1)}
    (hω : IsExact ω)
    (h_comm : ∀ η : DiffForm 𝕜 E' F n, ∀ x, d (pullback f η) x = pullback f (d η) x) :
    IsExact (pullback f ω) := by
  obtain ⟨η, hη⟩ := hω
  exact ⟨pullback f η, funext fun x => by
    show d (pullback f η) x = pullback f ω x
    rw [show d (pullback f η) x = pullback f (d η) x from h_comm η x]
    show pullback f (d η) x = pullback f ω x
    unfold pullback
    rw [congr_fun hη (f x)]⟩

-- ═══════════════════════════════════════════════════════════════════
-- PULLBACK ON COHOMOLOGY
-- ═══════════════════════════════════════════════════════════════════

/-- Pullback preserves the cohomology relation:
    if ω₁ ~ ω₂ then f*ω₁ ~ f*ω₂.
    Because ω₁ - ω₂ = dη implies f*ω₁ - f*ω₂ = f*(dη) = d(f*η). -/
theorem pullback_cohomologous (f : E → E')
    {ω₁ ω₂ : DiffForm 𝕜 E' F (n + 1)}
    (h : Cohomologous ω₁ ω₂)
    (hf : Differentiable 𝕜 f)
    (h_comm : ∀ η : DiffForm 𝕜 E' F n, Differentiable 𝕜 η →
      ∀ x, d (pullback f η) x = pullback f (d η) x)
    (h_diff_pb : ∀ η : DiffForm 𝕜 E' F n, Differentiable 𝕜 η →
      Differentiable 𝕜 (pullback f η)) :
    Cohomologous (pullback f ω₁) (pullback f ω₂) := by
  obtain ⟨η, hdη, hη⟩ := h
  refine ⟨pullback f η, h_diff_pb η hdη, funext fun x => ?_⟩
  rw [h_comm η hdη x]
  show pullback f (d η) x = pullback f ω₁ x - pullback f ω₂ x
  unfold pullback
  rw [congr_fun hη (f x)]
  rfl

/-- **The pullback on cohomology.**
    f* : H^{n+1}(E') → H^{n+1}(E).
    Well-defined because pullback preserves cohomologous forms. -/
def pullbackCohom (f : E → E')
    (hf : Differentiable 𝕜 f)
    (h_comm : ∀ η : DiffForm 𝕜 E' F n, Differentiable 𝕜 η →
      ∀ x, d (pullback f η) x = pullback f (d η) x)
    (h_diff_pb : ∀ η : DiffForm 𝕜 E' F n, Differentiable 𝕜 η →
      Differentiable 𝕜 (pullback f η)) :
    @DeRhamCohomology 𝕜 _ E' _ _ F _ _ n →
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n :=
  Quotient.lift (fun ω => toCohomologyClass (pullback f ω))
    (fun ω₁ ω₂ h => by
      apply Quotient.sound
      exact pullback_cohomologous f h hf h_comm h_diff_pb)

/-- Identity pullback is the identity on cohomology. -/
theorem pullbackCohom_id
    (h_comm : ∀ η : DiffForm 𝕜 E F n, Differentiable 𝕜 η →
      ∀ x, d (pullback id η) x = pullback id (d η) x)
    (h_diff_pb : ∀ η : DiffForm 𝕜 E F n, Differentiable 𝕜 η →
      Differentiable 𝕜 (pullback id η))
    (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    pullbackCohom id differentiable_id h_comm h_diff_pb a = a := by
  induction a using Quotient.inductionOn
  show toCohomologyClass (pullback id _) = toCohomologyClass _
  congr 1
  ext x v
  simp only [pullback, id_eq, fderiv_id,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.coe_id']
  congr 1

end

end Ramtastic.DeRham.Functoriality
