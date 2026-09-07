/-
  Quotient.lean — De Rham Cohomology: H^n = ker(d) / im(d).

  THE MONEY FILE. 🐟

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Ramtastic.DeRham.ClosedExact

namespace Ramtastic.DeRham.Quotient

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.DeRham.ClosedExact

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- COHOMOLOGOUS
-- ═══════════════════════════════════════════════════════════════════

/-- Two closed (n+1)-forms are cohomologous if their difference is exact.
    η must be differentiable (so dη is well-defined). -/
def Cohomologous (ω₁ ω₂ : DiffForm 𝕜 E F (n + 1)) : Prop :=
  ∃ η : DiffForm 𝕜 E F n, Differentiable 𝕜 η ∧
    d η = fun x => ω₁ x - ω₂ x

theorem cohomologous_refl (ω : DiffForm 𝕜 E F (n + 1)) :
    Cohomologous ω ω := by
  refine ⟨0, differentiable_const 0, funext fun x => ?_⟩
  simp only [sub_self]
  show d 0 x = 0
  unfold d extDeriv
  have : fderiv 𝕜 (0 : E → E [⋀^Fin n]→L[𝕜] F) x = 0 :=
    (hasFDerivAt_const (0 : E [⋀^Fin n]→L[𝕜] F) x).fderiv
  rw [this]; exact map_zero _

theorem cohomologous_symm {ω₁ ω₂ : DiffForm 𝕜 E F (n + 1)}
    (h : Cohomologous ω₁ ω₂) :
    Cohomologous ω₂ ω₁ := by
  obtain ⟨η, hd, hη⟩ := h
  refine ⟨-η, hd.neg, funext fun x => ?_⟩
  have h1 := congr_fun hη x
  show d (-η) x = ω₂ x - ω₁ x
  change extDeriv (-η) x = ω₂ x - ω₁ x
  rw [show (-η : DiffForm 𝕜 E F n) = ((-1 : 𝕜) • η : DiffForm 𝕜 E F n) from by ext; simp]
  rw [extDeriv_smul, neg_one_smul]
  change -(d η x) = ω₂ x - ω₁ x
  rw [h1, neg_sub]

-- ═══════════════════════════════════════════════════════════════════
-- DE RHAM COHOMOLOGY
-- ═══════════════════════════════════════════════════════════════════

def deRhamSetoid : Setoid (DiffForm 𝕜 E F (n + 1)) where
  r := Cohomologous
  iseqv := {
    refl := cohomologous_refl
    symm := fun h => cohomologous_symm h
    trans := fun {ω₁ ω₂ ω₃} ⟨η₁, hd₁, h₁⟩ ⟨η₂, hd₂, h₂⟩ =>
      ⟨η₁ + η₂, hd₁.add hd₂, funext fun x => by
        have hh₁ := congr_fun h₁ x
        have hh₂ := congr_fun h₂ x
        show d (η₁ + η₂) x = ω₁ x - ω₃ x
        change extDeriv (η₁ + η₂) x = ω₁ x - ω₃ x
        rw [extDeriv_add (hd₁.differentiableAt) (hd₂.differentiableAt)]
        change d η₁ x + d η₂ x = ω₁ x - ω₃ x
        rw [hh₁, hh₂, sub_add_sub_cancel]⟩
  }

/-- **De Rham cohomology in degree n+1.**
    H^{n+1}_dR(E, F) = (closed (n+1)-forms) / (cohomologous). -/
def DeRhamCohomology : Type _ :=
  Quotient (@deRhamSetoid 𝕜 _ E _ _ F _ _ n)

/-- Send a form to its cohomology class. -/
def toCohomologyClass (ω : DiffForm 𝕜 E F (n + 1)) :
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n :=
  Quotient.mk (@deRhamSetoid 𝕜 _ E _ _ F _ _ n) ω

/-- Two forms give the same class iff cohomologous. -/
theorem class_eq_iff (ω₁ ω₂ : DiffForm 𝕜 E F (n + 1)) :
    toCohomologyClass ω₁ = toCohomologyClass ω₂ ↔
    Cohomologous ω₁ ω₂ := by
  unfold toCohomologyClass; exact Quotient.eq

-- ═══════════════════════════════════════════════════════════════════
-- VECTOR SPACE STRUCTURE ON COHOMOLOGY
-- ═══════════════════════════════════════════════════════════════════

/-- Addition on cohomology classes: [ω₁] + [ω₂] = [ω₁ + ω₂].
    Well-defined: if ω₁ ~ ω₁' and ω₂ ~ ω₂', then ω₁+ω₂ ~ ω₁'+ω₂'.
    Proof: (ω₁+ω₂) - (ω₁'+ω₂') = (ω₁-ω₁') + (ω₂-ω₂') = dη₁ + dη₂ = d(η₁+η₂). -/
def cohomAdd :
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n →
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n →
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n :=
  Quotient.lift₂ (fun ω₁ ω₂ => toCohomologyClass (ω₁ + ω₂))
    (fun ω₁ ω₂ ω₁' ω₂' h₁ h₂ => by
      simp only [toCohomologyClass]
      apply Quotient.sound
      obtain ⟨η₁, hd₁, hη₁⟩ := h₁
      obtain ⟨η₂, hd₂, hη₂⟩ := h₂
      exact ⟨η₁ + η₂, hd₁.add hd₂, funext fun x => by
        have hh₁ := congr_fun hη₁ x
        have hh₂ := congr_fun hη₂ x
        show d (η₁ + η₂) x = (ω₁ + ω₂) x - (ω₁' + ω₂') x
        change extDeriv (η₁ + η₂) x = (ω₁ + ω₂) x - (ω₁' + ω₂') x
        rw [extDeriv_add hd₁.differentiableAt hd₂.differentiableAt]
        simp only [Pi.add_apply, Pi.sub_apply] at *
        change d η₁ x + d η₂ x = (ω₁ x + ω₂ x) - (ω₁' x + ω₂' x)
        rw [hh₁, hh₂]; abel⟩)

/-- Scalar multiplication on cohomology classes: c • [ω] = [c • ω].
    Well-defined: if ω ~ ω', then cω ~ cω'.
    Proof: cω - cω' = c(ω - ω') = c·dη = d(cη). -/
def cohomSmul (c : 𝕜) :
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n →
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n :=
  Quotient.lift (fun ω => toCohomologyClass (c • ω))
    (fun ω ω' h => by
      simp only [toCohomologyClass]
      apply Quotient.sound
      obtain ⟨η, hd, hη⟩ := h
      exact ⟨c • η, hd.const_smul c, funext fun x => by
        have hh := congr_fun hη x
        show d (c • η) x = (c • ω) x - (c • ω') x
        change extDeriv (c • η) x = c • ω x - c • ω' x
        rw [extDeriv_smul]
        change c • d η x = c • ω x - c • ω' x
        rw [hh, smul_sub]⟩)

/-- The zero cohomology class: [0]. -/
def cohomZero : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n :=
  toCohomologyClass 0

/-- Negation on cohomology: -[ω] = [-ω]. -/
def cohomNeg :
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n →
    @DeRhamCohomology 𝕜 _ E _ _ F _ _ n :=
  Quotient.lift (fun ω => toCohomologyClass (-ω))
    (fun ω ω' h => by
      apply Quotient.sound
      obtain ⟨η, hd, hη⟩ := h
      exact ⟨-η, hd.neg, funext fun x => by
        have hh := congr_fun hη x
        change extDeriv (-η) x = (-ω) x - (-ω') x
        rw [show (-η : DiffForm 𝕜 E F n) = ((-1 : 𝕜) • η) from by ext; simp]
        rw [extDeriv_smul]; change (-1 : 𝕜) • d η x = -ω x - (-ω' x)
        simp only [neg_one_smul, Pi.neg_apply, neg_sub_neg]
        change -(d η x) = ω' x - ω x
        rw [hh, neg_sub]⟩)

/-- Add instance on DeRhamCohomology. -/
instance instAddDeRham : Add (@DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :=
  ⟨cohomAdd⟩

/-- Neg instance on DeRhamCohomology. -/
instance instNegDeRham : Neg (@DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :=
  ⟨cohomNeg⟩

/-- Zero instance on DeRhamCohomology. -/
instance instZeroDeRham : Zero (@DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :=
  ⟨cohomZero⟩

/-- SMul instance on DeRhamCohomology. -/
instance instSMulDeRham : SMul 𝕜 (@DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :=
  ⟨cohomSmul⟩

-- ═══════════════════════════════════════════════════════════════════
-- AddCommGroup INSTANCE
-- ═══════════════════════════════════════════════════════════════════

private theorem cohom_add_assoc (a b c : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    a + b + c = a + (b + c) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp [add_assoc]

private theorem cohom_zero_add (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    0 + a = a := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp

private theorem cohom_add_zero (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    a + 0 = a := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp

private theorem cohom_add_comm (a b : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    a + b = b + a := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp [add_comm]

private theorem cohom_neg_add (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    -a + a = 0 := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp

instance instAddCommGroupDeRham :
    AddCommGroup (@DeRhamCohomology 𝕜 _ E _ _ F _ _ n) where
  add_assoc := cohom_add_assoc
  zero_add := cohom_zero_add
  add_zero := cohom_add_zero
  add_comm := cohom_add_comm
  neg_add_cancel := cohom_neg_add
  nsmul := nsmulRec
  zsmul := zsmulRec

-- ═══════════════════════════════════════════════════════════════════
-- Module 𝕜 INSTANCE
-- ═══════════════════════════════════════════════════════════════════

private theorem cohom_one_smul (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    (1 : 𝕜) • a = a := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp

private theorem cohom_mul_smul (r s : 𝕜) (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    (r * s) • a = r • s • a := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp [mul_smul]

private theorem cohom_smul_add (r : 𝕜) (a b : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    r • (a + b) = r • a + r • b := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp [smul_add]

private theorem cohom_add_smul (r s : 𝕜) (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    (r + s) • a = r • a + s • a := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp [add_smul]

private theorem cohom_zero_smul (a : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) :
    (0 : 𝕜) • a = 0 := by
  induction a using Quotient.inductionOn
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp

private theorem cohom_smul_zero (r : 𝕜) :
    r • (0 : @DeRhamCohomology 𝕜 _ E _ _ F _ _ n) = 0 := by
  show toCohomologyClass _ = toCohomologyClass _
  congr 1; ext; simp

instance instModuleDeRham :
    Module 𝕜 (@DeRhamCohomology 𝕜 _ E _ _ F _ _ n) where
  one_smul := cohom_one_smul
  mul_smul := cohom_mul_smul
  smul_add := cohom_smul_add
  add_smul := cohom_add_smul
  smul_zero := fun r => cohom_smul_zero r
  zero_smul := cohom_zero_smul

end

end Ramtastic.DeRham.Quotient
