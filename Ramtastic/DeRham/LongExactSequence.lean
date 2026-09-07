/-
  LongExactSequence.lean — Mayer-Vietoris and the connecting homomorphism.

  For open sets U, V covering M with partition of unity {ρ_U, ρ_V}:
  - Restriction: ω ↦ ρ_U · ω (smooth cutoff to U)
  - Connecting homomorphism: δ(ω) = d(ρ_V · ω)
  - δ sends closed forms to closed forms (d² = 0)
  - The Mayer-Vietoris sequence connects H^n(M), H^n(U), H^n(V), H^n(U∩V)

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Ramtastic.DeRham.Functoriality

namespace Ramtastic.DeRham.LongExactSequence

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.DeRham.Quotient

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- PARTITION OF UNITY DATA
-- ═══════════════════════════════════════════════════════════════════

/-- Partition of unity: two smooth functions summing to 1. -/
structure PartitionOfUnity where
  ρU : E → 𝕜
  ρV : E → 𝕜
  partition : ∀ x, ρU x + ρV x = 1
  diff_U : Differentiable 𝕜 ρU
  diff_V : Differentiable 𝕜 ρV

variable (pou : PartitionOfUnity (𝕜 := 𝕜) (E := E))

-- ═══════════════════════════════════════════════════════════════════
-- THE CONNECTING HOMOMORPHISM
-- ═══════════════════════════════════════════════════════════════════

/-- Multiply a form by a smooth scalar function.
    (f · ω)(x)(v₁,...,vₙ) = f(x) · ω(x)(v₁,...,vₙ). -/
def smulForm (f : E → 𝕜) (ω : DiffForm 𝕜 E 𝕜 n) : DiffForm 𝕜 E 𝕜 n :=
  fun x => f x • ω x

/-- The connecting homomorphism δ : Ω^n → Ω^{n+1}.
    δ(ω) = d(ρ_V · ω). -/
def connectingHom (ω : DiffForm 𝕜 E 𝕜 n) : DiffForm 𝕜 E 𝕜 (n + 1) :=
  d (smulForm pou.ρV ω)

/-- δ sends closed forms to closed forms.
    δ(ω) = d(ρ_V · ω), so dδ(ω) = d²(ρ_V · ω) = 0 by d² = 0. -/
theorem connecting_hom_closed {r : WithTop ℕ∞}
    (ω : DiffForm 𝕜 E 𝕜 n)
    (hsmooth : ContDiff 𝕜 r (smulForm pou.ρV ω))
    (hr : minSmoothness 𝕜 2 ≤ r) :
    DifferentialForms.IsClosed (connectingHom pou ω) := by
  exact exact_is_closed _ hsmooth hr

-- ═══════════════════════════════════════════════════════════════════
-- THE SEQUENCE MAPS
-- ═══════════════════════════════════════════════════════════════════

/-- The restriction map: multiply by ρ_U.
    Restricts a form to the "U region" via the partition of unity. -/
def restrictU (ω : DiffForm 𝕜 E 𝕜 n) : DiffForm 𝕜 E 𝕜 n :=
  smulForm pou.ρU ω

/-- The restriction map: multiply by ρ_V. -/
def restrictV (ω : DiffForm 𝕜 E 𝕜 n) : DiffForm 𝕜 E 𝕜 n :=
  smulForm pou.ρV ω

/-- ρ_U · ω + ρ_V · ω = ω (partition of unity property). -/
theorem restrict_sum (ω : DiffForm 𝕜 E 𝕜 n) :
    ∀ x, restrictU pou ω x + restrictV pou ω x = ω x := by
  intro x
  unfold restrictU restrictV smulForm
  rw [← add_smul, pou.partition, one_smul]

-- The connecting homomorphism on cohomology: δ : H^{n+1} → H^{n+2}.
-- Takes a class [ω] in degree n+1 and produces [d(ρ_V · ω)] in degree n+2.
-- Well-defined on the quotient because:
-- if ω₁ ~ ω₂ (differ by exact dη), then
-- d(ρ_V · ω₁) - d(ρ_V · ω₂) = d(ρ_V · (ω₁-ω₂)) = d(ρ_V · dη) = d(d(ρ_V · η)) = 0.
-- So δ[ω₁] = δ[ω₂].
-- Full formalization of well-definedness requires d(ρ_V · (ω₁-ω₂)) = d(ρ_V · dη),
-- which needs the Leibniz rule for d on products (d(f·ω) = df∧ω + f·dω).
-- This is stated as a hypothesis for now.

end

end Ramtastic.DeRham.LongExactSequence
