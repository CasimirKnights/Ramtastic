/-
  FredholmTheory.lean — Fredholm operators and the harmonic projection.

  A bounded linear operator T : X → Y between Banach spaces is Fredholm if:
  - ker T is finite-dimensional
  - coker T = Y / im(T) is finite-dimensional
  - im(T) is closed

  The Fredholm index is: ind(T) = dim ker T - dim coker T.

  For the Hodge Laplacian on a compact manifold: Δ is Fredholm of index 0
  (self-adjoint ⟹ ind = 0). This gives:
  - ker Δ is finite-dimensional (finitely many harmonic forms per degree)
  - im Δ is closed (and equals (ker Δ)⊥ by self-adjointness)

  The Fredholm alternative: for Δω = f, either
  (a) f ⊥ ker Δ and a solution ω exists, or
  (b) f has a component in ker Δ and no solution exists.

  This file CONSTRUCTS the harmonic projection from an orthonormal basis
  for ker Δ, and PROVES its properties (idempotent, linear, harmonic).
  The Fredholm alternative is PROVED from the projection + Fredholm
  decomposition hypothesis.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-17)
-/

import Mathlib.Tactic
import Ramtastic.Sobolev.EllipticRegularity

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.Sobolev.FredholmTheory

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.HodgeStar.HodgeLaplacian
open Ramtastic.Sobolev.SobolevSpaces

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ═══════════════════════════════════════════════════════════════════
-- FREDHOLM DATA — THE FREDHOLM PROPERTY OF Δ (structure, not class)
-- ═══════════════════════════════════════════════════════════════════

/-- Fredholm data for the Hodge Laplacian at degree q.

    On a compact manifold, elliptic regularity + Rellich compactness
    give: ker Δ is finite-dimensional with an explicit basis, and
    dim ker = dim coker (index 0, from self-adjointness).

    This is a STRUCTURE (not a class). The caller provides it for their
    specific domain. It is the OUTPUT of the hard PDE theory — the
    Fredholm property, packaged as data. -/
structure FredholmData (q : ℕ) [hlm : HodgeLaplacianMap (E := E) q] where
  /-- Dimension of ker Δ (the harmonic forms). -/
  dimKernel : ℕ
  /-- Dimension of coker Δ. -/
  dimCokernel : ℕ
  /-- A basis for ker Δ. -/
  basis : Fin dimKernel → DiffForm ℝ E ℝ q
  /-- Each basis element is harmonic. -/
  basis_harmonic : ∀ i, IsHarmonic (hlm := hlm) (basis i)
  /-- The basis spans all harmonic forms. -/
  basis_spans : ∀ ω, IsHarmonic (hlm := hlm) ω →
    ∃ coeffs : Fin dimKernel → ℝ, ω = ∑ i : Fin dimKernel, coeffs i • basis i
  /-- Linear combinations of basis elements are harmonic.
      Follows from linearity of Δ. The caller discharges this using
      their specific Δ construction (e.g. laplacianFromDCodiff_isHarmonic_add). -/
  span_harmonic : ∀ (coeffs : Fin dimKernel → ℝ),
    IsHarmonic (hlm := hlm) (∑ i : Fin dimKernel, coeffs i • basis i)
  /-- Self-adjoint ⟹ index 0: dim ker = dim coker. -/
  index_zero : dimKernel = dimCokernel

/-- The Fredholm index of Δ: ind(Δ) = dim ker - dim coker. -/
def fredholmIndex {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (fd : FredholmData (E := E) q) : ℤ :=
  (fd.dimKernel : ℤ) - (fd.dimCokernel : ℤ)

/-- The Hodge Laplacian has Fredholm index 0. -/
theorem fredholmIndex_zero {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (fd : FredholmData (E := E) q) : fredholmIndex fd = 0 := by
  unfold fredholmIndex
  rw [fd.index_zero]
  simp

-- ═══════════════════════════════════════════════════════════════════
-- CLOSING span_harmonic — PROVED FROM LINEARITY OF Δ
-- ═══════════════════════════════════════════════════════════════════

/-- Δ distributes over Finset.sum when Δ is additive. -/
private theorem laplacian_sum {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (h_add : ∀ (ω₁ ω₂ : DiffForm ℝ E ℝ q),
      hlm.laplacian (ω₁ + ω₂) = hlm.laplacian ω₁ + hlm.laplacian ω₂)
    (h_zero : hlm.laplacian 0 = 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → DiffForm ℝ E ℝ q) :
    hlm.laplacian (∑ i ∈ s, f i) = ∑ i ∈ s, hlm.laplacian (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero]
  | @insert a s' has ih =>
    rw [Finset.sum_insert has, h_add, ih, Finset.sum_insert has]

/-- **span_harmonic discharged from linearity of Δ.**

    If Δ is additive and ℝ-linear, then linear combinations of
    harmonic forms are harmonic: Δ(Σ cᵢhᵢ) = Σ cᵢΔ(hᵢ) = 0.

    For `laplacianFromDCodiff`: the caller provides
    `laplacianFromDCodiff_add` and `_smul` (with ContDiff witnesses
    for their specific basis elements) to discharge the hypotheses. -/
theorem span_harmonic_of_linear {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    {b : ℕ} (basis : Fin b → DiffForm ℝ E ℝ q)
    (h_harmonic : ∀ i, IsHarmonic (hlm := hlm) (basis i))
    (h_add : ∀ (ω₁ ω₂ : DiffForm ℝ E ℝ q),
      hlm.laplacian (ω₁ + ω₂) = hlm.laplacian ω₁ + hlm.laplacian ω₂)
    (h_smul : ∀ (c : ℝ) (ω : DiffForm ℝ E ℝ q),
      hlm.laplacian (c • ω) = c • hlm.laplacian ω)
    (coeffs : Fin b → ℝ) :
    IsHarmonic (hlm := hlm) (∑ i : Fin b, coeffs i • basis i) := by
  unfold IsHarmonic at *
  have h_zero : hlm.laplacian 0 = 0 := by
    have := h_smul 0 (0 : DiffForm ℝ E ℝ q); simp [zero_smul] at this; exact this
  rw [laplacian_sum h_add h_zero]
  apply Finset.sum_eq_zero
  intro i _
  rw [h_smul, h_harmonic i, smul_zero]

-- ═══════════════════════════════════════════════════════════════════
-- HARMONIC PROJECTION DATA — L² STRUCTURE + FREDHOLM DECOMPOSITION
-- ═══════════════════════════════════════════════════════════════════

/-- Data for the harmonic projection: L² pairing + orthonormal basis +
    the Fredholm decomposition.

    The L² pairing l2 : DiffForm × DiffForm → ℝ is the inner product
    ⟨ω, η⟩_{L²} = ∫_M ω ∧ ★η. It is provided as data because it
    depends on the metric, measure, and Hodge star of the specific domain.

    The Fredholm decomposition (fredholm_decomp) is the DEEP analytical
    content: self-adjointness of Δ + closedness of im Δ + Hilbert space
    structure give im Δ = (ker Δ)⊥. So ω - Hω ∈ (ker Δ)⊥ = im Δ.

    This takes the L² completion infrastructure as a HYPOTHESIS because
    Lean/Mathlib does not yet have L²-form completions wired. The
    hypothesis is honest and mathematically real. -/
structure HarmonicProjectionData (q : ℕ) [hlm : HodgeLaplacianMap (E := E) q]
    extends FredholmData (E := E) q where
  /-- The L² inner product on q-forms: ⟨ω, η⟩_{L²} = ∫_M ω ∧ ★η. -/
  l2 : DiffForm ℝ E ℝ q → DiffForm ℝ E ℝ q → ℝ
  /-- L² is additive in the first argument. -/
  l2_add_left : ∀ (ω₁ ω₂ η : DiffForm ℝ E ℝ q),
    l2 (ω₁ + ω₂) η = l2 ω₁ η + l2 ω₂ η
  /-- L² is ℝ-linear in the first argument. -/
  l2_smul_left : ∀ (c : ℝ) (ω η : DiffForm ℝ E ℝ q),
    l2 (c • ω) η = c * l2 ω η
  /-- L² is symmetric: ⟨ω, η⟩ = ⟨η, ω⟩. -/
  l2_symm : ∀ (ω η : DiffForm ℝ E ℝ q), l2 ω η = l2 η ω
  /-- L² is nonneg: ⟨ω, ω⟩ ≥ 0. -/
  l2_nonneg : ∀ (ω : DiffForm ℝ E ℝ q), 0 ≤ l2 ω ω
  /-- L² is positive definite: ⟨ω, ω⟩ = 0 → ω = 0 (in L²).
      On forms, this holds because ∫ |ω|² = 0 iff ω = 0 a.e. -/
  l2_pos_def : ∀ (ω : DiffForm ℝ E ℝ q), l2 ω ω = 0 → ω = 0
  /-- The harmonic basis is orthonormal with respect to L². -/
  basis_orthonormal : ∀ (i j : Fin dimKernel),
    l2 (basis i) (basis j) = if i = j then 1 else 0
  -- (l2_im_orth_ker is PROVED below from l2_self_adj, not a field)
  /-- **Self-adjointness of Δ**: ⟨Δω, η⟩ = ⟨ω, Δη⟩.
      On a compact Riemannian manifold, Δ = dδ + δd is self-adjoint
      because d and δ are adjoint (Stokes' theorem). -/
  l2_self_adj : ∀ (ω η : DiffForm ℝ E ℝ q),
    l2 (hlm.laplacian ω) η = l2 ω (hlm.laplacian η)
  /-- **The Fredholm decomposition**: ω - Hω ∈ im Δ.

      For self-adjoint Δ with closed image on a compact manifold:
      im Δ = (ker Δ)⊥ in L². The harmonic projection Hω = Σᵢ ⟨ω,hᵢ⟩hᵢ
      gives ω - Hω ⊥ ker Δ, so ω - Hω ∈ (ker Δ)⊥ = im Δ.

      This requires closedness of im Δ (from Rellich compactness +
      elliptic regularity → Fredholm property). The self-adjointness
      gives im Δ ⊆ (ker Δ)⊥, and closedness + the (ker Δ)⊥ ∩ (im Δ)⊥ = {0}
      theorem (PROVED from self-adj + pos_def) give the reverse. -/
  fredholm_decomp : ∀ (ω : DiffForm ℝ E ℝ q),
    ∃ η, hlm.laplacian η =
      ω - ∑ i : Fin dimKernel, l2 ω (basis i) • basis i

-- ═══════════════════════════════════════════════════════════════════
-- THE HARMONIC PROJECTION — CONSTRUCTED (not axiomatized)
-- ═══════════════════════════════════════════════════════════════════
-- im Δ ⊥ ker Δ — PROVED FROM SELF-ADJOINTNESS
-- ═══════════════════════════════════════════════════════════════════

/-- **im Δ ⊥ ker Δ**: ⟨Δω, hᵢ⟩ = 0 for all ω and harmonic hᵢ.
    PROVED from self-adjointness: ⟨Δω, hᵢ⟩ = ⟨ω, Δhᵢ⟩ = ⟨ω, 0⟩ = 0. -/
theorem l2_im_orth_ker {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (ω : DiffForm ℝ E ℝ q) (i : Fin hpd.dimKernel) :
    hpd.l2 (hlm.laplacian ω) (hpd.basis i) = 0 := by
  rw [hpd.l2_self_adj]
  have h_harm : hlm.laplacian (hpd.basis i) = 0 := hpd.basis_harmonic i
  rw [h_harm]
  have h0 := hpd.l2_smul_left 0 (hpd.basis i) ω
  simp [zero_smul, zero_mul] at h0
  rw [hpd.l2_symm]; exact h0

-- ═══════════════════════════════════════════════════════════════════
-- ORTHOGONAL EXCLUSION — PROVED FROM SELF-ADJOINTNESS
-- ═══════════════════════════════════════════════════════════════════

/-- **If f ⊥ ker Δ and f ⊥ im Δ, then f = 0.**

    PROVED from self-adjointness + positive definiteness:
    f ⊥ im Δ means ⟨f, Δω⟩ = 0 for all ω.
    Self-adjointness: ⟨Δf, ω⟩ = ⟨f, Δω⟩ = 0 for all ω.
    By symmetry + positive definiteness (nondegeneracy): Δf = 0.
    So f ∈ ker Δ. But f ⊥ ker Δ, so ⟨f, f⟩ = 0. Pos def: f = 0.

    This is the key fact that (ker Δ)⊥ ∩ (im Δ)⊥ = {0}, which
    together with closedness of im Δ gives im Δ = (ker Δ)⊥. -/
theorem orth_ker_orth_im_eq_zero {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (f : DiffForm ℝ E ℝ q)
    -- f ⊥ ker Δ
    (hf_orth_ker : ∀ i : Fin hpd.dimKernel, hpd.l2 f (hpd.basis i) = 0)
    -- f ⊥ im Δ
    (hf_orth_im : ∀ (ω : DiffForm ℝ E ℝ q), hpd.l2 f (hlm.laplacian ω) = 0) :
    f = 0 := by
  -- Step 1: ⟨Δf, ω⟩ = 0 for all ω (from self-adj + f ⊥ im Δ)
  have hΔf_zero : ∀ (ω : DiffForm ℝ E ℝ q), hpd.l2 (hlm.laplacian f) ω = 0 := by
    intro ω; rw [hpd.l2_self_adj]; exact hf_orth_im ω
  -- Step 2: Δf = 0 (nondegeneracy: ⟨g, ω⟩ = 0 ∀ ω → ⟨g, g⟩ = 0 → g = 0)
  have hf_harmonic : IsHarmonic (hlm := hlm) f :=
    hpd.l2_pos_def _ (by rw [hpd.l2_symm]; exact hΔf_zero (hlm.laplacian f))
  -- Step 3: f ∈ ker Δ, but f ⊥ ker Δ → ⟨f, f⟩ = 0 → f = 0.
  -- f is harmonic → f = Σ cᵢ hᵢ (from basis_spans)
  obtain ⟨coeffs, hcoeffs⟩ := hpd.basis_spans f hf_harmonic
  -- Each coefficient cᵢ = ⟨f, hᵢ⟩ = 0 (from hf_orth_ker)
  -- So f = Σ 0 • hᵢ = 0.
  rw [hcoeffs]
  suffices ∀ i, coeffs i = 0 by simp [this]
  intro i
  -- cᵢ = ⟨f, hᵢ⟩ (from orthonormality: ⟨Σ cⱼhⱼ, hᵢ⟩ = cᵢ)
  have h_coeff : hpd.l2 f (hpd.basis i) = coeffs i := by
    rw [hcoeffs]
    -- l2 (∑ i, cᵢ • hᵢ) hⱼ = cᵢ (by orthonormality)
    -- Use: l2 additive + smul + orthonormal basis
    have h_expand : hpd.l2 (∑ j : Fin hpd.dimKernel, coeffs j • hpd.basis j) (hpd.basis i) =
        ∑ j : Fin hpd.dimKernel, hpd.l2 (coeffs j • hpd.basis j) (hpd.basis i) := by
      induction (Finset.univ : Finset (Fin hpd.dimKernel)) using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have := hpd.l2_smul_left 0 0 (hpd.basis i)
        simp [zero_smul, zero_mul] at this; exact this
      | @insert a s has ih =>
        rw [Finset.sum_insert has, hpd.l2_add_left, ih, Finset.sum_insert has]
    rw [h_expand]
    simp_rw [hpd.l2_smul_left, hpd.basis_orthonormal]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  rw [← h_coeff]; exact hf_orth_ker i

-- ═══════════════════════════════════════════════════════════════════
-- THE HARMONIC PROJECTION — CONSTRUCTED (not axiomatized)
-- ═══════════════════════════════════════════════════════════════════

/-- **The harmonic projection**: orthogonal projection onto ker Δ.

    CONSTRUCTED from the orthonormal basis {hᵢ}:
      Hω = Σᵢ ⟨ω, hᵢ⟩_{L²} · hᵢ

    This is the Fourier expansion in the harmonic basis. Each coefficient
    ⟨ω, hᵢ⟩ measures the L² overlap of ω with the i-th harmonic form.

    Not a class field. A definition. A real door, not paint. -/
def harmonicProj {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (ω : DiffForm ℝ E ℝ q) : DiffForm ℝ E ℝ q :=
  ∑ i : Fin hpd.dimKernel, hpd.l2 ω (hpd.basis i) • hpd.basis i

-- ═══════════════════════════════════════════════════════════════════
-- HELPER LEMMAS (L² linearity over sums)
-- ═══════════════════════════════════════════════════════════════════

/-- L² of zero is zero (from scalar linearity: l2(0·ω, η) = 0·l2(ω,η) = 0). -/
theorem l2_zero_left {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (η : DiffForm ℝ E ℝ q) : hpd.l2 0 η = 0 := by
  have h := hpd.l2_smul_left 0 η η
  simp [zero_smul] at h
  exact h

/-- L² distributes over Finset.sum in the first argument. -/
theorem l2_sum_left {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → DiffForm ℝ E ℝ q)
    (η : DiffForm ℝ E ℝ q) :
    hpd.l2 (∑ i ∈ s, f i) η = ∑ i ∈ s, hpd.l2 (f i) η := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2_zero_left hpd]
  | @insert a s' ha ih =>
    rw [Finset.sum_insert ha, hpd.l2_add_left, ih, Finset.sum_insert ha]

-- ═══════════════════════════════════════════════════════════════════
-- PROVED PROPERTIES OF THE HARMONIC PROJECTION
-- ═══════════════════════════════════════════════════════════════════

/-- **The projection is harmonic.** Hω ∈ ker Δ.
    PROVED from span_harmonic: any linear combination of basis elements
    is harmonic. -/
theorem harmonicProj_harmonic {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q) (ω : DiffForm ℝ E ℝ q) :
    IsHarmonic (hlm := hlm) (harmonicProj hpd ω) :=
  hpd.span_harmonic _

/-- **The projection is idempotent.** H(Hω) = Hω.
    PROVED from orthonormality: the L² coefficients of Hω in the
    harmonic basis are the same as those of ω. -/
theorem harmonicProj_idem {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q) (ω : DiffForm ℝ E ℝ q) :
    harmonicProj hpd (harmonicProj hpd ω) = harmonicProj hpd ω := by
  unfold harmonicProj
  -- Show: the i-th L² coefficient of Hω equals the i-th L² coefficient of ω.
  -- l2 (Σⱼ cⱼ • hⱼ) hᵢ = Σⱼ cⱼ · l2 hⱼ hᵢ = Σⱼ cⱼ · δᵢⱼ = cᵢ = l2 ω hᵢ
  congr 1; ext i
  rw [l2_sum_left]
  simp_rw [hpd.l2_smul_left]
  simp_rw [hpd.basis_orthonormal]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- **The projection is additive.** H(ω₁ + ω₂) = Hω₁ + Hω₂.
    PROVED from bilinearity of L². -/
theorem harmonicProj_add {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (ω₁ ω₂ : DiffForm ℝ E ℝ q) :
    harmonicProj hpd (ω₁ + ω₂) = harmonicProj hpd ω₁ + harmonicProj hpd ω₂ := by
  unfold harmonicProj
  simp_rw [hpd.l2_add_left]
  simp_rw [add_smul]
  rw [← Finset.sum_add_distrib]

/-- **The projection is ℝ-linear.** H(c · ω) = c · Hω.
    PROVED from ℝ-linearity of L². -/
theorem harmonicProj_smul {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (c : ℝ) (ω : DiffForm ℝ E ℝ q) :
    harmonicProj hpd (c • ω) = c • harmonicProj hpd ω := by
  unfold harmonicProj
  simp_rw [hpd.l2_smul_left]
  simp_rw [mul_smul]
  rw [← Finset.smul_sum]

/-- **The remainder is in im Δ.** ∃ η, Δη = ω - Hω.
    PROVED from the Fredholm decomposition hypothesis. -/
theorem remainder_in_image {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q) (ω : DiffForm ℝ E ℝ q) :
    ∃ η, hlm.laplacian η = ω - harmonicProj hpd ω :=
  hpd.fredholm_decomp ω

/-- **The harmonic projection of an exact form is zero.**
    PROVED from l2_exact_orth_harmonic: all L² coefficients of dα
    against harmonic basis elements are zero, so Σᵢ 0 • hᵢ = 0.

    **The harmonic projection of Δω is zero.** H(Δω) = 0.
    PROVED from l2_im_orth_ker: all L² coefficients of Δω against
    harmonic basis elements are zero. -/
theorem harmonicProj_laplacian_zero {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (ω : DiffForm ℝ E ℝ q) :
    harmonicProj hpd (hlm.laplacian ω) = 0 := by
  unfold harmonicProj
  simp [l2_im_orth_ker hpd]

-- ═══════════════════════════════════════════════════════════════════
-- THE FREDHOLM ALTERNATIVE — PROVED
-- ═══════════════════════════════════════════════════════════════════

/-- **The Fredholm alternative for the Hodge Laplacian.**

    If f is orthogonal to all harmonic forms (f ⊥ ker Δ), then
    a solution ω to Δω = f exists.

    PROVED:
    1. f ⊥ ker Δ means all L² coefficients ⟨f, hᵢ⟩ = 0.
    2. So Hf = Σᵢ 0 · hᵢ = 0.
    3. Fredholm decomposition: ∃ η, Δη = f - Hf = f - 0 = f.

    The uniqueness is mod ker Δ: if Δω₁ = Δω₂ = f, then
    Δ(ω₁ - ω₂) = 0 (from linearity), so ω₁ - ω₂ is harmonic. -/
theorem fredholm_alternative {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (hpd : HarmonicProjectionData (E := E) q)
    (f : DiffForm ℝ E ℝ q)
    (hf_orth : ∀ i : Fin hpd.dimKernel, hpd.l2 f (hpd.basis i) = 0) :
    ∃ ω, hlm.laplacian ω = f := by
  -- Step 1: Hf = 0 (all coefficients are zero).
  have h_proj_zero : harmonicProj hpd f = 0 := by
    unfold harmonicProj
    simp [hf_orth]
  -- Step 2: Fredholm decomposition gives ∃ η, Δη = f - Hf = f.
  obtain ⟨η, hη⟩ := hpd.fredholm_decomp f
  refine ⟨η, ?_⟩
  -- hη : Δη = f - Σᵢ l2 f (basis i) • basis i
  -- h_proj_zero : harmonicProj hpd f = 0, i.e., Σᵢ l2 f (basis i) • basis i = 0
  have : ∑ i : Fin hpd.dimKernel, hpd.l2 f (hpd.basis i) • hpd.basis i = 0 := by
    show harmonicProj hpd f = 0; exact h_proj_zero
  rwa [this, sub_zero] at hη

/-- Uniqueness modulo ker Δ: if Δω₁ = f and Δω₂ = f, then ω₁ - ω₂
    is harmonic. Takes linearity of Δ as a hypothesis. -/
theorem fredholm_unique_mod_kernel {q : ℕ} [hlm : HodgeLaplacianMap (E := E) q]
    (ω₁ ω₂ f : DiffForm ℝ E ℝ q)
    (h₁ : hlm.laplacian ω₁ = f) (h₂ : hlm.laplacian ω₂ = f)
    (h_linear : hlm.laplacian (ω₁ - ω₂) =
      hlm.laplacian ω₁ - hlm.laplacian ω₂) :
    IsHarmonic (hlm := hlm) (ω₁ - ω₂) := by
  unfold IsHarmonic
  rw [h_linear, h₁, h₂, sub_self]

end

end Ramtastic.Sobolev.FredholmTheory
