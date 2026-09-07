/-
  DelDelBar.lean — The ∂ and ∂̄ operators.

  On a space with an almost complex structure J:
  - d = ∂ + ∂̄ (the exterior derivative splits)
  - ∂f = π^{1,0}(df) — the (1,0)-component of df
  - ∂̄f = π^{0,1}(df) — the (0,1)-component of df

  Key identities: ∂² = 0, ∂̄² = 0, ∂∂̄ + ∂̄∂ = 0
  (from d² = 0 + pullbackJ commuting with d on flat spaces).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ComplexStructure.TypeDecomposition

namespace Ramtastic.ComplexStructure.DelDelBar

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.ComplexStructure.AlmostComplex
open Ramtastic.ComplexStructure.TypeDecomposition

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [acs : AlmostComplexStr E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- ═══════════════════════════════════════════════════════════════════
-- ∂ AND ∂̄ ON FUNCTIONS
-- ═══════════════════════════════════════════════════════════════════

/-- ∂f: the (1,0)-component of df. -/
def del (f : DiffForm ℝ E F 0) : ComplexForm E F 1 :=
  proj10 (ComplexForm.ofReal (fun x => extDeriv f x))

/-- ∂̄f: the (0,1)-component of df. -/
def delbar (f : DiffForm ℝ E F 0) : ComplexForm E F 1 :=
  proj01 (ComplexForm.ofReal (fun x => extDeriv f x))

-- ═══════════════════════════════════════════════════════════════════
-- d = ∂ + ∂̄
-- ═══════════════════════════════════════════════════════════════════

/-- d = ∂ + ∂̄ (real part): Re(∂f) + Re(∂̄f) = df. -/
theorem del_add_delbar_re (f : DiffForm ℝ E F 0) (x : E) (m : Fin 1 → E) :
    (del f).re x m + (delbar f).re x m = extDeriv f x m :=
  proj10_add_proj01_re (ComplexForm.ofReal (fun x => extDeriv f x)) x m

/-- d = ∂ + ∂̄ (imaginary part): Im(∂f) + Im(∂̄f) = 0. -/
theorem del_add_delbar_im (f : DiffForm ℝ E F 0) (x : E) (m : Fin 1 → E) :
    (del f).im x m + (delbar f).im x m = 0 := by
  have := proj10_add_proj01_im (ComplexForm.ofReal (fun x => extDeriv f x)) x m
  simpa [ComplexForm.ofReal] using this

-- ═══════════════════════════════════════════════════════════════════
-- J*-EIGENVALUE PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

theorem del_eigenvalue_re (f : DiffForm ℝ E F 0) (x : E) (m : Fin 1 → E) :
    pullbackJ (del f).re x m = -((del f).im x m) :=
  pullbackJ_proj10_re _ x m

theorem del_eigenvalue_im (f : DiffForm ℝ E F 0) (x : E) (m : Fin 1 → E) :
    pullbackJ (del f).im x m = (del f).re x m :=
  pullbackJ_proj10_im _ x m

theorem delbar_eigenvalue_re (f : DiffForm ℝ E F 0) (x : E) (m : Fin 1 → E) :
    pullbackJ (delbar f).re x m = (delbar f).im x m :=
  pullbackJ_proj01_re _ x m

theorem delbar_eigenvalue_im (f : DiffForm ℝ E F 0) (x : E) (m : Fin 1 → E) :
    pullbackJ (delbar f).im x m = -((delbar f).re x m) :=
  pullbackJ_proj01_im _ x m

-- ═══════════════════════════════════════════════════════════════════
-- ∂̄² = 0 AND ∂² = 0 ON FLAT SPACES
-- ═══════════════════════════════════════════════════════════════════

-- The real parts of ∂f and ∂̄f are both (1/2)•df.
-- So d(Re(∂f)) = d(Re(∂̄f)) = (1/2)•d²f = 0 by d²=0.
-- The imaginary parts are ±(1/2)•J*df.
-- d(J*df) = J*(d²f) = 0 on flat spaces (J constant → commutes with d).
-- The commutativity is stated as a hypothesis for the imaginary parts.

/-- ∂̄² = 0 (real part): d(Re(∂̄f)) = 0. From d²f = 0.
    Re(∂̄f) = (1/2)df, so d(Re(∂̄f)) = (1/2)d²f = 0. -/
theorem delbar_sq_re {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r) (x : E) :
    extDeriv (delbar f).re x = 0 := by
  -- ∂̄f.re = (1/2) • (df + 0) = (1/2) • df
  have h_form : (delbar f).re = (1/2 : ℝ) • (fun x => extDeriv f x) := by
    ext y m; simp [delbar, proj01, ComplexForm.ofReal, pullbackJ_zero]
  rw [h_form, extDeriv_smul]
  have := congr_fun (extDeriv_extDeriv hf hr) x
  simp [this]

/-- ∂² = 0 (real part): d(Re(∂f)) = 0. From d²f = 0. -/
theorem del_sq_re {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r) (x : E) :
    extDeriv (del f).re x = 0 := by
  have h_form : (del f).re = (1/2 : ℝ) • (fun x => extDeriv f x) := by
    ext y m; simp [del, proj10, ComplexForm.ofReal, pullbackJ_zero]
  rw [h_form, extDeriv_smul]
  have := congr_fun (extDeriv_extDeriv hf hr) x
  simp [this]

/-- **d(J*df) is of type (1,1)**: the hypothesis version.
    The hypothesis h_type11 states the J*-invariance pointwise.
    On flat spaces, this follows from: J² = -id + symmetry of fderiv²f.
    The algebraic proof (verified by hand):
    Let B(u,w) = fderiv²f(u)(w), symmetric. Then
    d(J*df)(Jv₀,Jv₁) = B(Jv₀,-v₁) - B(Jv₁,-v₀) = B(v₀,Jv₁) - B(v₁,Jv₀)
    = d(J*df)(v₀,v₁). -/
theorem dJdf_type11 (f : DiffForm ℝ E F 0)
    (h_type11 : ∀ y (m : Fin 2 → E),
      extDeriv (pullbackJ (fun x => extDeriv f x)) y (acs.J ∘ m) =
      extDeriv (pullbackJ (fun x => extDeriv f x)) y m) :
    IsType11 (fun x => extDeriv (pullbackJ (fun x => extDeriv f x)) x) := by
  ext y m; exact h_type11 y m

/-- ∂̄² = 0 (correct form): the (2,0)+(0,2)-projection of d(Im(∂̄f)) vanishes.
    Im(∂̄f) = (1/2)J*df. The 2-form d(J*df) is type (1,1), so its
    (2,0)+(0,2) projection is zero. This IS ∂̄²f = 0. -/
theorem delbar_sq_proj (f : DiffForm ℝ E F 0) (x : E) (m : Fin 2 → E)
    (h_type11 : ∀ y (m : Fin 2 → E),
      extDeriv (pullbackJ (fun x => extDeriv f x)) y (acs.J ∘ m) =
      extDeriv (pullbackJ (fun x => extDeriv f x)) y m) :
    proj20_02 (fun x => extDeriv (delbar f).im x) x m = 0 := by
  have h_form : (delbar f).im = (1/2 : ℝ) • pullbackJ (fun x => extDeriv f x) := by
    ext y v; simp [delbar, proj01, ComplexForm.ofReal, pullbackJ_zero]
  simp only [h_form, proj20_02, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply, pullbackJ_apply,
    extDeriv_smul, pullbackJ_smul]
  rw [h_type11 x m]
  module

/-- ∂² = 0 (correct form): the (2,0)+(0,2)-projection of d(Im(∂f)) vanishes.
    Im(∂f) = -(1/2)J*df. Negation preserves type (1,1). -/
theorem del_sq_proj (f : DiffForm ℝ E F 0) (x : E) (m : Fin 2 → E)
    (h_type11 : ∀ y (m : Fin 2 → E),
      extDeriv (pullbackJ (fun x => extDeriv f x)) y (acs.J ∘ m) =
      extDeriv (pullbackJ (fun x => extDeriv f x)) y m) :
    proj20_02 (fun x => extDeriv (del f).im x) x m = 0 := by
  have h_form : (del f).im = (-1/2 : ℝ) • pullbackJ (fun x => extDeriv f x) := by
    ext y v; simp [del, proj10, ComplexForm.ofReal, pullbackJ_zero]; module
  simp only [h_form, proj20_02, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply, pullbackJ_apply,
    extDeriv_smul, pullbackJ_smul]
  rw [h_type11 x m]
  module

/-- **d(J*df) is type (1,1) on flat spaces — PROVED.**
    The symmetry hypothesis h_sym is B(u,w) = B(w,u) where
    B(u,w) = fderiv(fun z => extDeriv f z ![w]) y u.

    This IS d²f = 0 expanded at the Fin 2 level:
    extDeriv(extDeriv f) y ![u,w] = B(u,w) - B(w,u) = 0 → B(u,w) = B(w,u).

    From h_sym: LHS = -B(J(m0), m1) + B(J(m1), m0)
             = -B(m1, J(m0)) + B(m0, J(m1))  [symmetry]
             = B(m0, J(m1)) - B(m1, J(m0)) = RHS. -/
theorem h_type11_proved (f : DiffForm ℝ E F 0)
    (hdf : ∀ y, DifferentiableAt ℝ (pullbackJ (fun x => extDeriv f x)) y)
    (h_sym : ∀ y u w,
      fderiv ℝ (fun z => (extDeriv f z) ![w]) y u =
      fderiv ℝ (fun z => (extDeriv f z) ![u]) y w) :
    ∀ y (m : Fin 2 → E),
      extDeriv (pullbackJ (fun x => extDeriv f x)) y (acs.J ∘ m) =
      extDeriv (pullbackJ (fun x => extDeriv f x)) y m := by
  intro y m
  conv_lhs => rw [extDeriv_apply (hdf y)]
  conv_rhs => rw [extDeriv_apply (hdf y)]
  -- Both sides are ∑ i, (-1)^i • fderiv(pullbackJ df · removeNth ...) y (arg i)
  -- Expand pullbackJ and simplify removeNth(J∘m) = J∘removeNth(m), J²=-id
  simp only [Function.comp, pullbackJ_apply]
  -- Now need to show the sum equality.
  -- Key facts about removeNth for Fin 2:
  -- removeNth 0 (J ∘ m) = J ∘ removeNth 0 m, etc.
  -- And J ∘ J ∘ v = fun j => -(v j), so extDeriv f z evaluates with negation
  -- For degree-1: negation of the argument negates the value
  -- Let's compute both sides by converting sums to explicit Fin 2 terms
  -- and applying the symmetry hypothesis
  -- The sum over Fin 2 with removeNth gives specific evaluations
  -- After all simplification, use h_sym to swap and add_comm to finish
  -- Use Finset.sum for Fin 2: explicit evaluation
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  -- Now: term0_L + term1_L = term0_R + term1_R
  -- After simp, the J∘removeNth and J² reductions should leave
  -- terms that match crosswise via h_sym
  -- Goal should now be explicit Fin 2 terms.
  -- Let me try simp with all the relevant lemmas:
  -- After Fin.sum_univ_two + Function.comp + pullbackJ_apply:
  -- Goal is a sum with opaque fderiv terms.
  -- Strategy: rewrite the functions INSIDE fderiv using congrArg,
  -- then use h_sym to swap, then abel to close.
  -- Key helper: J∘removeNth(J∘m) = J∘J∘removeNth(m) = -(removeNth m)
  -- J∘(J∘m)∘succAbove = (fun i => J(J(m(succAbove i)))) = (fun i => -(m(succAbove i)))
  -- This equals (fun i => (-1 : ℝ) • (m ∘ succAbove) i)
  -- So extDeriv f z evaluated at this = -(extDeriv f z (m ∘ succAbove))
  have hrem0 : (fun z => (extDeriv f z) (acs.J ∘ Fin.removeNth 0 (acs.J ∘ m))) =
    (fun z => -((extDeriv f z) (m ∘ Fin.succAbove 0))) := by
    ext z
    have : acs.J ∘ Fin.removeNth 0 (acs.J ∘ m) =
      (fun i => (-1 : ℝ) • ((m ∘ Fin.succAbove 0) i)) := by
      ext i; simp [Fin.removeNth, Function.comp, J_apply_sq]
    rw [this, (extDeriv f z).map_smul_univ]; simp [Finset.prod_const, Finset.card_fin]
  have hrem1 : (fun z => (extDeriv f z) (acs.J ∘ Fin.removeNth 1 (acs.J ∘ m))) =
    (fun z => -((extDeriv f z) (m ∘ Fin.succAbove 1))) := by
    ext z
    have : acs.J ∘ Fin.removeNth 1 (acs.J ∘ m) =
      (fun i => (-1 : ℝ) • ((m ∘ Fin.succAbove 1) i)) := by
      ext i; simp [Fin.removeNth, Function.comp, J_apply_sq]
    rw [this, (extDeriv f z).map_smul_univ]; simp [Finset.prod_const, Finset.card_fin]
  rw [hrem0, hrem1]
  -- Now fderiv of negated functions. Use show to normalize the negation:
  rw [show (fun z => -((extDeriv f z) (m ∘ Fin.succAbove 0))) =
    (-(fun z => (extDeriv f z) (m ∘ Fin.succAbove 0))) from by ext; simp]
  rw [show (fun z => -((extDeriv f z) (m ∘ Fin.succAbove 1))) =
    (-(fun z => (extDeriv f z) (m ∘ Fin.succAbove 1))) from by ext; simp]
  simp only [fderiv_neg, ContinuousLinearMap.neg_apply, neg_neg, neg_smul]
  -- Now LHS: B(J(m 0), m∘succAbove 0) + (-1)•(-B(J(m 1), m∘succAbove 1))
  --        = B(J(m 0), ![m 1]) + B(J(m 1), ![m 0])  [after neg_neg + succAbove eval]
  -- RHS: B(m 0, J∘m∘succAbove 0) + (-1)•B(m 1, J∘m∘succAbove 1)
  --     = B(m 0, ![J(m 1)]) - B(m 1, ![J(m 0)])
  -- h_sym: B(J(m 0), ![m 1]) = B(m 1, ![J(m 0)])
  --        B(J(m 1), ![m 0]) = B(m 0, ![J(m 1)])
  -- Normalize succAbove to concrete ![...]:
  -- Normalize removeNth to concrete ![...] using Fin.removeNth = m ∘ succAbove
  simp only [show m ∘ Fin.succAbove 0 = Fin.removeNth 0 m from by ext i; simp [Fin.removeNth]]
  simp only [show m ∘ Fin.succAbove 1 = Fin.removeNth 1 m from by ext i; simp [Fin.removeNth]]
  -- Now convert removeNth and J∘removeNth to concrete vectors
  conv_lhs =>
    rw [show Fin.removeNth (0 : Fin 2) m = ![m 1] from by ext i; fin_cases i; simp [Fin.removeNth, Fin.succAbove]]
    rw [show Fin.removeNth (1 : Fin 2) m = ![m 0] from by ext i; fin_cases i; simp [Fin.removeNth, Fin.succAbove]]
  conv_rhs =>
    rw [show acs.J ∘ Fin.removeNth (0 : Fin 2) m = ![acs.J (m 1)] from by ext i; fin_cases i; simp [Fin.removeNth, Fin.succAbove, Fin.tail]]
    rw [show acs.J ∘ Fin.removeNth (1 : Fin 2) m = ![acs.J (m 0)] from by ext i; fin_cases i; simp [Fin.removeNth, Fin.succAbove, Fin.tail]]
  rw [h_sym y (acs.J (m 0)) (m 1), h_sym y (acs.J (m 1)) (m 0)]
  simp only [neg_one_smul, one_smul, neg_smul, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, neg_neg]
  abel

/-- **h_sym from d²f = 0 — PROVED.**
    The symmetry B(u,w) = B(w,u) follows from extDeriv(extDeriv f) = 0.
    Expanding d²f via extDeriv_apply at ![u,w] gives B(u,w) - B(w,u) = 0. -/
theorem h_sym_from_d2 {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r)
    (hdf_diff : ∀ y, DifferentiableAt ℝ (fun x => extDeriv f x) y) :
    ∀ y u w,
      fderiv ℝ (fun z => (extDeriv f z) ![w]) y u =
      fderiv ℝ (fun z => (extDeriv f z) ![u]) y w := by
  intro y u w
  -- d²f = 0 at y: extDeriv(extDeriv f) y = 0
  have hd2 := congr_fun (extDeriv_extDeriv hf hr) y
  -- Expand d²f at ![u, w] using extDeriv_apply:
  have hd2_eval : extDeriv (fun x => extDeriv f x) y ![u, w] = 0 := by
    rw [hd2]; simp
  rw [extDeriv_apply (hdf_diff y)] at hd2_eval
  -- After extDeriv_apply: ∑ i : Fin 2, (-1)^i • fderiv(...) y (![u,w] i) = 0
  -- hd2_eval has the extDeriv_apply expansion as a sum.
  -- Convert removeNth to concrete form and extract the symmetry.
  -- removeNth 0 ![u,w] = ![w] and removeNth 1 ![u,w] = ![u]
  -- After expansion: B(u,w) + (-1)^1 • B(w,u) = 0 → B(u,w) = B(w,u)
  have hrn0 : Fin.removeNth (0 : Fin 2) ![u, w] = ![w] := by
    ext i; fin_cases i; simp [Fin.removeNth, Fin.succAbove, Fin.tail]
  have hrn1 : Fin.removeNth (1 : Fin 2) ![u, w] = ![u] := by
    ext i; fin_cases i; simp [Fin.removeNth, Fin.succAbove]
  -- Expand the sum to two explicit terms:
  rw [Fin.sum_univ_two] at hd2_eval
  -- Now substitute the concrete removeNth values:
  rw [hrn0, hrn1] at hd2_eval
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hd2_eval
  -- hd2_eval: B(u,w) + (-1)•B(w,u) = 0, i.e., B(u,w) - B(w,u) = 0 → B(u,w) = B(w,u)
  simp only [neg_one_smul] at hd2_eval
  -- hd2_eval : B(u,w) + (-B(w,u)) = 0, i.e., B(u,w) - B(w,u) = 0
  rwa [add_neg_eq_zero] at hd2_eval

/-- **The complete h_type11 on flat spaces — PROVED from d²f = 0.**
    Combines h_type11_proved with h_sym_from_d2. -/
theorem h_type11_complete {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r)
    (hdf : ∀ y, DifferentiableAt ℝ (pullbackJ (fun x => extDeriv f x)) y)
    (hdf_diff : ∀ y, DifferentiableAt ℝ (fun x => extDeriv f x) y) :
    ∀ y (m : Fin 2 → E),
      extDeriv (pullbackJ (fun x => extDeriv f x)) y (acs.J ∘ m) =
      extDeriv (pullbackJ (fun x => extDeriv f x)) y m :=
  h_type11_proved f hdf (h_sym_from_d2 f hf hr hdf_diff)

/-- **∂∂̄ + ∂̄∂ = 0 (imaginary cross-terms).**
    Im(∂f) = -(1/2)J*df and Im(∂̄f) = (1/2)J*df.
    So d(Im(∂f)) + d(Im(∂̄f)) = d(-(1/2)J*df + (1/2)J*df) = d(0) = 0.
    This is the (1,1)-component of d²f = 0. -/
theorem del_delbar_cross_im {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r) (x : E) :
    extDeriv (del f).im x + extDeriv (delbar f).im x = 0 := by
  have h_del : (del f).im = (-1/2 : ℝ) • pullbackJ (fun x => extDeriv f x) := by
    ext y v; simp [del, proj10, ComplexForm.ofReal, pullbackJ_zero]; module
  have h_delbar : (delbar f).im = (1/2 : ℝ) • pullbackJ (fun x => extDeriv f x) := by
    ext y v; simp [delbar, proj01, ComplexForm.ofReal, pullbackJ_zero]
  rw [h_del, h_delbar, extDeriv_smul, extDeriv_smul]
  simp; module

/-- **∂∂̄ + ∂̄∂ = 0 (real cross-terms).**
    Re(∂f) = Re(∂̄f) = (1/2)df. So d(Re(∂f)) = d(Re(∂̄f)) = 0 (from d²=0).
    Both are zero individually, so their sum is zero. -/
theorem del_delbar_cross_re {r : WithTop ℕ∞} (f : DiffForm ℝ E F 0)
    (hf : ContDiff ℝ r f) (hr : minSmoothness ℝ 2 ≤ r) (x : E) :
    extDeriv (del f).re x + extDeriv (delbar f).re x = 0 := by
  rw [del_sq_re f hf hr x, delbar_sq_re f hf hr x, add_zero]

end

end Ramtastic.ComplexStructure.DelDelBar
