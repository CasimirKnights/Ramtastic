/-
  TypeDecomposition.lean — The (p,q)-type decomposition of forms under J.

  An almost complex structure J on E induces a pullback J* on k-forms:
    (J*ω)(v₁,...,vₖ) = ω(Jv₁,...,Jvₖ)

  Key property: (J*)² = (-1)ᵏ · id on k-forms.
  - For k=1: J* is itself an almost complex structure on 1-forms
  - For k=2: J* is an involution, splitting 2-forms into ±1 eigenspaces
    - The +1 eigenspace = type (1,1) forms (includes the Kähler form)
    - The -1 eigenspace = type (2,0)+(0,2) forms

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.ComplexStructure.AlmostComplex

namespace Ramtastic.ComplexStructure.TypeDecomposition

open Ramtastic.DeRham.DifferentialForms
open Ramtastic.ComplexStructure.AlmostComplex

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [acs : AlmostComplexStr E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- THE PULLBACK J* ON FORMS
-- ═══════════════════════════════════════════════════════════════════

/-- The pullback of J on k-forms.
    (J*ω)(x)(v₁,...,vₖ) = ω(x)(Jv₁,...,Jvₖ). -/
def pullbackJ (ω : DiffForm ℝ E F n) : DiffForm ℝ E F n :=
  fun x => (ω x).compContinuousLinearMap acs.J

/-- Evaluation of pullbackJ: (J*ω)(x)(m) = ω(x)(J∘m). -/
theorem pullbackJ_apply (ω : DiffForm ℝ E F n) (x : E) (m : Fin n → E) :
    pullbackJ ω x m = ω x (acs.J ∘ m) := by
  simp [pullbackJ]

-- ═══════════════════════════════════════════════════════════════════
-- PULLBACK J* LINEARITY
-- ═══════════════════════════════════════════════════════════════════

/-- J* is additive. -/
theorem pullbackJ_add (ω₁ ω₂ : DiffForm ℝ E F n) :
    pullbackJ (ω₁ + ω₂) = pullbackJ ω₁ + pullbackJ ω₂ := by
  ext x m; simp [pullbackJ]

/-- J* respects scalar multiplication. -/
theorem pullbackJ_smul (c : ℝ) (ω : DiffForm ℝ E F n) :
    pullbackJ (c • ω) = c • pullbackJ ω := by
  ext x m; simp [pullbackJ]

/-- J* sends zero to zero. -/
theorem pullbackJ_zero : pullbackJ (0 : DiffForm ℝ E F n) = 0 := by
  ext x m; simp [pullbackJ]

/-- J* respects negation. -/
theorem pullbackJ_neg (ω : DiffForm ℝ E F n) :
    pullbackJ (-ω) = -pullbackJ ω := by
  ext x m; simp [pullbackJ]

-- ═══════════════════════════════════════════════════════════════════
-- THE COMPOSITION (J*)² = (-1)ⁿ
-- ═══════════════════════════════════════════════════════════════════

/-- Double pullback: (J*)(J*ω)(x)(m) = ω(x)(fun i => -(m i)). -/
theorem pullbackJ_pullbackJ_apply (ω : DiffForm ℝ E F n) (x : E) (m : Fin n → E) :
    pullbackJ (pullbackJ ω) x m = ω x (fun i => -(m i)) := by
  simp only [pullbackJ_apply]
  congr 1; ext i; exact J_apply_sq (m i)

/-- THE KEY THEOREM: (J*)² = (-1)��� · id on k-forms.
    Uses map_smul_univ: scaling all n arguments by -1 gives (-1)ⁿ. -/
theorem pullbackJ_sq (ω : DiffForm ℝ E F n) (x : E) (m : Fin n → E) :
    pullbackJ (pullbackJ ω) x m = ((-1 : ℝ) ^ n) • ω x m := by
  rw [pullbackJ_pullbackJ_apply]
  conv_lhs => rw [show (fun i => -(m i)) = (fun i => (-1 : ℝ) • m i) from by ext; simp]
  rw [(ω x).map_smul_univ]
  congr 1
  simp [Finset.prod_const, Finset.card_fin]

-- ════════════════════════════════════════════════════════════��══════
-- SPECIFIC DEGREES
-- ═══════════════════════════════════════════════════════════════════

/-- For 1-forms: (J*)² = -id. The pullback is another almost complex structure. -/
theorem pullbackJ_sq_one (ω : DiffForm ℝ E F 1) (x : E) (m : Fin 1 → E) :
    pullbackJ (pullbackJ ω) x m = -(ω x m) := by
  rw [pullbackJ_sq]; norm_num

/-- For 2-forms: (J*)² = id. The pullback is an involution. -/
theorem pullbackJ_sq_two (ω : DiffForm ℝ E F 2) (x : E) (m : Fin 2 → E) :
    pullbackJ (pullbackJ ω) x m = ω x m := by
  rw [pullbackJ_sq]; norm_num

/-- For 3-forms: (J*)² = -id again. -/
theorem pullbackJ_sq_three (ω : DiffForm ℝ E F 3) (x : E) (m : Fin 3 → E) :
    pullbackJ (pullbackJ ω) x m = -(ω x m) := by
  rw [pullbackJ_sq]; norm_num

-- ═══════════════════════════════════════════════════════════════════
-- TYPE DECOMPOSITION FOR 2-FORMS
-- ═══════════════════════════════════════════════════════════════════

/-- A 2-form is of type (1,1) if J*ω = ω (J*-invariant). -/
def IsType11 (ω : DiffForm ℝ E F 2) : Prop :=
  pullbackJ ω = ω

/-- A 2-form is of type (2,0)+(0,2) if J*ω = -ω (J*-anti-invariant). -/
def IsType20_02 (ω : DiffForm ℝ E F 2) : Prop :=
  pullbackJ ω = -ω

/-- The (1,1)-projection: π₊(ω) = (1/2)(ω + J*ω). -/
def proj11 (ω : DiffForm ℝ E F 2) : DiffForm ℝ E F 2 :=
  fun x => (1/2 : ℝ) • (ω x + pullbackJ ω x)

/-- The (2,0)+(0,2)-projection: π₋(ω) = (1/2)(ω - J*ω). -/
def proj20_02 (ω : DiffForm ℝ E F 2) : DiffForm ℝ E F 2 :=
  fun x => (1/2 : ℝ) • (ω x - pullbackJ ω x)

/-- The projections are complementary: π₊(ω) + π₋(ω) = ω. -/
theorem proj_sum (ω : DiffForm ℝ E F 2) :
    proj11 ω + proj20_02 ω = ω := by
  ext x m
  simp only [proj11, proj20_02, Pi.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply]
  module

/-- The (1,1)-projection of a (1,1)-form is itself. -/
theorem proj11_of_type11 {ω : DiffForm ℝ E F 2} (h : IsType11 ω) :
    proj11 ω = ω := by
  ext x m
  simp only [proj11, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply]
  have := congr_fun h x
  rw [show pullbackJ ω x = ω x from this]
  module

/-- The (2,0)+(0,2)-projection of a (2,0)+(0,2)-form is itself. -/
theorem proj20_02_of_type20_02 {ω : DiffForm ℝ E F 2} (h : IsType20_02 ω) :
    proj20_02 ω = ω := by
  ext x m
  simp only [proj20_02, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply]
  have := congr_fun h x
  rw [show pullbackJ ω x = -(ω x) from by
    rw [show -ω = fun x => -(ω x) from rfl] at this; exact this]
  simp only [ContinuousAlternatingMap.neg_apply]
  module

/-- Applying J twice to all arguments of a 2-form gives identity.
    J∘J∘m has each component negated, but for 2-forms the (-1)² cancels. -/
theorem apply_JJ_two (ω : DiffForm ℝ E F 2) (x : E) (m : Fin 2 → E) :
    ω x (acs.J ∘ acs.J ∘ m) = ω x m := by
  conv_lhs =>
    rw [show (acs.J ∘ acs.J ∘ m) = (fun i => (-1 : ℝ) • m i) from by
      ext i; simp [Function.comp, J_apply_sq]]
  rw [(ω x).map_smul_univ]
  simp [Finset.prod_const, Finset.card_fin]

/-- The (1,1)-projection produces a (1,1)-form. -/
theorem proj11_isType11 (ω : DiffForm ℝ E F 2) :
    IsType11 (proj11 ω) := by
  ext x m
  simp only [IsType11, proj11, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply]
  rw [apply_JJ_two ω x m]
  congr 1; exact add_comm _ _

/-- The (2,0)+(0,2)-projection produces a (2,0)+(0,2)-form. -/
theorem proj20_02_isType20_02 (ω : DiffForm ℝ E F 2) :
    IsType20_02 (proj20_02 ω) := by
  ext x m
  simp only [IsType20_02, proj20_02, pullbackJ_apply, Pi.neg_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.neg_apply]
  rw [apply_JJ_two ω x m]
  simp [smul_sub, neg_sub]

/-- Type (1,1) and type (2,0)+(0,2) are mutually exclusive (unless ω = 0). -/
theorem type_exclusive {ω : DiffForm ℝ E F 2}
    (h11 : IsType11 ω) (h20 : IsType20_02 ω) : ω = 0 := by
  have key : ω = -ω := by
    calc ω = pullbackJ ω := h11.symm
    _ = -ω := h20
  funext x
  have hx : ω x = -(ω x) := by
    have := congr_fun key x; rwa [Pi.neg_apply] at this
  have hadd : ω x + ω x = 0 := by
    have := sub_eq_zero.mpr hx; rwa [sub_neg_eq_add] at this
  rw [← two_smul ℝ] at hadd
  exact (smul_eq_zero.mp hadd).resolve_left (by norm_num)

-- ═══════════════════════════════════════════════════════════════════
-- COMPLEXIFIED (p,q)-DECOMPOSITION FOR 1-FORMS
-- ═══════════════════════════════════════════════════════════════════

-- For 1-forms, (J*)² = -id. The eigenvalues ±i live in ℂ.
-- The decomposition Ω¹_ℂ = Ω^{1,0} ⊕ Ω^{0,1} requires complex-valued forms.
-- We represent these as PAIRS of real forms: (α, β) = α + iβ.
-- The J* pullback acts componentwise: J*(α, β) = (J*α, J*β).
-- The (1,0)-projection: π^{1,0}(α+iβ) = (1/2)((α+J*β) + i(β-J*α))
-- The (0,1)-projection: π^{0,1}(α+iβ) = (1/2)((α-J*β) + i(β+J*α))

/-- A complexified k-form: a pair (re, im) of real k-forms.
    Represents re + i·im. -/
@[ext]
structure ComplexForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) where
  re : DiffForm ℝ E F n
  im : DiffForm ℝ E F n

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Embed a real form as a complexified form with zero imaginary part. -/
def ComplexForm.ofReal (ω : DiffForm ℝ E G n) : ComplexForm E G n :=
  ⟨ω, 0⟩

/-- The J* pullback on complexified forms: acts on both components. -/
def pullbackJC (ω : ComplexForm E G n) : ComplexForm E G n :=
  ⟨pullbackJ ω.re, pullbackJ ω.im⟩

/-- The (1,0)-projection of a complexified 1-form.
    π^{1,0}(α+iβ) = (1/2)((α+J*β) + i(β-J*α)).
    Projects onto the J*-eigenspace with eigenvalue +i. -/
def proj10 (ω : ComplexForm E G 1) : ComplexForm E G 1 :=
  ⟨fun x => (1/2 : ℝ) • (ω.re x + pullbackJ ω.im x),
   fun x => (1/2 : ℝ) • (ω.im x - pullbackJ ω.re x)⟩

/-- The (0,1)-projection of a complexified 1-form.
    π^{0,1}(α+iβ) = (1/2)((α-J*β) + i(β+J*α)).
    Projects onto the J*-eigenspace with eigenvalue -i. -/
def proj01 (ω : ComplexForm E G 1) : ComplexForm E G 1 :=
  ⟨fun x => (1/2 : ℝ) • (ω.re x - pullbackJ ω.im x),
   fun x => (1/2 : ℝ) • (ω.im x + pullbackJ ω.re x)⟩

/-- The projections sum to identity on each component. -/
theorem proj10_add_proj01_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 ω).re x m + (proj01 ω).re x m = ω.re x m := by
  simp only [proj10, proj01, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  module

theorem proj10_add_proj01_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 ω).im x m + (proj01 ω).im x m = ω.im x m := by
  simp only [proj10, proj01, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  module

/-- For a REAL 1-form ω (imaginary part = 0):
    the (1,0)-projection has re = (1/2)ω, im = -(1/2)J*ω.
    This represents (1/2)(ω - iJ*ω). -/
theorem proj10_ofReal_re (ω : DiffForm ℝ E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 (ComplexForm.ofReal ω)).re x m = (1/2 : ℝ) • ω x m := by
  simp [proj10, ComplexForm.ofReal, pullbackJ_zero]

theorem proj10_ofReal_im (ω : DiffForm ℝ E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 (ComplexForm.ofReal ω)).im x m = -(1/2 : ℝ) • pullbackJ ω x m := by
  simp [proj10, ComplexForm.ofReal, pullbackJ_zero]

/-- For a REAL 1-form: the (0,1)-projection has re = (1/2)ω, im = (1/2)J*ω. -/
theorem proj01_ofReal_re (ω : DiffForm ℝ E G 1) (x : E) (m : Fin 1 → E) :
    (proj01 (ComplexForm.ofReal ω)).re x m = (1/2 : ℝ) • ω x m := by
  simp [proj01, ComplexForm.ofReal, pullbackJ_zero]

theorem proj01_ofReal_im (ω : DiffForm ℝ E G 1) (x : E) (m : Fin 1 → E) :
    (proj01 (ComplexForm.ofReal ω)).im x m = (1/2 : ℝ) • pullbackJ ω x m := by
  simp [proj01, ComplexForm.ofReal, pullbackJ_zero]

/-- The J*-eigenvalue property for (1,0)-forms (real part):
    Re(J* π^{1,0}(ω)) = -Im(π^{1,0}(ω)).
    Combined with the imaginary part, this gives J* π^{1,0} = i · π^{1,0}. -/
theorem pullbackJ_proj10_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    pullbackJ (proj10 ω).re x m = -((proj10 ω).im x m) := by
  simp only [proj10, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  -- Need: (1/2)(J*re + J*J*im)(m) = -(1/2)(im - J*re)(m)
  -- i.e., (1/2)(J*re(J∘m) + J*J*im(J∘m)) = (1/2)(J*re(m) - im(m))
  -- J*J*im(J∘m) = im(J∘J∘J∘m). For degree 1: J∘J∘J∘m = fun i => J(J(J(m i))) = -(J(m i))
  -- So J*J*im(J∘m) = im(fun i => -(J(m i))) = -(im (J∘m)) for degree 1
  -- And J*re(J∘m) = re(J∘J∘m) = -(re(m)) for degree 1 [by pullbackJ_sq_one style]
  -- So LHS = (1/2)(-(re(m)) + (-(im(J∘m)))) = -(1/2)(re(m) + im(J∘m))
  -- RHS = -(1/2)(im(m) - re(J∘m)) = -(1/2)(im(m) - re(J∘m))
  -- Hmm these don't obviously match. Let me reconsider.
  -- Actually the pullbackJ of (proj10 ω).re is:
  -- pullbackJ ((1/2)(re + J*im)) at (x, m)
  -- = (1/2)(re(J∘m) + (J*im)(J∘m))
  -- = (1/2)(re(J∘m) + im(J∘J∘m))
  -- For degree 1: im(J∘J∘m) = -(im(m)) [by pullbackJ_sq_one]
  -- So = (1/2)(re(J∘m) - im(m))
  -- The RHS is -((1/2)(im - J*re))(m) = -(1/2)(im(m) - re(J∘m)) = (1/2)(re(J∘m) - im(m))
  -- These are EQUAL. ✓
  rw [show ω.im x (acs.J ∘ acs.J ∘ m) = -(ω.im x m) from by
    conv_lhs =>
      rw [show (acs.J ∘ acs.J ∘ m) = (fun i => (-1 : ℝ) • m i) from by
        ext i; simp [Function.comp, J_apply_sq]]
    rw [(ω.im x).map_smul_univ]; simp [Finset.prod_const, Finset.card_fin]]
  module

/-- Helper: for degree-1 forms, ω(J∘J∘m) = -(ω(m)). -/
theorem apply_JJ_one (ω : DiffForm ℝ E G 1) (x : E) (m : Fin 1 → E) :
    ω x (acs.J ∘ acs.J ∘ m) = -(ω x m) := by
  conv_lhs =>
    rw [show (acs.J ∘ acs.J ∘ m) = (fun i => (-1 : ℝ) • m i) from by
      ext i; simp [Function.comp, J_apply_sq]]
  rw [(ω x).map_smul_univ]; simp [Finset.prod_const, Finset.card_fin]

/-- The J*-eigenvalue property for (1,0)-forms (imaginary part):
    Im(J* π^{1,0}(ω)) = Re(π^{1,0}(ω)).
    Together with pullbackJ_proj10_re: J* π^{1,0} = i · π^{1,0}. -/
theorem pullbackJ_proj10_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    pullbackJ (proj10 ω).im x m = (proj10 ω).re x m := by
  simp only [proj10, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  rw [apply_JJ_one ω.re x m]
  module

/-- The J*-eigenvalue for (0,1)-forms (real part):
    Re(J* π^{0,1}(ω)) = Im(π^{0,1}(ω)). -/
theorem pullbackJ_proj01_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    pullbackJ (proj01 ω).re x m = (proj01 ω).im x m := by
  simp only [proj01, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  rw [apply_JJ_one ω.im x m]
  module

/-- The J*-eigenvalue for (0,1)-forms (imaginary part):
    Im(J* π^{0,1}(ω)) = -Re(π^{0,1}(ω)). -/
theorem pullbackJ_proj01_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    pullbackJ (proj01 ω).im x m = -((proj01 ω).re x m) := by
  simp only [proj01, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  rw [apply_JJ_one ω.re x m]
  module

/-- π^{1,0} is idempotent (real part). -/
theorem proj10_idem_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 (proj10 ω)).re x m = (proj10 ω).re x m := by
  simp only [proj10, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- π^{1,0} is idempotent (imaginary part). -/
theorem proj10_idem_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 (proj10 ω)).im x m = (proj10 ω).im x m := by
  simp only [proj10, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- π^{0,1} is idempotent (real part). -/
theorem proj01_idem_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj01 (proj01 ω)).re x m = (proj01 ω).re x m := by
  simp only [proj01, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- π^{0,1} is idempotent (imaginary part). -/
theorem proj01_idem_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj01 (proj01 ω)).im x m = (proj01 ω).im x m := by
  simp only [proj01, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- Orthogonality: π^{1,0} ∘ π^{0,1} = 0 (real part). -/
theorem proj10_proj01_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 (proj01 ω)).re x m = 0 := by
  simp only [proj10, proj01, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- Orthogonality: π^{1,0} ∘ π^{0,1} = 0 (imaginary part). -/
theorem proj10_proj01_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 (proj01 ω)).im x m = 0 := by
  simp only [proj10, proj01, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- Orthogonality: π^{0,1} ∘ π^{1,0} = 0 (real part). -/
theorem proj01_proj10_re (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj01 (proj10 ω)).re x m = 0 := by
  simp only [proj01, proj10, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- Orthogonality: π^{0,1} ∘ π^{1,0} = 0 (imaginary part). -/
theorem proj01_proj10_im (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj01 (proj10 ω)).im x m = 0 := by
  simp only [proj01, proj10, pullbackJ_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
  simp only [apply_JJ_one]
  module

/-- Hodge symmetry at degree 1: complex conjugation swaps (1,0) and (0,1).
    conj(π^{1,0}(ω)) = π^{0,1}(conj(ω)) where conj(α+iβ) = (α,-β). -/
theorem hodge_symmetry_one (ω : ComplexForm E G 1) (x : E) (m : Fin 1 → E) :
    (proj10 ⟨ω.re, -ω.im⟩).re x m = (proj01 ω).re x m ∧
    (proj10 ⟨ω.re, -ω.im⟩).im x m = -((proj01 ω).im x m) := by
  constructor
  · simp only [proj10, proj01, pullbackJ_apply, pullbackJ_neg,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.neg_apply,
      Pi.neg_apply]
    module
  · simp only [proj10, proj01, pullbackJ_apply, pullbackJ_neg,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.neg_apply,
      Pi.neg_apply]
    module

-- ═══════════════════════════════════════════════════════════════════
-- H^{p,q} SUBTYPES FOR THE GENERATOR
-- ═══════════════════════════════════════════════════════════════════

/-- The subtype of (1,0)-complexified 1-forms: those in the image of proj10.
    This IS H^{1,0} — the type the Generator's HodgeStructure needs. -/
def FormType10 (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AlmostComplexStr E] [NormedAddCommGroup G] [NormedSpace ℝ G] :=
  { ω : ComplexForm E G 1 //
    ∀ x m, (proj10 ω).re x m = ω.re x m ∧ (proj10 ω).im x m = ω.im x m }

/-- The subtype of (0,1)-complexified 1-forms. H^{0,1}. -/
def FormType01 (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AlmostComplexStr E] [NormedAddCommGroup G] [NormedSpace ℝ G] :=
  { ω : ComplexForm E G 1 //
    ∀ x m, (proj01 ω).re x m = ω.re x m ∧ (proj01 ω).im x m = ω.im x m }

/-- The subtype of (1,1) real 2-forms. -/
def FormType11Real (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AlmostComplexStr E] [NormedAddCommGroup G] [NormedSpace ℝ G] :=
  { ω : DiffForm ℝ E G 2 // IsType11 ω }

/-- The subtype of (2,0)+(0,2) real 2-forms. -/
def FormType2002Real (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AlmostComplexStr E] [NormedAddCommGroup G] [NormedSpace ℝ G] :=
  { ω : DiffForm ℝ E G 2 // IsType20_02 ω }

/-- proj10 produces a (1,0)-form. -/
theorem proj10_mem (ω : ComplexForm E G 1) :
    ∀ x m, (proj10 (proj10 ω)).re x m = (proj10 ω).re x m ∧
            (proj10 (proj10 ω)).im x m = (proj10 ω).im x m :=
  fun x m => ⟨proj10_idem_re ω x m, proj10_idem_im ω x m⟩

/-- proj01 produces a (0,1)-form. -/
theorem proj01_mem (ω : ComplexForm E G 1) :
    ∀ x m, (proj01 (proj01 ω)).re x m = (proj01 ω).re x m ∧
            (proj01 (proj01 ω)).im x m = (proj01 ω).im x m :=
  fun x m => ⟨proj01_idem_re ω x m, proj01_idem_im ω x m⟩

/-- The embedding of a (1,0)-form into the complexified 1-form space. -/
def FormType10.embed (ω : FormType10 E G) : ComplexForm E G 1 := ω.val

/-- The embedding of a (0,1)-form. -/
def FormType01.embed (ω : FormType01 E G) : ComplexForm E G 1 := ω.val

/-- The embedding of a (1,1) real 2-form into all 2-forms. -/
def FormType11Real.embed (ω : FormType11Real E G) : DiffForm ℝ E G 2 := ω.val

/-- Embeddings are injective. -/
theorem formType10_embed_injective :
    Function.Injective (FormType10.embed (E := E) (G := G)) :=
  Subtype.val_injective

theorem formType01_embed_injective :
    Function.Injective (FormType01.embed (E := E) (G := G)) :=
  Subtype.val_injective

theorem formType11_embed_injective :
    Function.Injective (FormType11Real.embed (E := E) (G := G)) :=
  Subtype.val_injective

-- ═══════════════════════════════════════════════════════════════════
-- HIGHER-DEGREE (p,q)-FORMS: DEGREE 2 COMPLEXIFIED
-- ═══════════════════════════════════════════════════════════════════

/-- A complexified 2-form is of type (1,1) if its real and imaginary
    parts are both of type (1,1) under J*. -/
def IsComplexType11 (ω : ComplexForm E G 2) : Prop :=
  IsType11 ω.re ∧ IsType11 ω.im

/-- A complexified 2-form is of type (2,0) if it satisfies the
    eigenvalue condition: J*(re) = -im and J*(im) = re
    (eigenvalue +i of J* on 2-forms for the holomorphic piece). -/
def IsComplexType20 (ω : ComplexForm E G 2) : Prop :=
  (∀ x m, pullbackJ ω.re x m = -(ω.im x m)) ∧
  (∀ x m, pullbackJ ω.im x m = ω.re x m)

/-- Type (0,2): eigenvalue -i. Conjugate of (2,0). -/
def IsComplexType02 (ω : ComplexForm E G 2) : Prop :=
  (∀ x m, pullbackJ ω.re x m = ω.im x m) ∧
  (∀ x m, pullbackJ ω.im x m = -(ω.re x m))

end

end Ramtastic.ComplexStructure.TypeDecomposition
