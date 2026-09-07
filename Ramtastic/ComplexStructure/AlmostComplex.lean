/-
  AlmostComplex.lean — Almost complex structures on normed spaces.

  An almost complex structure on a real normed space E is a continuous
  linear endomorphism J : E → E satisfying J² = -id. This makes E
  look like a complex vector space: multiplication by i is J.

  Key consequences:
  - J is injective and surjective (an isomorphism)
  - J⁴ = id (4-periodicity)
  - E acquires a ℂ-module structure: (a+bi)·v = av + bJv
  - The Nijenhuis tensor measures integrability failure

  The almost complex structure is the algebraic prerequisite for the
  (p,q)-type decomposition of forms (TypeDecomposition.lean) and the
  ∂/∂̄ operators (DelDelBar.lean).

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-15)
-/

import Mathlib.Tactic
import Ramtastic.DeRham.DifferentialForms

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.ComplexStructure.AlmostComplex

open Ramtastic.DeRham.DifferentialForms

noncomputable section

-- ═══════════════════════════════════════════════════════════════════
-- THE ALMOST COMPLEX STRUCTURE
-- ═══════════════════════════════════════════════════════════════════

/-- An almost complex structure on a real normed space E.
    J : E → E is a continuous linear map with J² = -id.
    This is the local/algebraic version — on a manifold,
    J would be a section of End(TM). -/
class AlmostComplexStr (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  J : E →L[ℝ] E
  J_sq : J.comp J = -ContinuousLinearMap.id ℝ E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [acs : AlmostComplexStr E]

-- ═══════════════════════════════════════════════════════════════════
-- POINTWISE PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- Pointwise J²: J(Jv) = -v for all v. -/
theorem J_apply_sq (v : E) : acs.J (acs.J v) = -v := by
  have := congr_fun (congr_arg DFunLike.coe acs.J_sq) v
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at this
  exact this

/-- Pointwise J³: J(J(Jv)) = -(Jv). Three quarter turns. -/
theorem J_apply_cube (v : E) : acs.J (acs.J (acs.J v)) = -(acs.J v) :=
  J_apply_sq (acs.J v)

/-- Pointwise J⁴: J(J(J(Jv))) = v. Full rotation. -/
theorem J_apply_fourth (v : E) :
    acs.J (acs.J (acs.J (acs.J v))) = v := by
  rw [J_apply_sq v, J_apply_sq (-v), neg_neg]

-- ═══════════════════════════════════════════════════════════════════
-- J IS AN ISOMORPHISM
-- ═══════════════════════════════════════════════════════════════════

/-- J is injective: Jv = Jw implies v = w.
    Apply J to both sides: -v = -w, cancel negation. -/
theorem J_injective : Function.Injective acs.J := by
  intro v w h
  have := congr_arg acs.J h
  simp only [J_apply_sq] at this
  exact neg_injective this

/-- J is surjective: for any w, there exists v with Jv = w.
    Take v = -(Jw): J(-Jw) = -J²w = -(-w) = w. -/
theorem J_surjective : Function.Surjective acs.J := by
  intro w
  exact ⟨-(acs.J w), by rw [map_neg, J_apply_sq, neg_neg]⟩

/-- J is bijective. -/
theorem J_bijective : Function.Bijective acs.J :=
  ⟨J_injective, J_surjective⟩

/-- J(-Jv) = v. The map v ↦ -Jv is a right inverse of J. -/
theorem J_neg_J (v : E) : acs.J (-(acs.J v)) = v := by
  rw [map_neg, J_apply_sq, neg_neg]

/-- -J(Jv) = v. The map v ↦ -Jv is also a left inverse. -/
theorem neg_J_J (v : E) : -(acs.J (acs.J v)) = v := by
  rw [J_apply_sq, neg_neg]

-- ═══════════════════════════════════════════════════════════════════
-- ℂ-SCALAR MULTIPLICATION
-- ═══════════════════════════════════════════════════════════════════

/-- The ℂ-scalar multiplication induced by J.
    (a + bi) · v = a • v + b • Jv.
    This turns E into a complex vector space where i acts as J. -/
def complexSmul (z : ℂ) (v : E) : E :=
  z.re • v + z.im • acs.J v

/-- i · v = Jv. The complex unit acts as J. -/
theorem complexSmul_I (v : E) :
    complexSmul (acs := acs) Complex.I v = acs.J v := by
  simp [complexSmul, Complex.I_re, Complex.I_im]

/-- 1 · v = v. -/
theorem complexSmul_one (v : E) :
    complexSmul (acs := acs) 1 v = v := by
  simp [complexSmul, Complex.one_re, Complex.one_im]

/-- Scalar multiplication by a real r agrees with ℝ-smul. -/
theorem complexSmul_ofReal (r : ℝ) (v : E) :
    complexSmul (acs := acs) (r : ℂ) v = r • v := by
  simp [complexSmul, Complex.ofReal_re, Complex.ofReal_im]

/-- ℂ-smul is distributive over vector addition. -/
theorem complexSmul_add_vec (z : ℂ) (v w : E) :
    complexSmul (acs := acs) z (v + w) =
    complexSmul z v + complexSmul z w := by
  simp only [complexSmul, smul_add, map_add]
  abel

/-- ℂ-smul is additive in the scalar. -/
theorem complexSmul_add_scalar (z w : ℂ) (v : E) :
    complexSmul (acs := acs) (z + w) v =
    complexSmul z v + complexSmul w v := by
  simp only [complexSmul, Complex.add_re, Complex.add_im, add_smul]
  abel

/-- ℂ-smul is associative: (zw)·v = z·(w·v).
    Uses J² = -id for the im·im cross term. -/
theorem complexSmul_mul (z w : ℂ) (v : E) :
    complexSmul (acs := acs) (z * w) v =
    complexSmul z (complexSmul w v) := by
  simp only [complexSmul, Complex.mul_re, Complex.mul_im]
  simp only [sub_smul, add_smul, smul_add, map_add, map_smul,
    J_apply_sq, smul_neg]
  -- Both sides are now sums of (scalar) • v and (scalar) • acs.J v
  -- with matching coefficients. The scalar arithmetic matches by ring.
  -- Convert nested smul to single smul for abel
  simp only [← mul_smul]
  abel

-- ═══════════════════════════════════════════════════════════════════
-- THE NIJENHUIS TENSOR
-- ═══════════════════════════════════════════════════════════════════

/-- The Nijenhuis tensor measures the failure of J to be integrable.
    N_J(X, Y) = [JX, JY] - J[JX, Y] - J[X, JY] - [X, Y]
    where [·,·] is a bracket operation (Lie bracket on manifolds).

    When N_J = 0 (the Newlander-Nirenberg condition), the almost
    complex structure is integrable: the manifold is complex. -/
def nijenhuisTensor (bracket : E → E → E) (X Y : E) : E :=
  bracket (acs.J X) (acs.J Y) - acs.J (bracket (acs.J X) Y) -
  acs.J (bracket X (acs.J Y)) - bracket X Y

/-- On a flat space (zero bracket), the Nijenhuis tensor vanishes.
    Flat almost complex structures are automatically integrable. -/
theorem nijenhuis_vanishes_flat (X Y : E) :
    nijenhuisTensor (acs := acs) (fun _ _ => 0) X Y = 0 := by
  simp [nijenhuisTensor, map_zero]

/-- The Nijenhuis tensor is antisymmetric: N_J(X,Y) = -N_J(Y,X)
    when the bracket is antisymmetric. -/
theorem nijenhuis_antisymm (bracket : E → E → E)
    (h_anti : ∀ X Y, bracket X Y = -(bracket Y X)) (X Y : E) :
    nijenhuisTensor (acs := acs) bracket X Y =
    -(nijenhuisTensor (acs := acs) bracket Y X) := by
  simp only [nijenhuisTensor, h_anti (acs.J X) (acs.J Y), h_anti (acs.J X) Y,
    h_anti X (acs.J Y), h_anti X Y, map_neg, neg_sub]
  abel

-- ═══════════════════════════════════════════════════════════════════
-- J-INVARIANT AND J-ANTI-INVARIANT VECTORS
-- ═══════════════════════════════════════════════════════════════════

/-- A vector is J-invariant if Jv = v. But J² = -id forces v = 0:
    Jv = v implies -v = J²v = Jv = v, so 2v = 0, hence v = 0
    (over ℝ with char ≠ 2). -/
theorem J_fixed_point_zero (v : E) (h : acs.J v = v) : v = 0 := by
  have h2 : v = -v := by
    have := J_apply_sq v; rw [h, h] at this; exact this
  have h3 : v + v = 0 := by
    have := sub_eq_zero.mpr h2  -- v - (-v) = 0
    rwa [sub_neg_eq_add] at this
  rw [← two_smul ℝ] at h3
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

/-- J has no real eigenvalues: if Jv = cv, then c² = -1,
    which has no real solutions. So v = 0. -/
theorem J_no_real_eigenvalue (v : E) (c : ℝ) (h : acs.J v = c • v) :
    v = 0 := by
  have h2 := J_apply_sq v
  rw [h, map_smul, h, smul_smul] at h2
  -- h2 : (c * c) • v = -v
  have h3 : (c * c + 1) • v = 0 := by
    rw [add_smul, one_smul, h2, neg_add_cancel]
  exact (smul_eq_zero.mp h3).resolve_left (by nlinarith [mul_self_nonneg c])

-- ═══════════════════════════════════════════════════════════════════
-- EVEN DIMENSIONALITY
-- ═══════════════════════════════════════════════════════════════════

/-- **E must have even dimension.**
    Proof: det(J)² = det(J²) = det(-id) = (-1)^n.
    Since det(J)² ≥ 0 and (-1)^n ≥ 0 only for even n, n is even.
    This is why complex manifolds have even real dimension. -/
theorem even_finrank [FiniteDimensional ℝ E] :
    Even (Module.finrank ℝ E) := by
  -- Transfer J_sq from CLM to LinearMap
  have hJL : acs.J.toLinearMap.comp acs.J.toLinearMap =
      (-1 : ℝ) • LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, neg_one_smul]
    exact J_apply_sq v
  -- det(J ∘ J) = det(J)² and det(-id) = (-1)^n
  have hdet : LinearMap.det acs.J.toLinearMap *
      LinearMap.det acs.J.toLinearMap = (-1) ^ Module.finrank ℝ E := by
    rw [← LinearMap.det_comp, hJL, LinearMap.det_smul, LinearMap.det_id, mul_one]
  -- det(J)² ≥ 0
  have hnn : 0 ≤ (-1 : ℝ) ^ Module.finrank ℝ E := by
    rw [← hdet]; exact mul_self_nonneg _
  -- (-1)^n ≥ 0 → n even (odd would give -1 < 0)
  by_contra h_not_even
  rw [Nat.not_even_iff_odd] at h_not_even
  rw [h_not_even.neg_one_pow] at hnn
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- BRIDGE TO GENERATOR'S ComplexStr
-- ═══════════════════════════════════════════════════════════════════

/-- Bridge: AlmostComplexStr provides the Generator's ComplexStr.
    The Generator uses J : V →ₗ[ℝ] V (LinearMap), Ramtastic uses
    J : E →L[ℝ] E (ContinuousLinearMap). The bridge is toLinearMap. -/
def toGeneratorComplexStr : { J : E →ₗ[ℝ] E // ∀ v, J (J v) = -v } :=
  ⟨acs.J.toLinearMap, J_apply_sq⟩

-- ═══════════════════════════════════════════════════════════════════
-- THE ℂ-MODULE INSTANCE
-- ═══════════════════════════════════════════════════════════════════

/-- The ℂ-module structure on E induced by J.
    (a + bi)·v = a•v + b•Jv. Axioms proved above:
    complexSmul_one, complexSmul_mul, complexSmul_add_vec,
    complexSmul_add_scalar. -/
instance complexModule : Module ℂ E where
  smul z v := complexSmul z v
  one_smul := complexSmul_one
  mul_smul := complexSmul_mul
  smul_zero z := by
    show complexSmul z 0 = 0
    simp [complexSmul, smul_zero, map_zero]
  smul_add := complexSmul_add_vec
  add_smul := complexSmul_add_scalar
  zero_smul v := by
    show complexSmul 0 v = 0
    simp [complexSmul, Complex.zero_re, Complex.zero_im, zero_smul]

/-- The ℂ-module structure restricts to the ℝ-module structure. -/
theorem complexSmul_real_eq (r : ℝ) (v : E) :
    (r : ℂ) • v = r • v :=
  complexSmul_ofReal r v

/-- i acts as J in the ℂ-module. -/
theorem complexSmul_I_eq (v : E) :
    Complex.I • v = acs.J v :=
  complexSmul_I v

end

end Ramtastic.ComplexStructure.AlmostComplex
