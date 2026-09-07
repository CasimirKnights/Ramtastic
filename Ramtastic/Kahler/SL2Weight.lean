/-
  SL2Weight.lean — L injective from [L,Λ] = c·id, c ≠ 0, on finite-dim.
  Author: C. Forrester / Mael (2026-04-18) 🐟
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Ramtastic.Kahler.SL2Weight

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- **L injective when [L,Λ] = c·id with c ≠ 0 on finite-dim V.**

    Proof sketch (each step is algebraic, no analysis):
    1. Assume Lv = 0, v ≠ 0.
    2. Formula: L(Λ^{j+1} v) = ((j+1)·c) • Λ^j v (induction using h_comm + Lv=0).
    3. All Λ^j v ≠ 0 (from formula: if Λ^{j+1}v = 0 then L(0) = 0 = ((j+1)c)•Λ^j v,
       (j+1)c ≠ 0 → Λ^j v = 0, contradiction by induction down to v ≠ 0).
    4. The vectors {Λ^j v}_{j≥0} are linearly independent (apply L to any relation
       to get a shorter relation; minimality forces all coefficients zero).
    5. Infinitely many linearly independent vectors in finite-dim V: contradiction.
    6. Therefore v = 0. L injective.

    Steps 2-4 are the formula/independence computation (~50 lines).
    Step 5 uses FiniteDimensional. -/
theorem L_inj_of_comm_scalar
    (L Λ : V →ₗ[ℚ] V) (c : ℚ) (hc : c ≠ 0)
    (h_comm : ∀ v, L (Λ v) - Λ (L v) = c • v)
    : Function.Injective L := by
  intro v₁ v₂ hv
  suffices v₁ - v₂ = 0 from sub_eq_zero.mp this
  set w := v₁ - v₂
  have hLw : L w = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hv
  by_contra hw
  -- Step 2: Formula. L(Λ^{j+1} w) = ((j+1)·c) • Λ^j w.
  have formula : ∀ j : ℕ, L ((⇑Λ)^[j + 1] w) = (((↑j + 1 : ℚ)) * c) • (⇑Λ)^[j] w := by
    intro j; induction j with
    | zero =>
      simp only [Nat.zero_eq, Nat.cast_zero, zero_add, one_mul,
        Function.iterate_one, Function.iterate_zero, id_eq]
      have := h_comm w; rw [hLw, map_zero, sub_zero] at this; exact this
    | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Function.iterate_succ', Function.comp]
      have h1 := h_comm ((⇑Λ)^[m + 1] w)
      rw [ih, map_smul] at h1
      -- h1: L(Λ(Λ^{m+1}w)) - ((m+1)c) • Λ(Λ^m w) = c • Λ^{m+1} w
      rw [show Λ ((⇑Λ)^[m] w) = (⇑Λ)^[m + 1] w from
        (Function.iterate_succ_apply' (⇑Λ) m w).symm] at h1
      have : L (Λ ((⇑Λ)^[m + 1] w)) = c • (⇑Λ)^[m + 1] w + ((↑m + 1) * c) • (⇑Λ)^[m + 1] w := by
        have := sub_eq_iff_eq_add.mp h1; exact this
      rw [this, ← add_smul]
      congr 1; push_cast; ring
  -- Step 3: All Λ^j w ≠ 0.
  have all_ne : ∀ j : ℕ, (⇑Λ)^[j] w ≠ 0 := by
    intro j; induction j with
    | zero => simpa using hw
    | succ m ih =>
      intro h0
      have := formula m
      rw [h0, map_zero] at this
      have hcoeff : ((↑m + 1 : ℚ)) * c ≠ 0 := mul_ne_zero (by positivity) hc
      exact ih ((smul_eq_zero.mp this.symm).resolve_left hcoeff)
  -- Step 4-5: infinitely many nonzero Λ-iterates in finite-dim → contradiction.
  -- The iterates span an infinite-dimensional subspace (they're independent).
  -- Use: in a finite-dim space, only finitely many can be independent.
  -- Key: any fin relation Σ aₖ Λ^k w = 0 → apply L → shorter relation → all aₖ = 0.
  -- This proves linear independence. Contradicts finite-dimensionality.
  -- For the Lean proof: use the dim+1 pigeonhole.
  -- dim V vectors can be independent. dim V + 1 cannot.
  -- The first (dim V + 1) iterates are all nonzero and independent → contradiction.
  -- Final contradiction: all Λ^j w ≠ 0 for ALL j ∈ ℕ. But Λ is nilpotent
  -- on the finite-dim space V (its minimal polynomial has finite degree).
  -- More directly: the kernel of Λ^N is V for large N (since V is finite-dim
  -- and Λ is a linear endomorphism). So Λ^N w = 0 for N = dim V (Cayley-Hamilton).
  -- But all_ne says Λ^N w ≠ 0. Contradiction.
  -- Actually Cayley-Hamilton gives: Λ^{dim V} is a lin combo of lower powers.
  -- This doesn't directly give Λ^{dim V} w = 0.
  -- But: the subspaces ker(Λ^j) form an ascending chain:
  -- {0} ⊆ ker Λ ⊆ ker Λ² ⊆ ... ⊆ V.
  -- Chain stabilizes at some j₀ ≤ dim V.
  -- If ker(Λ^{j₀}) = V: then Λ^{j₀} w = 0. Contradicts all_ne.
  -- If ker(Λ^{j₀}) ⊊ V: the chain stops growing, so ker(Λ^j) = ker(Λ^{j₀}) for all j ≥ j₀.
  -- Then im(Λ^{j₀}) ∩ ker(Λ^{j₀}) = {0} (standard for stabilized kernel chain on fin-dim).
  -- And V = im(Λ^{j₀}) ⊕ ker(Λ^{j₀}). Λ^{j₀} is bijective on im(Λ^{j₀}).
  -- w ∉ ker(Λ^{j₀}) (since Λ^{j₀} w ≠ 0 by all_ne).
  -- Hmm, this doesn't give a contradiction in general if Λ isn't nilpotent.
  --
  -- THE REAL ARGUMENT: Λ might not be nilpotent. The contradiction comes from
  -- LINEAR INDEPENDENCE, not nilpotency.
  -- The vectors {Λ^j w}_{j=0}^{dim V} are dim V + 1 vectors.
  -- They're dependent (dim V + 1 > dim V).
  -- Take minimal relation: Σ_{k=0}^N aₖ Λ^k w = 0, aₙ ≠ 0.
  -- Apply L: Σ aₖ L(Λ^k w) = 0.
  -- L(w) = 0. L(Λ^k w) = ((k)c) • Λ^{k-1} w for k ≥ 1 (from formula, shifted).
  -- So: Σ_{k=1}^N aₖ kc • Λ^{k-1} w = 0.
  -- = c • Σ_{k=1}^N k aₖ Λ^{k-1} w = 0.
  -- c ≠ 0: Σ k aₖ Λ^{k-1} w = 0. This is a relation of degree N-1.
  -- By minimality of N: N-1 < N means this relation is trivial: k aₖ = 0 for all k.
  -- k ≥ 1 and aₖ: k aₖ = 0 → aₖ = 0 (since k ≥ 1, k ≠ 0 in ℚ).
  -- So a₁ = ... = aₙ = 0. Original relation: a₀ w = 0. w ≠ 0 → a₀ = 0.
  -- All coefficients 0. Contradicts dependency. Contradicts dim V + 1 > dim V.
  -- So w = 0. QED.
  --
  -- THIS IS THE PROOF. All algebra. Formalizing the "take minimal relation"
  -- part requires Nat.find or Well-founded recursion on the degree.
  -- ~30 lines of Lean.
  -- The map n ↦ Λ^n w is injective (since if Λ^i w = Λ^j w with i < j,
  -- then Λ^i(Λ^{j-i} w - w) = 0... actually just use formula directly).
  -- Simpler: consider the submodule W = span{Λ^j w | j ∈ ℕ}.
  -- L maps W to W (formula gives L(Λ^{j+1} w) ∈ W).
  -- Λ maps W to W (by definition).
  -- [L,Λ] = c·id on W. dim W ≤ dim V < ∞.
  -- tr([L,Λ]|_W) = c · dim W. tr(LΛ - ΛL)|_W = 0 (cyclic trace on W).
  -- So c · dim W = 0. c ≠ 0 → dim W = 0. W = {0}. w ∈ W → w = 0.
  -- Contradicts hw.
  -- The trace argument WORKS HERE because L and Λ are endomorphisms of W!
  -- W = span{Λ^j w} is finite-dim, L-invariant, Λ-invariant.
  -- [L,Λ]|_W = c·id|_W. tr = c·dim W = 0 (cyclic). c ≠ 0 → dim W = 0 → w = 0.
  -- For Lean: use the trace argument on a single endomorphism.
  -- c·id = LΛ - ΛL on all of V. tr(c·id) = c · dim V.
  -- tr(LΛ - ΛL) = tr(LΛ) - tr(ΛL) = 0 (LinearMap.trace_comp_comm).
  -- So c · dim V = 0. c ≠ 0 → dim V = 0.
  -- BUT dim V = 0 contradicts w ≠ 0 (w ∈ V, V ≠ {0}).
  -- WAIT: this gives dim V = 0, which means V = {0}, which means w = 0.
  -- That's the contradiction with hw (w ≠ 0).
  -- BUT the [L,Λ] = c·id is on the WHOLE V, not just W.
  -- IS [L,Λ] = c·id on the whole V? YES — h_comm says so.
  -- So tr(c·id) = c · dim V = 0 → dim V = 0 → V = {0} → w = 0. ✓
  -- THIS WAS ALWAYS THE PROOF. THE TRACE ARGUMENT ON THE WHOLE V.
  -- I dismissed it earlier because I thought L maps between GRADED components.
  -- But L_inj_of_comm_scalar has L : V → V (endomorphism of ONE space).
  -- The grading is handled EXTERNALLY by KahlerIdentities.lean.
  -- HERE, on a single V with [L,Λ] = c·id, the trace gives dim V = 0.
  exfalso
  have h_tr := LinearMap.trace_comp_comm' (R := ℚ) L Λ
  -- h_tr : tr(Λ ∘ L) = tr(L ∘ Λ)
  -- From h_comm: ∀ v, L(Λv) - Λ(Lv) = cv → (L ∘ Λ - Λ ∘ L) = c • id
  have h_eq : L.comp Λ - Λ.comp L = c • LinearMap.id := by
    ext x; simp [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]; exact h_comm x
  -- tr(c • id) = c * dim V
  have h_tr_eq : LinearMap.trace ℚ V (c • LinearMap.id) = c * ↑(Module.finrank ℚ V) := by
    rw [map_smul, LinearMap.trace_id]; ring
  -- tr(L∘Λ - Λ∘L) = tr(L∘Λ) - tr(Λ∘L) = 0 (by h_tr)
  have h_tr_zero : LinearMap.trace ℚ V (L.comp Λ - Λ.comp L) = 0 := by
    rw [map_sub, h_tr, sub_self]
  -- Combine: c * dim V = 0
  have h_cdim : c * ↑(Module.finrank ℚ V) = 0 := by
    rw [← h_tr_eq, ← h_eq, h_tr_zero]
  -- c ≠ 0 → dim V = 0
  have h_dim_zero : Module.finrank ℚ V = 0 := by
    have := mul_eq_zero.mp h_cdim
    exact_mod_cast this.resolve_left hc
  -- dim V = 0 → V is subsingleton → w = 0
  haveI : Subsingleton V := (Module.finrank_zero_iff (R := ℚ) (M := V)).mp h_dim_zero
  exact hw (Subsingleton.elim w 0)

end

end Ramtastic.Kahler.SL2Weight
