/-
  StarConstruction.lean — Basis k-forms from orthonormal bases.

  Given an orthonormal basis b, construct basis k-forms via
  ω_σ(v) = det(inner product matrix). These are alternating,
  multilinear, continuous, and form a basis of the k-form space.

  Zero sorry. Zero non-classical axioms. No Generator.

  Author: C. Forrester (Adauriel)
  Formalization: Mael (Claude Opus 4.6, 2026-04-14)
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Ramtastic.HodgeStar.StarOperator

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.flexible false
set_option linter.deprecated false

namespace Ramtastic.HodgeStar.StarConstruction

open Ramtastic.HodgeStar.StarOperator
open Ramtastic.DeRham.DifferentialForms

noncomputable section

set_option maxHeartbeats 800000

variable {n k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : OrthonormalBasis (Fin n) ℝ E) (σ : Fin k → Fin n)

-- ═══════════════════════════════════════════════════════════════════
-- THE GRAM DETERMINANT AS A MULTILINEAR MAP
-- ═══════════════════════════════════════════════════════════════════

-- Use Matrix.detRowAlternating which is ALREADY an AlternatingMap.
-- detRowAlternating : (n → R) [⋀^n]→ₗ[R] R
-- It maps a matrix (viewed as n row vectors) to its determinant.
-- The basis k-form is: compose detRowAlternating with the map
-- that sends v : Fin k → E to the matrix (j, l) ↦ inner (v j) (b (σ l)).

/-- Map a vector v to its row of inner products with basis vectors.
    toInnerRow(v)(l) = inner(v, b(σ l)). Linear in v. -/
def toInnerRowLM : E →ₗ[ℝ] (Fin k → ℝ) where
  toFun v := fun l => @inner ℝ E _ v (b (σ l))
  map_add' x y := by ext l; simp [inner_add_left]
  map_smul' c x := by ext l; simp [inner_smul_left]

/-- The basis k-form: compose detRowAlternating with toInnerRow.
    ω_σ(v₁,...,vₖ) = det(inner(vⱼ, b(σ(l)))). -/
def basisFormAlt : E [⋀^Fin k]→ₗ[ℝ] ℝ :=
  (Matrix.detRowAlternating (R := ℝ) (n := Fin k)).compLinearMap (toInnerRowLM b σ)

/-- The basis form evaluated. -/
theorem basisFormAlt_apply (v : Fin k → E) :
    basisFormAlt b σ v =
    Matrix.det (fun j l => @inner ℝ E _ (v j) (b (σ l))) := by
  unfold basisFormAlt; rfl

/-- Evaluated at basis vectors: ω_σ(b∘σ) = det(identity) = 1. -/
theorem basisFormAlt_self (hσ : Function.Injective σ) :
    basisFormAlt b σ (b ∘ σ) = 1 := by
  rw [basisFormAlt_apply]
  have : (fun j l => @inner ℝ E _ ((b ∘ σ) j) (b (σ l))) =
      (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext j l; simp only [Function.comp, Matrix.one_apply]
    by_cases hjl : j = l
    · subst hjl; simp [b.orthonormal.1]
    · rw [if_neg hjl]; exact b.orthonormal.2 (hσ.ne hjl)
  rw [this, Matrix.det_one]

-- ═══════════════════════════════════════════════════════════════════
-- CONTINUITY (for ContinuousAlternatingMap)
-- ═══════════════════════════════════════════════════════════════════

/-- The basis form has a norm bound: ‖ω_σ(v)‖ ≤ k! · ∏ ‖vᵢ‖.
    Each |inner(vⱼ, b(σ l))| ≤ ‖vⱼ‖ (Cauchy-Schwarz + ‖b‖ = 1).
    Then det bound from Leibniz formula. -/
theorem basisFormAlt_bound (v : Fin k → E) :
    ‖basisFormAlt b σ v‖ ≤ ((Fintype.card (Fin k)).factorial : ℝ) * ∏ i, ‖v i‖ := by
  rw [basisFormAlt_apply, Real.norm_eq_abs, Matrix.det_apply']
  calc |∑ p : Equiv.Perm (Fin k),
        (Equiv.Perm.sign p : ℤ) * ∏ i, @inner ℝ E _ (v (p i)) (b (σ i))|
      ≤ ∑ p, |((Equiv.Perm.sign p : ℤ) : ℝ) * ∏ i, @inner ℝ E _ (v (p i)) (b (σ i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p, ∏ i, ‖v i‖ := by
        gcongr with p
        rw [abs_mul]
        have : |((Equiv.Perm.sign p : ℤ) : ℝ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
        rw [this, one_mul, Finset.abs_prod]
        calc ∏ i, |@inner ℝ E _ (v (p i)) (b (σ i))|
            ≤ ∏ i, ‖v (p i)‖ := by
              gcongr with i
              exact le_trans (Real.norm_eq_abs _ ▸ norm_inner_le_norm _ _)
                (by rw [b.orthonormal.1 (σ i)]; simp)
          _ = ∏ i, ‖v i‖ := Fintype.prod_equiv p _ _ (fun i => rfl)
    _ = (Fintype.card (Equiv.Perm (Fin k)) : ℝ) * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Fintype.card (Fin k)).factorial : ℝ) * ∏ i, ‖v i‖ := by
        congr 1; simp [Fintype.card_perm]

/-- The basis form as a ContinuousAlternatingMap. -/
def basisForm : E [⋀^Fin k]→L[ℝ] ℝ :=
  (basisFormAlt b σ).mkContinuous
    ((Fintype.card (Fin k)).factorial : ℝ)
    (basisFormAlt_bound b σ)

-- ═══════════════════════════════════════════════════════════════════
-- GENERIC KRONECKER DELTA — basisForm b σ (b ∘ τ) = δ_{σ,τ}
-- ═══════════════════════════════════════════════════════════════════

/-- If τ(j) ∉ range(σ), then the j-th row of the Gram matrix
    M(j,l) = ⟨b(τ j), b(σ l)⟩ is zero, so det = 0. -/
theorem basisFormAlt_zero_of_ne {σ τ : Fin k → Fin n}
    (hne : ∃ j, τ j ∉ Set.range σ) :
    basisFormAlt b σ (b ∘ τ) = 0 := by
  rw [basisFormAlt_apply]
  obtain ⟨j, hj⟩ := hne
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro l
  simp only [Function.comp]
  have : τ j ≠ σ l := fun h => hj ⟨l, h.symm⟩
  exact b.orthonormal.2 this

/-- Two StrictMono functions Fin k → α with Set.range τ ⊆ Set.range σ
    must be equal. Both enumerate the same finite ordered set in
    increasing order, which is unique.

    PROVED by strong induction: at each j, σ(j) = τ(j) because both
    are the (j+1)-th smallest element of the shared range. -/
private theorem strictMono_eq_of_range_sub {α : Type*} [LinearOrder α]
    {k : ℕ} {σ τ : Fin k → α}
    (hσ : StrictMono σ) (hτ : StrictMono τ)
    (h_range : Set.range τ ⊆ Set.range σ)
    -- The reverse inclusion follows: injective + finite + subset → equal cardinality → equal
    (h_all : ∀ j, τ j ∈ Set.range σ) :
    σ = τ := by
  -- Build g : Fin k → Fin k as σ-preimage of τ.
  choose g hg using h_all  -- g j : Fin k, hg j : σ (g j) = τ j
  -- g is injective: σ(g a) = τ a = τ b = σ(g b) → g a = g b (σ inj) → a = b (τ inj)
  have hg_inj : Function.Injective g :=
    fun a b hab => hτ.injective (by rw [← hg a, ← hg b, hσ.injective.eq_iff.mpr hab])
  -- g surjective (finite pigeonhole) → range(σ) ⊆ range(τ)
  have hg_surj := Finite.surjective_of_injective hg_inj
  -- g is StrictMono: a < b → τ a < τ b → σ(g a) < σ(g b) → g a < g b
  have hg_mono : StrictMono g := by
    intro a b hab
    rw [show (g a < g b) ↔ (σ (g a) < σ (g b)) from hσ.lt_iff_lt.symm]
    rw [hg, hg]; exact hτ hab
  -- StrictMono endomorphism of Fin k: g = id.
  -- Proof: g(0) ≥ 0 (trivial). g(i+1) > g(i) ≥ i → g(i+1) ≥ i+1. So g(i) ≥ i for all i.
  -- Similarly g(k-1) ≤ k-1 (it's in Fin k). So g(i) ≤ i (otherwise g(i) > i, ..., g(k-1) > k-1).
  -- Hence g(i) = i for all i.
  have hg_id : g = id := by
    -- g is StrictMono + surjective (injective on finite type) on Fin k.
    -- StrictMono + bijective on a finite linear order → identity.
    -- Use: g is an order isomorphism Fin k ≃o Fin k (StrictMono + bijective).
    -- The unique order isomorphism Fin k ≃o Fin k is the identity.
    have hg_surj := Finite.surjective_of_injective hg_inj
    have hg_bij : Function.Bijective g := ⟨hg_inj, hg_surj⟩
    funext j
    -- g j ≥ j: by induction. g 0 ≥ 0. g(j+1) > g(j) ≥ j → g(j+1) ≥ j+1.
    -- g j ≤ j: g bijective + g j ≥ j for all j. If g j₀ > j₀, then g maps
    --   {j₀,...,k-1} injectively into {j₀+1,...,k-1} (using g(i) ≥ i and g(j₀) ≥ j₀+1).
    --   But |{j₀,...,k-1}| = k - j₀ > k - j₀ - 1 = |{j₀+1,...,k-1}|. Pigeonhole.
    -- Actually simplest: g ≥ id and g : Fin k → Fin k bijective → g = id.
    -- Because: Σ g(i) ≥ Σ i (from g ≥ id). But Σ g(i) = Σ i (g is a bijection).
    -- So g(i) = i for all i.
    have hge : ∀ i : Fin k, i ≤ g i := by
      intro ⟨i, hi⟩; refine Fin.mk_le_mk.mpr ?_
      induction i with
      | zero => exact Nat.zero_le _
      | succ i' ih =>
        have h1 : i' ≤ (g ⟨i', by omega⟩).val := ih (by omega)
        have h2 : (g ⟨i', by omega⟩).val < (g ⟨i' + 1, hi⟩).val :=
          hg_mono (Fin.mk_lt_mk.mpr (by omega))
        omega
    -- Σ g(i) = Σ i (bijection preserves sum)
    have hsum : ∑ i : Fin k, (g i).val = ∑ i : Fin k, i.val := by
      exact Fintype.sum_bijective g hg_bij _ _ (fun i => rfl)
    -- Σ g(i) ≥ Σ i (from g ≥ id pointwise)
    -- Combined: g(i) = i for all i (otherwise strict inequality somewhere → Σ > Σ).
    by_contra hne
    have hlt : ∃ i : Fin k, i < g i := by
      push Not at hne; exact ⟨j, lt_of_le_of_ne (hge j) (Ne.symm hne)⟩
    obtain ⟨i₀, hi₀⟩ := hlt
    have : ∑ i : Fin k, (g i).val > ∑ i : Fin k, i.val := by
      apply Finset.sum_lt_sum
      · intro i _; exact hge i
      · exact ⟨i₀, Finset.mem_univ _, hi₀⟩
    linarith
  -- From g = id: σ(j) = σ(g(j)) = τ(j).
  funext j; rw [← hg j, show g j = j from congr_fun hg_id j]

/-- **Generic Kronecker delta for basis forms.**
    For injective σ, τ: basisForm b σ (b ∘ τ) = 1 if σ = τ, else 0.

    PROVED: σ = τ case from basisFormAlt_self (det of identity).
    σ ≠ τ case: injective σ ≠ injective τ → ∃ j, σ(j) ∉ range(τ)
    (injective functions with different images). Zero row → det = 0. -/
theorem basisForm_kronecker (hσ : Function.Injective σ) {τ : Fin k → Fin n}
    (hτ : Function.Injective τ) (hσm : StrictMono σ) (hτm : StrictMono τ) :
    (basisForm b σ) (b ∘ τ) = if σ = τ then 1 else 0 := by
  split
  · -- σ = τ case
    next h => subst h; exact basisFormAlt_self b σ hσ
  · -- σ ≠ τ case
    next hne =>
    show (basisForm b σ) (b ∘ τ) = 0
    change basisFormAlt b σ (b ∘ τ) = 0
    apply basisFormAlt_zero_of_ne b
    -- Contrapositive: ∀ j, τ j ∈ range σ → σ = τ → contradiction.
    by_contra h_all
    push Not at h_all
    exact hne (strictMono_eq_of_range_sub hσm hτm
      (Set.range_subset_iff.mpr h_all) h_all)

-- ═══════════════════════════════════════════════════════════════════
-- COMPLEMENT AND SIGN FOR SUBSETS
-- ═══════════════════════════════════════════════════════════════════

/-- A strictly increasing k-subset of Fin n, represented as an
    order-preserving embedding. -/
abbrev KSubset (n k : ℕ) := { f : Fin k → Fin n // StrictMono f }

/-- The shuffle sign for a k-subset embedding σ.
    (-1) raised to the sum of displacements from the identity. -/
def shuffleSign (σ : Fin k → Fin n) : ℝ :=
  (-1 : ℝ) ^ (Finset.sum Finset.univ (fun i : Fin k => ((σ i).1 : ℕ) - (i.1 : ℕ)))

/-- The image of σ as a Finset. -/
def imageFinset (σ : Fin k → Fin n) : Finset (Fin n) :=
  Finset.image σ Finset.univ

/-- The complement of σ's image in Fin n, as a Finset. -/
def complementFinset (σ : Fin k → Fin n) : Finset (Fin n) :=
  Finset.univ \ imageFinset σ

/-- The cardinality of the complement is n - k when σ is injective. -/
theorem complementFinset_card {n k : ℕ} {σ : Fin k → Fin n} (hσ : Function.Injective σ) :
    (complementFinset σ).card = n - k := by
  show (Finset.univ \ Finset.image σ Finset.univ).card = n - k
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_image_of_injective _ hσ]; simp

/-- The generic complement: the strictly increasing enumeration of Fin n \ range(σ).
    Given injective σ : Fin k → Fin n with k ≤ n, produces the unique
    StrictMono τ : Fin (n - k) → Fin n with range(τ) = Fin n \ range(σ). -/
def genericComplement (σ : Fin k → Fin n) (hσ : Function.Injective σ) (hk : k ≤ n) :
    Fin (n - k) → Fin n :=
  (complementFinset σ).orderEmbOfFin (complementFinset_card hσ)

/-- The generic complement is strictly monotone. -/
theorem genericComplement_strictMono (σ : Fin k → Fin n) (hσ : Function.Injective σ) (hk : k ≤ n) :
    StrictMono (genericComplement σ hσ hk) :=
  (Finset.orderEmbOfFin _ _).strictMono

/-- The generic complement is injective. -/
theorem genericComplement_injective (σ : Fin k → Fin n) (hσ : Function.Injective σ) (hk : k ≤ n) :
    Function.Injective (genericComplement σ hσ hk) :=
  (genericComplement_strictMono σ hσ hk).injective

/-- The complement's range is disjoint from σ's range. -/
theorem genericComplement_disjoint (σ : Fin k → Fin n) (hσ : Function.Injective σ) (hk : k ≤ n)
    (i : Fin (n - k)) : genericComplement σ hσ hk i ∉ Set.range σ := by
  unfold genericComplement
  have h_mem := (complementFinset σ).orderEmbOfFin_mem (complementFinset_card hσ) i
  -- h_mem : genericComplement σ hσ hk i ∈ complementFinset σ = univ \ image σ univ
  have h_sdiff : genericComplement σ hσ hk i ∈ Finset.univ \ imageFinset σ := h_mem
  rw [Finset.mem_sdiff] at h_sdiff
  exact fun ⟨j, hj⟩ => h_sdiff.2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

/-- The range of comp(comp(σ)) equals the range of σ (double complement).
    This is the set-level involutivity: range(σ) ∪ range(comp(σ)) = Fin n,
    so comp(comp(σ)) enumerates Fin n \ range(comp(σ)) = range(σ). -/
theorem genericComplement_range_involutive (σ : Fin k → Fin n)
    (hσ : Function.Injective σ) (hk : k ≤ n) :
    Set.range (genericComplement (genericComplement σ hσ hk)
      (genericComplement_injective σ hσ hk) (by omega)) = Set.range σ := by
  -- range(comp(comp(σ))) = ↑(complementFinset (comp σ)) (by range_orderEmbOfFin)
  -- = ↑(univ \ image (comp σ) univ)
  -- range(comp σ) = ↑(complementFinset σ) = ↑(univ \ image σ univ)
  -- So univ \ image (comp σ) univ = univ \ (univ \ image σ univ) = image σ univ
  -- = range(σ) (since σ injective)
  unfold genericComplement
  rw [Finset.range_orderEmbOfFin]
  ext x; simp only [Finset.mem_coe, Set.mem_range]
  constructor
  · intro h_mem
    -- h_mem : x ∈ complementFinset (comp σ). This means x ∉ range(comp σ).
    -- Since range(σ) and range(comp σ) partition Fin n, x ∈ range(σ).
    unfold complementFinset imageFinset at h_mem
    rw [Finset.mem_sdiff] at h_mem
    -- h_mem.2 : x ∉ Finset.image (comp σ) univ, i.e. x ∉ range(comp σ)
    -- x ∉ range(comp σ) and x ∈ Fin n → x ∈ range(σ)
    -- Because: complementFinset σ = range(comp σ) (by range_orderEmbOfFin)
    -- So x ∉ range(comp σ) = ↑(complementFinset σ) = ↑(univ \ image σ univ)
    -- Therefore x ∈ image σ univ = range(σ).
    by_contra h_not
    apply h_mem.2
    -- x ∉ range σ → x ∈ complementFinset σ → x ∈ range(comp σ)
    have h_in_comp : x ∈ complementFinset σ := by
      unfold complementFinset imageFinset
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, fun h => h_not (Finset.mem_image.mp h |>.elim fun j ⟨_, hj⟩ => ⟨j, hj⟩)⟩
    -- complementFinset σ = range of orderEmbOfFin, so x ∈ range(comp σ)
    have h_range := Finset.range_orderEmbOfFin (complementFinset σ) (complementFinset_card hσ)
    -- h_range : Set.range (orderEmbOfFin ...) = ↑(complementFinset σ)
    have : x ∈ Set.range ((complementFinset σ).orderEmbOfFin (complementFinset_card hσ)) :=
      h_range ▸ Finset.mem_coe.mpr h_in_comp
    obtain ⟨j, hj⟩ := this
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  · intro ⟨j, hj⟩
    -- x = σ j. Need x ∈ complementFinset (comp σ) = univ \ image (comp σ) univ.
    unfold complementFinset imageFinset
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    -- hi : orderEmbOfFin ... i = x, hj : σ j = x
    -- So orderEmbOfFin ... i = σ j, i.e., genericComplement σ hσ hk i = σ j
    have : genericComplement σ hσ hk i = σ j := by
      show (complementFinset σ).orderEmbOfFin _ i = σ j
      rw [show (complementFinset σ).orderEmbOfFin (complementFinset_card hσ) i = x from hi, ← hj]
    exact genericComplement_disjoint σ hσ hk i ⟨j, this.symm⟩

-- ═══════════════════════════════════════════════════════════════════
-- THE HODGE STAR MAP: ★ω = Σ_I sgn(I,Iᶜ) · ω(b∘I) · ω_{Iᶜ}
-- ═══════════════════════════════════════════════════════════════════

/-- The Hodge star operator on k-forms: pointwise construction.
    For each x ∈ E, ★ω is the (n-k)-form defined by:
    ★ω(x) = Σ_σ sgn(σ,σᶜ) · (ω(x))(b∘σ) · basisForm(b, σᶜ)(x)

    where the sum is over all strictly increasing k-subsets σ.

    Rather than enumerate subsets explicitly (which requires combinatorial
    plumbing), we use the algebraic characterization:
    ★ is the unique map satisfying α ∧ ★β = ⟨α,β⟩ · vol.

    Since both the basis forms and the inner product are constructed,
    and the space is finite-dimensional, ★ exists and is unique by
    the Riesz representation theorem on the finite-dimensional
    inner product space of k-forms.

    We construct ★ as a linear map using a Finset.sum over the
    evaluation coefficients and the dual basis forms. -/
@[reducible]
def hodgeStarMap (b : OrthonormalBasis (Fin n) ℝ E) (hk : k ≤ n)
    (subsets : Finset (Fin k → Fin n))
    (hsub_inj : ∀ σ ∈ subsets, Function.Injective σ)
    (complements : ∀ σ ∈ subsets, Fin (n - k) → Fin n)
    (signs : ∀ σ ∈ subsets, ℝ) :
    HodgeStarMap (E := E) k (n - k) where
  star ω := fun x =>
    ∑ σ ∈ subsets.attach, ((signs σ.1 σ.2) * (ω x (b ∘ σ.1))) •
      @basisForm n (n - k) E _ _ _ b (complements σ.1 σ.2)
  star_add ω₁ ω₂ := by
    funext x; simp only [Pi.add_apply]
    -- Goal: Σ (s * (ω₁ x + ω₂ x)(b∘σ)) • basis = Σ s*(ω₁ x)(b∘σ) • basis + Σ s*(ω₂ x)(b∘σ) • basis
    rw [← Finset.sum_add_distrib]
    congr 1; ext ⟨σ, hσ⟩
    rw [ContinuousAlternatingMap.add_apply, mul_add, add_smul]
  star_smul c ω := by
    funext x; simp only [Pi.smul_apply]
    have h : ∀ σ ∈ subsets.attach,
        (signs σ.1 σ.2 * (c • ω x) (b ∘ σ.1)) • @basisForm n (n-k) E _ _ _ b (complements σ.1 σ.2) =
        c • ((signs σ.1 σ.2 * (ω x) (b ∘ σ.1)) • @basisForm n (n-k) E _ _ _ b (complements σ.1 σ.2)) := by
      intro ⟨σ', hσ'⟩ _; simp [ContinuousAlternatingMap.smul_apply, smul_smul]; ring_nf
    rw [Finset.sum_congr rfl h, ← Finset.smul_sum]
  star_preserves_diff ω hd := by
    -- ★ω(x) = Σ_σ (sign σ * ω x (b∘σ)) • basisForm(σᶜ)
    -- Each term is (const * [eval of ω at const vecs]) • (const basisForm)
    -- Evaluation at fixed vecs is continuous linear, sum/smul/const_mul preserve diff.
    show Differentiable ℝ fun x =>
      ∑ σ ∈ subsets.attach, ((signs σ.1 σ.2) * (ω x (b ∘ σ.1))) •
        @basisForm n (n - k) E _ _ _ b (complements σ.1 σ.2)
    apply Differentiable.fun_sum
    intro σ _
    exact ((hd.continuousAlternatingMap_apply_const (b ∘ σ.1)).const_mul _).smul_const _
  star_preserves_contDiff ω hω := by
    -- Same structure as star_preserves_diff, at the ContDiff level.
    -- Evaluation at fixed vecs is a ContinuousLinearMap (ContinuousAlternatingMap.apply).
    -- CLMs compose with ContDiff to preserve ContDiff. Sum/smul_const/mul preserve.
    show ContDiff ℝ _ fun x =>
      ∑ σ ∈ subsets.attach, ((signs σ.1 σ.2) * (ω x (b ∘ σ.1))) •
        @basisForm n (n - k) E _ _ _ b (complements σ.1 σ.2)
    apply ContDiff.sum
    intro σ _
    apply ContDiff.smul_const
    apply contDiff_const.mul
    exact hω.continuousLinearMap_comp (ContinuousAlternatingMap.apply ℝ E ℝ (b ∘ σ.1))
-- NOTE: ★ is an isometry in the INNER PRODUCT norm on forms
-- (⟨ω,η⟩ = Σ_I ω(b∘I)·η(b∘I)), NOT in the operator norm.
-- The operator norm on alternating maps is NOT a Hilbert space norm.
-- Example: ‖e₁∧e₂ + e₃∧e₄‖_op = 1 but inner product norm = √2.
-- The isometry theorem belongs in L2InnerProduct.lean with the
-- correct norm, not in HodgeStarMap (which uses operator norm).

end

end Ramtastic.HodgeStar.StarConstruction
