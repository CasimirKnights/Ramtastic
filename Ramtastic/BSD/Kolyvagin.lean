/-
  Kolyvagin.lean - Kolyvagin and Gross-Zagier-Kolyvagin vocabulary.

  Published results that close BSD for rank 0 and rank 1:

  1. Kolyvagin (1988): L(E,1) ≠ 0 → rank = 0 AND Sha finite.
     Contrapositive: rank ≥ 1 → L(E,1) = 0 → analytic_rank ≥ 1.

  2. Gross-Zagier (1986): if L'(E,1) ≠ 0 then the Heegner point
     has positive height → rank ≥ 1.

  3. Combined (Gross-Zagier-Kolyvagin): analytic_rank ≤ 1 → rank = analytic_rank.

  This Tower-side file records the classical rank-at-most-one comparison
  package used by public BSD statement surfaces.
-/

import Mathlib.Tactic
import Ramtastic.BSD.BSDFormula

namespace Ramtastic.BSD.Kolyvagin

open Ramtastic.BSD.BSDFormula
open Ramtastic.BSD.MordellWeil
open Ramtastic.BSD.LFunction

noncomputable section

/-- **Kolyvagin-Gross-Zagier data.**
    An elliptic curve with the published rank ≤ 1 results. -/
structure KGZData where
  mw : MordellWeilGroup
  ar : AnalyticRank
  /-- **Kolyvagin (1988).** analytic_rank = 0 → rank = 0.
      Published: "Finiteness of E(ℚ) and Sha(E/ℚ) for a subclass
      of Weil curves." Izvestiya 1988. -/
  kolyvagin_rank0 : ar.analytic_rank = 0 → mw.rank = 0
  /-- **Kolyvagin (1988), contrapositive.** rank ≥ 1 → analytic_rank ≥ 1.
      Equivalently: rank ≠ 0 → analytic_rank ≠ 0. -/
  kolyvagin_contra : mw.rank ≠ 0 → ar.analytic_rank ≠ 0
  /-- **Gross-Zagier (1986) + Kolyvagin (1988).**
      analytic_rank = 1 → rank = 1.
      Published: Gross-Zagier, "Heegner points and derivatives of
      L-series," Inventiones 1986. Combined with Kolyvagin's Euler
      system to get rank ≤ 1. -/
  gross_zagier : ar.analytic_rank = 1 → mw.rank = 1

/-- BSD rank equality in the analytic-rank-zero package. -/
theorem bsd_analytic_rank_0 (data : KGZData) (h : data.ar.analytic_rank = 0) :
    data.mw.rank = data.ar.analytic_rank := by
  rw [h, data.kolyvagin_rank0 h]

/-- BSD rank equality in the analytic-rank-one package. -/
theorem bsd_analytic_rank_1 (data : KGZData) (h : data.ar.analytic_rank = 1) :
    data.mw.rank = data.ar.analytic_rank := by
  rw [h, data.gross_zagier h]

/-- BSD rank equality in the analytic-rank-at-most-one package. -/
theorem bsd_analytic_rank_le_1 (data : KGZData) (h : data.ar.analytic_rank ≤ 1) :
    data.mw.rank = data.ar.analytic_rank := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · exact bsd_analytic_rank_0 data h0
  · exact bsd_analytic_rank_1 data h1

end

end Ramtastic.BSD.Kolyvagin
