import Mathlib.Tactic
import Ramtastic.BSD.EllipticCurve
import Ramtastic.BSD.LFunction
import Ramtastic.BSD.MordellWeil
import Ramtastic.BSD.HeightPairing
import Ramtastic.BSD.TateShafarevich

/-!
BSD arithmetic comparison meta-theory.

This is Tower-side reference vocabulary for Weierstrass arithmetic data, local
Neron/Tamagawa data, Hasse-Weil readouts, and Mordell-Weil/height data.
-/

namespace Ramtastic.BSD.ArithmeticGAGA

open Ramtastic.BSD.EllipticCurve
open Ramtastic.BSD.LFunction
open Ramtastic.BSD.MordellWeil
open Ramtastic.BSD.HeightPairing
open Ramtastic.BSD.TateShafarevich

noncomputable section

/-- Algebraic curve data and analytic L-function data are the same curve. -/
structure AlgebraicAnalyticCurveComparison where
  arithmetic : ArithmeticECData
  analytic : AnalyticRank
  same_weierstrass_a : analytic.a = arithmetic.a
  same_weierstrass_b : analytic.b = arithmetic.b
  same_conductor : analytic.conductor = arithmetic.conductor
  same_local_data : forall p : Nat, analytic.local_data p = arithmetic.local_data p

/-- Local Neron model comparison at every prime. -/
structure NeronModelLocalComparison
    (C : AlgebraicAnalyticCurveComparison) where
  componentGroupOrder : Nat -> Nat
  frobeniusTrace : Nat -> Int
  localFactorTrace : Nat -> Int
  component_group_matches_tamagawa :
    forall p : Nat, componentGroupOrder p = (C.arithmetic.local_data p).tamagawa
  frobenius_matches_arithmetic :
    forall p : Nat, frobeniusTrace p = (C.arithmetic.local_data p).trace_frobenius
  local_factor_trace_matches_frobenius :
    forall p : Nat, Nat.Prime p -> localFactorTrace p = frobeniusTrace p
  good_reduction_component_trivial :
    forall p : Nat,
      (C.arithmetic.local_data p).reduction = ReductionType.good ->
        componentGroupOrder p = 1

/-- Hasse-Weil readout comparison: local Euler factors assemble the L-function. -/
structure HasseWeilReadoutComparison
    (C : AlgebraicAnalyticCurveComparison)
    (N : NeronModelLocalComparison C) where
  eulerCoefficient : Nat -> Int
  completedCentralCoefficient : Nat -> Real
  euler_coefficients_are_frobenius :
    forall p : Nat, Nat.Prime p -> eulerCoefficient p = N.frobeniusTrace p
  analytic_rank_is_first_nonzero_completed_coefficient :
    (forall n : Nat, n < C.analytic.analytic_rank ->
      completedCentralCoefficient n = 0) /\
    completedCentralCoefficient C.analytic.analytic_rank ≠ 0
  completed_coefficients_match_lfunction :
    forall n : Nat,
      completedCentralCoefficient n =
        iteratedDeriv n C.analytic.L 1 / (Nat.factorial n : Real)

/-- Mordell-Weil and height comparison against the arithmetic curve. -/
structure MordellWeilHeightComparison
    (_C : AlgebraicAnalyticCurveComparison) where
  mw : MordellWeilGroup
  regulator : Regulator mw
  basisRank : Nat
  basis_rank_matches_mw : basisRank = mw.rank
  free_generators_independent :
    forall coeffs : Fin mw.rank -> Int,
      Finset.univ.sum (fun i => coeffs i • mw.free_generators i) = 0 ->
        forall i, coeffs i = 0
  free_generators_span :
    forall P : mw.Point, exists coeffs : Fin mw.rank -> Int, exists t : mw.Point,
      (exists n : Nat, 0 < n /\ (n : Int) • t = 0) /\
      P = Finset.univ.sum (fun i => coeffs i • mw.free_generators i) + t
  height_detects_torsion :
    forall P : mw.Point, regulator.height P = 0 <->
      exists n : Nat, 0 < n /\ (n : Int) • P = 0
  regulator_positive_for_positive_rank :
    0 < mw.rank -> 0 < regulator.regulator

/-- Full Tower-side arithmetic comparison package. -/
structure BSDArithmeticGAGAComparison where
  curve : AlgebraicAnalyticCurveComparison
  neron : NeronModelLocalComparison curve
  hasseWeil : HasseWeilReadoutComparison curve neron
  mordellWeil : MordellWeilHeightComparison curve

end

end Ramtastic.BSD.ArithmeticGAGA
