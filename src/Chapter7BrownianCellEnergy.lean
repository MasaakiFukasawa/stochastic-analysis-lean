import Chapter7CellIntegralRestriction
import Chapter7ClockCellTruncation
import Chapter7CellDisjointSquare
import Chapter7BrownianClockMean

open MeasureTheory Set Finset
open scoped BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma brownian_cell_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s h t : ℝ) (hs : 0≤s) (hh : 0≤h) (ht : 0≤t) (w : Ω) :
    (∫ r in 0..t,(brownianCellIntegrand B u s (s+h) (w,r))^2)=
      ∫ r in 0..max 0 (min h (t-s)),
        (∑ j,u j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))^2 := by
  have he r : (brownianCellIntegrand B u s (s+h) (w,r))^2=
      (Ioc s (s+h)).indicator (fun r => (∑ j,u j*(B.W j (realTimeClamp r) w-B.W j (realTimeClamp s) w))^2) r := by
    by_cases hr : r∈Ioc s (s+h)
    · have hr0 : 0≤r := hs.trans hr.1.le
      simp only [brownianCellIntegrand,indicator_of_mem hr,max_eq_right hr0,min_eq_left hr.1.le]
    · simp only [brownianCellIntegrand,indicator_of_notMem hr,zero_pow (by decide : (2:ℕ)≠0)]
  simp_rw [he]
  exact cell_integral_restriction _ s h t hs hh ht

lemma brownian_grid_energy_clock {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n) (w : Ω) :
    (4*(n:ℝ)/T^2)*(∫ r in 0..t,(brownianGridIntegrand B u (T/n) (n+1) (w,r))^2)=
      brownianCellClock B u T t n w := by
  have hh : 0≤T/(n:ℝ) := div_nonneg hT.le (Nat.cast_nonneg _)
  simp_rw [brownian_grid_square B u (T/n) hh (n+1)]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun (k : Fin (n+1)) _ =>
    (brownian_cell_integrand_regular P B u ((k:ℝ)*(T/n)) (((k:ℝ)+1)*(T/n))
      (mul_nonneg (by positivity) hh)).2.2 t ht0 w)]
  change _=(4*(n:ℝ)/T^2)*_
  congr 1
  apply sum_congr rfl
  intro k _
  have he : ((k:ℝ)+1)*(T/n)=(k:ℝ)*(T/n)+T/n := by ring
  rw [he,brownian_cell_energy B u _ _ _ (mul_nonneg (by positivity) hh) hh ht0,
    ← clock_cell_truncation T t n hT ht0 htT hn k]

end Asakura.Chapter7
