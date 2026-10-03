import Chapter7BrownianClockMean
import Chapter7ClockVarianceScale
import Chapter7CenteredIntegralScale

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma brownian_cell_clock_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n) :
    (∫ w,(brownianCellClock B u T t n w-(∫ v,brownianCellClock B u T t n v ∂P))^2 ∂P)
      ≤ 32*(∑ j,u j^2)^2/n := by
  let h := T/(n:ℝ)
  let ell := clockCellLength T t n
  let U := fun (k : Fin (n+1)) w => ∫ r in 0..ell k,
      (∑ j,u j*(B.W j (realTimeClamp ((k:ℝ)*h+r)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))^2
  have hh : 0 ≤ h := div_nonneg hT.le (Nat.cast_nonneg _)
  have hl := clock_cell_length_bounds T t n hT ht0 htT hn
  have hm := brownian_block_grid_mean P B u u (fun k : Fin (n+1) => (k:ℝ)*h)
    ell (fun k => mul_nonneg (by positivity) hh) (fun k => (hl k).1)
  have hs : (∑ j,u j*u j)=(∑ j,u j^2) := by simp only [pow_two]
  have hb := brownian_block_grid_variance P B u u h hh ell (fun k => (hl k).1) (fun k => (hl k).2)
  have hmean k : (∫ w,U k w ∂P)=(ell k)^2*(∑ j,u j^2)/2 := by
    simpa only [U,← pow_two,hs] using
      (shifted_brownian_block_moments P B u u ((k:ℝ)*h) (ell k) (mul_nonneg (by positivity) hh) (hl k).1).2.1
  have hi k : Integrable (U k) P := by
    have hk := (shifted_brownian_block_moments P B u u ((k:ℝ)*h) (ell k) (mul_nonneg (by positivity) hh) (hl k).1).1
    simpa only [U,← pow_two] using hk.integrable (by norm_num)
  have he w : (∑ k,U k w)-(∫ v,∑ k,U k v ∂P)=∑ k,(U k w-(ell k)^2*(∑ j,u j^2)/2) := by
    rw [integral_finsetSum _ (fun k _ => hi k),Finset.sum_sub_distrib]
    simp only [hmean]
  change (∫ w,((4*(n:ℝ)/T^2)*(∑ k,U k w)-
    (∫ v,(4*(n:ℝ)/T^2)*(∑ k,U k v) ∂P))^2 ∂P) ≤ _
  rw [centered_integral_scale]
  simp_rw [he]
  have hb' : (∫ w,(∑ k,(U k w-(ell k)^2*(∑ j,u j^2)/2))^2 ∂P) ≤
      ((n+1:ℕ):ℝ)*h^4*(∑ j,u j^2)^2 := by
    have he' : ((n+1:ℕ):ℝ)*h^4*((∑ j,u j^2)^2+2*(∑ j,u j^2)^2)/3=
        ((n+1:ℕ):ℝ)*h^4*(∑ j,u j^2)^2 := by ring
    simpa only [U,← pow_two,hs,he'] using hb
  calc
    _ ≤ (4*(n:ℝ)/T^2)^2*(((n+1:ℕ):ℝ)*h^4*(∑ j,u j^2)^2) :=
      mul_le_mul_of_nonneg_left hb' (sq_nonneg _)
    _ ≤ _ := by simpa only [h,mul_assoc] using clock_variance_scale n hn T (∑ j,u j^2) hT

end Asakura.Chapter7
