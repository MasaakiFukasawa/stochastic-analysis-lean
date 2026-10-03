import FullAuditSquareSubsequence
import Mathlib.Topology.Algebra.Order.Floor

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def timeAverage (f : ℝ → ℝ) (t : ℝ) := t⁻¹*(∫ u in (0:ℝ)..t,f u)

/-- Control the unfinished interval between two averaging times. -/
theorem time_average_difference_bound (f : ℝ → ℝ) (hf : Continuous f)
    (K s t : ℝ) (hK : 0 ≤ K) (hb : ∀ u, |f u| ≤ K) (hs : 0 < s) (hst : s ≤ t) :
    |timeAverage f t-timeAverage f s| ≤ 2*K*(t-s)/s := by
  have ht : 0 < t := hs.trans_le hst
  let A := ∫ u in (0:ℝ)..s,f u
  let B := ∫ u in s..t,f u
  have ha : |A| ≤ K*s := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := (0:ℝ)) (b := s) (fun u _ => by simpa only [Real.norm_eq_abs] using hb u)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos hs] using h
  have hbB : |B| ≤ K*(t-s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := s) (b := t) (fun u _ => by simpa only [Real.norm_eq_abs] using hb u)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using h
  have hsplit : (∫ u in (0:ℝ)..t,f u) = A+B :=
    (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 s) (hf.intervalIntegrable s t)).symm
  have he : timeAverage f t-timeAverage f s = (t⁻¹-s⁻¹)*A+t⁻¹*B := by
    rw [timeAverage,timeAverage,hsplit]
    dsimp only [A,B]
    ring
  have hi : t⁻¹ ≤ s⁻¹ := inv_anti₀ hs hst
  rw [he]
  calc
    _ ≤ |(t⁻¹-s⁻¹)*A|+|t⁻¹*B| := abs_add_le _ _
    _ = (s⁻¹-t⁻¹)*|A|+t⁻¹*|B| := by
      rw [abs_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hi),neg_sub,abs_of_pos (inv_pos.mpr ht)]
    _ ≤ (s⁻¹-t⁻¹)*(K*s)+t⁻¹*(K*(t-s)) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hi))
        (mul_le_mul_of_nonneg_left hbB (inv_nonneg.mpr ht.le))
    _ = 2*K*(t-s)/t := by field_simp; ring
    _ ≤ 2*K*(t-s)/s := div_le_div_of_nonneg_left (by positivity) hs hst

noncomputable def squareTimeIndex (t : ℝ) : ℕ := ⌊Real.sqrt t⌋₊

theorem square_time_index_bounds (t : ℝ) (ht : 0 ≤ t) :
    ((squareTimeIndex t:ℕ):ℝ)^2 ≤ t ∧ t < (((squareTimeIndex t:ℕ):ℝ)+1)^2 := by
  have hlo := Nat.floor_le (Real.sqrt_nonneg t)
  have hhi := Nat.lt_floor_add_one (Real.sqrt t)
  have hs := Real.sq_sqrt ht
  constructor
  · have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hlo 2
    simpa only [hs,squareTimeIndex] using h
  · have h := (sq_lt_sq₀ (Real.sqrt_nonneg t) (by positivity : 0 ≤ (⌊Real.sqrt t⌋₊:ℝ)+1)).mpr hhi
    simpa only [hs,squareTimeIndex] using h

theorem square_time_index_tendsto : Tendsto squareTimeIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop ((n:ℝ)^2)] with t ht
  have ht0 : 0 ≤ t := (sq_nonneg _).trans ht
  apply Nat.le_floor
  exact (Real.le_sqrt (Nat.cast_nonneg _) ht0).mpr ht

/-- Extension from square times to every real time, using the exact gap
 (n+1)^2-n^2 and the bound 2K(2n+1)/n^2. -/
theorem time_average_square_extension (f : ℝ → ℝ) (hf : Continuous f)
    (K l : ℝ) (hK : 0 ≤ K) (hb : ∀ u, |f u| ≤ K)
    (hseq : Tendsto (fun n : ℕ => timeAverage f ((n:ℝ)^2)) atTop (nhds l)) :
    Tendsto (timeAverage f) atTop (nhds l) := by
  let N := squareTimeIndex
  have hN : Tendsto (fun t : ℝ => (N t:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp square_time_index_tendsto
  have hsmall : Tendsto (fun t : ℝ => 6*K/(N t:ℝ)) atTop (nhds 0) := tendsto_const_nhds.div_atTop hN
  have hbound : ∀ᶠ t in atTop, |timeAverage f t-timeAverage f ((N t:ℝ)^2)| ≤ 6*K/(N t:ℝ) := by
    filter_upwards [eventually_ge_atTop (0:ℝ),square_time_index_tendsto.eventually (eventually_ge_atTop 1)] with t ht hn
    have hn1 : (1:ℝ) ≤ (N t:ℝ) := by exact_mod_cast hn
    have hnp : 0 < (N t:ℝ) := lt_of_lt_of_le (by norm_num) hn1
    have hg := square_time_index_bounds t ht
    calc
      _ ≤ 2*K*(t-(N t:ℝ)^2)/(N t:ℝ)^2 := time_average_difference_bound f hf K _ t hK hb (sq_pos_of_pos hnp) hg.1
      _ ≤ 2*K*(2*(N t:ℝ)+1)/(N t:ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*K)
        nlinarith [hg.2]
      _ ≤ 6*K/(N t:ℝ) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hnp) hnp).mpr
        nlinarith [mul_nonneg (mul_nonneg hK hnp.le) (sub_nonneg.mpr hn1)]
  have hzero : Tendsto (fun t => timeAverage f t-timeAverage f ((N t:ℝ)^2)) atTop (nhds 0) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound) hsmall
  have h := (hseq.comp square_time_index_tendsto).add hzero
  simpa only [N,Function.comp_def,add_sub_cancel,add_zero,add_sub_cancel_left] using h

end Asakura.FullAudit
