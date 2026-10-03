import Chapter12DominatedLpLimit
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

noncomputable def smoothIntervalIndicator (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((n+1:ℕ)*(x-a))*Real.smoothTransition ((n+1:ℕ)*(b-x))

theorem smooth_interval_bounds (a b : ℝ) (n : ℕ) (x : ℝ) :
    0≤smoothIntervalIndicator a b n x ∧ smoothIntervalIndicator a b n x≤1 := by
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul 1)⟩

theorem smooth_interval_zero (a b : ℝ) (n : ℕ) (x : ℝ) (hx : x∉Ioo a b) :
    smoothIntervalIndicator a b n x=0 := by
  have hn : (0:ℝ)≤(n+1:ℕ) := by positivity
  by_cases ha : a<x
  · have hb : b≤x := le_of_not_gt (fun hb => hx ⟨ha,hb⟩)
    simp only [smoothIntervalIndicator,Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.mpr hb)),mul_zero]
  · simp only [smoothIntervalIndicator,Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.mpr (le_of_not_gt ha))),zero_mul]

theorem smooth_interval_contDiff (a b : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (smoothIntervalIndicator a b n) := by
  unfold smoothIntervalIndicator
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem smooth_interval_compact (a b : ℝ) (n : ℕ) :
    HasCompactSupport (smoothIntervalIndicator a b n) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc a b))
  intro x hx
  by_contra hn
  have ho : x∉Ioo a b := fun h => hn ⟨h.1.le,h.2.le⟩
  exact hx (smooth_interval_zero a b n x ho)

theorem smooth_interval_indicator_limit (a b x : ℝ) :
    Tendsto (fun n => smoothIntervalIndicator a b n x) atTop
      (𝓝 ((Ioo a b).indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : x∈Ioo a b
  · rw [indicator_of_mem hx]
    have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
    have hl := (hn.atTop_mul_const (sub_pos.mpr hx.1)).eventually (eventually_ge_atTop (1:ℝ))
    have hr := (hn.atTop_mul_const (sub_pos.mpr hx.2)).eventually (eventually_ge_atTop (1:ℝ))
    apply tendsto_const_nhds.congr'
    filter_upwards [hl,hr] with n h1 h2
    simp only [smoothIntervalIndicator,Real.smoothTransition.one_of_one_le h1,
      Real.smoothTransition.one_of_one_le h2,one_mul]
  · rw [indicator_of_notMem hx]
    have he : (fun n => smoothIntervalIndicator a b n x)=fun _ => (0:ℝ) :=
      funext (fun n => smooth_interval_zero a b n x hx)
    rw [he]
    exact tendsto_const_nhds

end Asakura.Chapter12
