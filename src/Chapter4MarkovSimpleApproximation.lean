import Chapter4MarkovInitialLimit
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Finite-valued approximations retain the initial information and converge
in mean square under the ambient probability measure. -/
theorem initial_simple_approximation_L2
    {Ω : Type*} {m : MeasurableSpace Ω} {dim : ℕ}
    (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G≤m)
    (η : Ω → Fin dim → ℝ) (hη : Measurable[G] η) (hi : MemLp η 2 P) :
    ∃ a : ℕ → @SimpleFunc Ω G (Fin dim → ℝ),
      (∀ n,MemLp (fun w => a n w) 2 P) ∧
      Tendsto (fun n => ∫ w,‖a n w-η w‖^2 ∂P) atTop (𝓝 0) := by
  letI : MeasurableSpace Ω := m
  let a : ℕ → @SimpleFunc Ω G (Fin dim → ℝ) := by
    letI : MeasurableSpace Ω := G
    exact SimpleFunc.approxOn η hη univ 0 (mem_univ 0)
  have hma n : Measurable[G] (fun w => a n w) := by
    letI : MeasurableSpace Ω := G
    exact (a n).measurable
  have hm n : Measurable[m] (fun w => a n w) := (hma n).mono hG le_rfl
  have hb n w : ‖a n w‖≤2*‖η w‖ := by
    letI : MeasurableSpace Ω := G
    simpa only [a,two_mul] using SimpleFunc.norm_approxOn_zero_le hη (mem_univ (0:Fin dim → ℝ)) w n
  have hai n : MemLp (fun w => a n w) 2 P := hi.of_le_mul (c:=2) (hm n).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb n))
  refine ⟨a,hai,?_⟩
  have hηm : Measurable[m] η := hη.mono hG le_rfl
  have hdom : Integrable (fun w => 9*‖η w‖^2) P := (hi.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul 9
  have hbound n : ∀ᵐ w ∂P,‖‖a n w-η w‖^2‖≤9*‖η w‖^2 := by
    apply Filter.Eventually.of_forall
    intro w
    have hh := norm_sub_le (a n w) (η w)
    have hd : ‖a n w-η w‖≤3*‖η w‖ := by linarith only [hh,hb n w]
    rw [Real.norm_eq_abs,abs_sq]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith only [hs]
  have hlim : ∀ᵐ w ∂P,Tendsto (fun n => ‖a n w-η w‖^2) atTop (𝓝 (0:ℝ)) := by
    apply Filter.Eventually.of_forall
    intro w
    letI : MeasurableSpace Ω := G
    have hh := SimpleFunc.tendsto_approxOn hη (mem_univ (0:Fin dim → ℝ)) (x:=w) (by simp)
    simpa only [a,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using (hh.sub_const (η w)).norm.pow 2
  have ht := tendsto_integral_of_dominated_convergence (μ:=P) (fun w => 9*‖η w‖^2)
    (fun n => ((hm n).sub hηm).norm.pow_const 2 |>.aestronglyMeasurable) hdom hbound hlim
  simpa only [integral_zero,Pi.sub_apply] using ht

end Asakura.Chapter4
