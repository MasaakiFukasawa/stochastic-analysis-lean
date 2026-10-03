import Chapter4MarkovInitialLimit
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma bounded_pointwise_L2_convergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hm : ∀ n,Measurable (f n)) (hg : Measurable g)
    (B : ℝ) (hb : ∀ n w,‖f n w‖≤B) (hgb : ∀ w,‖g w‖≤B)
    (ht : ∀ᵐ w ∂P,Tendsto (fun n => f n w) atTop (𝓝 (g w))) :
    Tendsto (fun n => eLpNorm (fun w => f n w-g w) 2 P) atTop (𝓝 0) := by
  have hi n : MemLp (f n) 2 P := MemLp.of_bound (hm n).aestronglyMeasurable B (ae_of_all _ (hb n))
  have hgi : MemLp g 2 P := MemLp.of_bound hg.aestronglyMeasurable B (ae_of_all _ hgb)
  have hdom n : ∀ᵐ w ∂P,‖‖f n w-g w‖^2‖≤(2*B)^2 := by
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs,abs_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by linarith [hb n w,hgb w])
  have hlim : ∀ᵐ w ∂P,Tendsto (fun n => ‖f n w-g w‖^2) atTop (𝓝 (0:ℝ)) :=
    ht.mono (fun w hw => by simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using (hw.sub_const (g w)).norm.pow 2)
  have hs := tendsto_integral_of_dominated_convergence (μ:=P) (fun _ => (2*B)^2)
    (fun n => ((hm n).sub hg).norm.pow_const 2 |>.aestronglyMeasurable) (integrable_const _) hdom hlim
  simp only [integral_zero] at hs
  have he n := path_eLpNorm_eq_sqrt_moment P (fun w => f n w-g w) ((hi n).sub hgi)
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (Real.continuous_sqrt.continuousAt.tendsto.comp hs)
  simpa only [Real.sqrt_zero,ENNReal.ofReal_zero,Function.comp_def,Pi.sub_apply] using hh

/-- Conditional identities survive an L2 limit on the left and a bounded
pointwise limit on the right, without choosing a subsequence. -/
theorem conditional_L2_bounded_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G≤m)
    (f g : ℕ → Ω → ℝ) (f₀ g₀ : Ω → ℝ)
    (hf : ∀ n,MemLp (f n) 2 P) (hf₀ : MemLp f₀ 2 P)
    (hg : ∀ n,Measurable[m] (g n)) (hg₀ : Measurable[m] g₀)
    (B : ℝ) (hb : ∀ n w,‖g n w‖≤B) (hb₀ : ∀ w,‖g₀ w‖≤B)
    (htf : Tendsto (fun n => eLpNorm (fun w => f n w-f₀ w) 2 P) atTop (𝓝 0))
    (htg : ∀ᵐ w ∂P,Tendsto (fun n => g n w) atTop (𝓝 (g₀ w)))
    (he : ∀ n,P[f n | G]=ᵐ[P] g n) : P[f₀ | G]=ᵐ[P] g₀ := by
  letI : MeasurableSpace Ω := m
  exact (Asakura.FullAudit.conditional_l2_limit_identity P hG g f g₀ f₀
    (fun n => MemLp.of_bound (hg n).aestronglyMeasurable B (ae_of_all _ (hb n))) hf
    (MemLp.of_bound hg₀.aestronglyMeasurable B (ae_of_all _ hb₀)) hf₀
    (fun n => (he n).symm)
    (bounded_pointwise_L2_convergence P g g₀ hg hg₀ B hb hb₀ htg) htf).symm

end Asakura.Chapter4
