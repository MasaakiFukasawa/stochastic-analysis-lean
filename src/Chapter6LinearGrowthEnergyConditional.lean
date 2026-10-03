import Chapter6BrownianGrowthEnergyGrid
import Chapter6BrownianPathEnvelope
import Chapter6UniformRiemannL1
import Chapter6ConditionalBoundLimit

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

theorem linear_growth_energy_conditional_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H : Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ j t,Measurable[B.F t] (H j t)) (hHc : ∀ j w,Continuous (fun t => H j t w))
    (R : ℝ) (hR : 0<R) (b : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (hb : ∀ r,Measurable (b r)) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ r y,‖WithLp.toLp 2 (b r y)‖≤K*(1+‖WithLp.toLp 2 y‖))
    (hrep : ∀ j w r,r∈Icc 0 R → H j (realTimeClamp r) w=b r (fun i => B.W i (realTimeClamp r) w) j) :
    let V := fun w i => B.W i (realTimeClamp R) w
    let Z := fun w => ∫ r in 0..R,∑ j,(H j (realTimeClamp r) w)^2
    Integrable Z P ∧ ∀ᵐ w ∂P,|P[Z|MeasurableSpace.comap V inferInstance] w|≤
      R*(2*K^2*(3+2*(d:ℝ)*R))*(1+‖WithLp.toLp 2 (V w)‖^2) := by
  let V := fun w i => B.W i (realTimeClamp R) w
  let J := fun z : Ω × ℝ => ∑ j,(H j (realTimeClamp z.2) z.1)^2
  let Z := fun w => ∫ r in 0..R,J (w,r)
  obtain ⟨U,hUi,hU0,hUb⟩ := brownian_path_L2_envelope P B R hR.le
  let A := fun w => K*(1+U w)
  have hAi : MemLp A 2 P := ((memLp_const (1:ℝ)).add hUi).const_mul K
  have hA0 w : 0≤A w := mul_nonneg hK (add_nonneg zero_le_one (hU0 w))
  have hHbj j w r (hr : r∈Icc 0 R) : |H j (realTimeClamp r) w|≤A w := by
    rw [hrep j w r hr]
    apply ((PiLp.norm_apply_le (WithLp.toLp 2 (b r (fun i => B.W i (realTimeClamp r) w))) j).trans (hbb _ _)).trans
    exact mul_le_mul_of_nonneg_left (by linarith [hUb w r hr]) hK
  let F := fun w => (d:ℝ)*(A w)^2
  have hFi : Integrable F P := by
    simpa only [F,Real.norm_eq_abs,sq_abs] using (hAi.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul (d:ℝ)
  have hJc w : Continuous (fun r => J (w,r)) := continuous_finsetSum _ (fun j _ => ((hHc j w).comp real_time_clamp_continuous).pow 2)
  have hJm : Measurable J := by
    have hm r : Measurable (fun w => J (w,r)) := Finset.measurable_sum _ (fun j _ => (((hHa j (realTimeClamp r)).mono (B.le _) le_rfl)).pow_const 2)
    simpa only [Function.comp_def,Function.uncurry_def,Prod.swap] using (measurable_uncurry_of_continuous_of_measurable hJc hm).comp measurable_swap
  have hJb w r (hr : r∈Icc 0 R) : |J (w,r)|≤F w := by
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => sq_nonneg _))]
    calc
      _ ≤ ∑ _j : Fin d,(A w)^2 := sum_le_sum (fun j _ => sq_le_sq.mpr (by simpa only [abs_of_nonneg (hA0 w)] using hHbj j w r hr))
      _ = _ := by simp [F]
  let h := fun n : ℕ => R/((n:ℝ)+1)
  have hh n : 0<h n := div_pos hR (by positivity)
  have hend n : ((n+1:ℕ):ℝ)*h n=R := by dsimp [h]; push_cast; field_simp
  let S := fun n w => ∑ k∈range (n+1),h n*J (w,(k:ℝ)*h n)
  have hl := uniform_riemann_L1_limit P R hR J hJm (fun w => (hJc w).continuousOn) F hFi hJb
  have heS n w : S n w=∑ k∈range (n+1),h n*∑ j,(b ((k:ℝ)*h n) (fun i => B.W i (realTimeClamp ((k:ℝ)*h n)) w) j)^2 := by
    apply sum_congr rfl
    intro k hk
    have hr : (k:ℝ)*h n∈Icc 0 R := by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) (hh n).le,?_⟩
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mem_range.mp hk).le) (hh n).le).trans_eq (hend n)
    congr 1
    exact sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (hrep j w _ hr))
  have hg n := brownian_growth_energy_grid_bound (n := n+1) P B (h n) (hh n)
    (fun k => b ((k:ℝ)*h n)) (fun k => hb _) K hK (fun k => hbb _)
  have hSi n : Integrable (S n) P := by rw [funext (heS n)]; exact (hg n).1
  have hSb n : ∀ᵐ w ∂P,|P[S n|MeasurableSpace.comap V inferInstance] w|≤R*(2*K^2*(3+2*(d:ℝ)*R))*(1+‖WithLp.toLp 2 (V w)‖^2) := by
    have ht := (hg n).2
    rw [hend n,←funext (heS n)] at ht
    exact ht
  have hZi : Integrable Z P := by
    have hFp : Integrable (fun z : Ω × ℝ => F z.1) (P.prod (volume.restrict (Ioc 0 R))) :=
      ((memLp_one_iff_integrable.mpr hFi).comp_fst _).integrable le_rfl
    have hi : Integrable J (P.prod (volume.restrict (Ioc 0 R))) := hFp.mono' hJm.aestronglyMeasurable (by
      have hgood : ∀ᵐ z ∂P.prod (volume.restrict (Ioc (0:ℝ) R)),z.2∈Ioc (0:ℝ) R := by
        apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2
        exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hgood] with z hz
      exact hJb z.1 z.2 ⟨hz.1.le,hz.2⟩)
    simpa only [Z,intervalIntegral.integral_of_le hR.le] using hi.integral_prod_left
  have hgauss := (brownian_grid_samples_gaussian (n := 1) P B R hR.le
    (fun _ : Fin d => 1) (fun _ => le_rfl) id).1
  have hVg : HasGaussianLaw V P := by simpa only [Nat.cast_one,one_mul,id_eq] using hgauss
  have hVe : HasGaussianLaw (fun w => WithLp.toLp 2 (V w)) P := hVg.map_equiv (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hBi : Integrable (fun w => R*(2*K^2*(3+2*(d:ℝ)*R))*(1+‖WithLp.toLp 2 (V w)‖^2)) P :=
    ((integrable_const (1:ℝ)).add (hVe.memLp_two.integrable_norm_pow (by norm_num : (2:ℕ)≠0))).const_mul _
  exact ⟨hZi,conditional_bound_L1_limit P (MeasurableSpace.comap V inferInstance) S Z _ hSi hZi hBi hSb hl⟩

end Asakura.Chapter6
