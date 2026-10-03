import Chapter8TimeAverageCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The time-average estimate from stationarity, the conditional Markov
identity and synchronous contraction. The covariance and moment estimates
are conclusions rather than assumed hypotheses. -/
theorem stationary_markov_time_average {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (π : Measure E) [IsProbabilityMeasure π] (hπ : MemLp (fun x : E => x) 2 π)
    (Y : ℝ → Ω → E) (hmY : Measurable (fun p : Ω × ℝ => Y p.2 p.1))
    (hcY : ∀ ω, Continuous (fun t => Y t ω)) (hlaw : ∀ t, P.map (Y t) = π)
    (G : ℝ → MeasurableSpace Ω) (hG : ∀ t, G t ≤ m)
    (hYG : ∀ t, AEStronglyMeasurable[G t] (Y t) P)
    (X : ℝ → E → Ω → E) (hX : ∀ t ≥ 0, ∀ x, MemLp (X t x) 2 P)
    (κ T : ℝ) (hκ : 0 < κ) (hT : 0 < T)
    (hLip : ∀ t ≥ 0, ∀ x y, ∀ᵐ ω ∂P,
      ‖X t x ω-X t y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖)
    (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (hCE : ∀ s ≥ 0, ∀ t, s ≤ t →
      P[(fun ω => f (Y t ω))|G s] =ᵐ[P] fun ω => ∫ η,f (X (t-s) (Y s ω) η) ∂P) :
    (∫ ω, (timeAverage (fun t => f (Y t ω)) T-(∫ x,f x ∂π))^2 ∂P) ≤
      2*(L:ℝ)^2*(∫ x, ‖x‖^2 ∂π)/(κ*T) := by
  let a := ∫ x,f x ∂π
  let Z := fun ω t => f (Y t ω)-a
  have hm (t : ℝ) : Measurable (Y t) := hmY.comp (measurable_id.prodMk measurable_const)
  have hfπ := lipschitz_observable_memLp π (fun x => x) hπ f L hf
  have hfY (t : ℝ) : MemLp (fun ω => f (Y t ω)) 2 P := by
    apply MemLp.comp_of_map (f := Y t) _ (hm t).aemeasurable
    rwa [hlaw]
  have hmeanY (t : ℝ) : (∫ ω,f (Y t ω) ∂P) = a := by
    rw [← integral_map (hm t).aemeasurable hf.continuous.aestronglyMeasurable,hlaw]
  have hZ (t : ℝ) : MemLp (fun ω => Z ω t) 2 P := (hfY t).sub (memLp_const a)
  have hmean (t : ℝ) : (∫ ω,Z ω t ∂P) = 0 := by
    dsimp only [Z]
    rw [integral_sub ((hfY t).integrable (by norm_num)) (integrable_const _),hmeanY]
    simp
  have hsecond (t : ℝ) : (∫ ω,(Z ω t)^2 ∂P) ≤ (L:ℝ)^2*(∫ x,‖x‖^2 ∂π) := by
    have hv := lipschitz_variance_bound π hπ f L hf hfπ
    have he : (∫ ω,(Z ω t)^2 ∂P) = Var[f;π] := by
      rw [variance_eq_integral hfπ.aemeasurable]
      dsimp only [Z,a]
      have hh := integral_map (μ := P) (φ := Y t)
        (f := fun x => (f x-(∫ y,f y ∂π))^2) (hm t).aemeasurable
        ((hf.continuous.sub continuous_const).pow 2).aestronglyMeasurable
      rw [hlaw] at hh
      exact hh.symm
    rw [he]
    exact hv.trans (mul_le_mul_of_nonneg_left (centered_second_moment_le π hπ) (sq_nonneg _))
  have hc (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      |cov[fun ω => Z ω s,fun ω => Z ω t;P]| ≤
        (L:ℝ)^2*(∫ x,‖x‖^2 ∂π)*Real.exp (-κ*(t-s)) := by
    dsimp only [Z]
    rw [covariance_sub_const_left ((hfY s).integrable (by norm_num)),
      covariance_sub_const_right ((hfY t).integrable (by norm_num))]
    exact markov_stationary_covariance P (hG s) π hπ (Y s) (Y t) (hm s) (hm t)
      (hlaw s) (hlaw t) (hYG s) (X (t-s)) (hX _ (sub_nonneg.mpr hst)) f L hf κ (t-s)
      (hLip _ (sub_nonneg.mpr hst)) (hCE s hs t hst)
  have hcov (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (ht : 0 ≤ t) :
      |cov[fun ω => Z ω s,fun ω => Z ω t;P]| ≤
        (L:ℝ)^2*(∫ x,‖x‖^2 ∂π)*Real.exp (-κ*|t-s|) := by
    rcases le_total s t with hst|hts
    · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hc s t hs hst
    · rw [covariance_comm]
      simpa [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using hc t s ht hts
  have hh := time_average_from_covariance_bound P Z
    ((hf.continuous.measurable.comp hmY).sub measurable_const)
    (fun ω => (hf.continuous.comp (hcY ω)).sub continuous_const) hZ hmean
    ((L:ℝ)^2*(∫ x,‖x‖^2 ∂π)) κ T (by positivity) hκ hT hsecond hcov
  have he (ω : Ω) : timeAverage (Z ω) T = timeAverage (fun t => f (Y t ω)) T-a := by
    dsimp only [timeAverage,Z]
    rw [intervalIntegral.integral_sub (f := fun t => f (Y t ω)) (g := fun _ => a) ((hf.continuous.comp (hcY ω)).intervalIntegrable 0 T)
      (intervalIntegrable_const),intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
    field_simp [hT.ne']
  simp_rw [he] at hh
  convert hh using 1 <;> ring

end Asakura.Chapter8
