import Chapter11EuropeanAnalytic
import Chapter11HeatEndpoint

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianLogPrice (f : ℝ → ℝ) (r σ t x : ℝ) : ℝ :=
  Real.exp (-r*t)*(∫ z,f (Real.log x+(r-σ^2/2)*t+Real.sqrt (σ^2*t)*z) ∂gaussianReal 0 1)

/-- The discounted, drifted Gaussian price converges uniformly on every
compact set of positive stock prices, including the discount and drift. -/
theorem gaussian_price_uniform_endpoint (f : ℝ → ℝ) (hf : Continuous f)
    (C m r σ : ℝ) (hC : 0≤C) (hb : ∀ z,|f z|≤C*(1+Real.exp (m*z)))
    (K : Set ℝ) (hK : IsCompact K) (hKpos : K⊆Ioi 0) :
    TendstoUniformlyOn (gaussianLogPrice f r σ) (fun x => f (Real.log x))
      (𝓝[Icc (0:ℝ) 1] 0) K := by
  have hA := exponential_heat_average_continuous f hf C m hC hb
  have hlog : ContinuousOn (fun q : ℝ × ℝ => Real.log q.2) (Icc (0:ℝ) 1 ×ˢ K) :=
    continuous_snd.continuousOn.log (fun q hq => ne_of_gt (hKpos hq.2))
  have hmap : ContinuousOn (fun q : ℝ × ℝ => (σ^2*q.1,Real.log q.2+(r-σ^2/2)*q.1)) (Icc (0:ℝ) 1 ×ˢ K) :=
    (continuousOn_const.mul continuous_fst.continuousOn).prodMk
      (hlog.add (continuousOn_const.mul continuous_fst.continuousOn))
  have hE : ContinuousOn (fun q : ℝ × ℝ => Real.exp (-r*q.1)) (Icc (0:ℝ) 1 ×ˢ K) := by fun_prop
  have hc : ContinuousOn (fun q : ℝ × ℝ => gaussianLogPrice f r σ q.1 q.2) (Icc (0:ℝ) 1 ×ˢ K) :=
    hE.mul (hA.comp_continuousOn hmap)
  have hu := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc
  have ht := UniformContinuousOn.tendstoUniformlyOn (F:=gaussianLogPrice f r σ)
    (by convert hu using 1;funext q;rcases q with ⟨t,x⟩;rfl) (show (0:ℝ)∈Icc 0 1 by simp)
  have hz : gaussianLogPrice f r σ 0=(fun x => f (Real.log x)) := by
    funext x
    simp [gaussianLogPrice]
  rw [hz] at ht
  exact ht

theorem european_gaussian_uniform_endpoint (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h)
    (hn : ∀ x,0≤h x) (C m r σ : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (K : Set ℝ) (hK : IsCompact K) (hKpos : K⊆Ioi 0) :
    TendstoUniformlyOn (gaussianLogPrice (logPayoff h) r σ) (fun x => logPayoff h (Real.log x))
      (𝓝[Icc (0:ℝ) 1] 0) K := by
  obtain ⟨hc,hn,hb⟩ := log_payoff_regular h hh hn C m hb
  exact gaussian_price_uniform_endpoint _ hc C m r σ hC
    (fun z => by rw [abs_of_nonneg (hn z)];exact hb z) K hK hKpos

theorem european_heat_equals_gaussian_log_price (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h)
    (r σ t x : ℝ) (hσ : σ≠0) (ht : 0<t) :
    europeanHeatPrice h r σ t x=gaussianLogPrice (logPayoff h) r σ t x := by
  dsimp only [europeanHeatPrice,heatPrice,gaussianLogPrice]
  have hm : Measurable (logPayoff h) := (hh.comp (Real.continuous_exp.subtype_mk _)).measurable
  rw [heat_gaussian_representation _ hm _ _
    (mul_pos (sq_pos_of_ne_zero hσ) ht)]

end Asakura.Chapter11
