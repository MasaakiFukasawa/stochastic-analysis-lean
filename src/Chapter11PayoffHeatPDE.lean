import Chapter11HeatMixtureJets
import Chapter11HeatKernelDerivatives
import Chapter11ScalarSlice
import Chapter11PayoffHeatSmooth

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem weighted_heat_mixture_equation (L : ℝ) (hL : 0<L) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t y : ℝ) (ht : 0<t ∧ t<L) :
    HasDerivAt (fun s => ∫ z,Real.exp (weightedHeatExponent L z (s,y)) ∂μ)
      ((1/2:ℝ)*deriv (deriv (fun a => ∫ z,Real.exp (weightedHeatExponent L z (t,a)) ∂μ)) y) t := by
  let F := fun q : ℝ × ℝ => ∫ z,Real.exp (weightedHeatExponent L z q) ∂μ
  have hU : IsOpen {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hs a : ContDiffAt ℝ ∞ F (t,a) := (weighted_heat_mixture_smooth L hL μ).contDiffAt (hU.mem_nhds ht)
  have hd := scalar_time_slice_derivative F t y (hs y)
  have hj : iteratedFDeriv ℝ 1 F (t,y) (fun _ => (1,0))=(1/2:ℝ)*iteratedFDeriv ℝ 2 F (t,y) (fun _ => (0,1)) := by
    dsimp only [F]
    rw [weighted_heat_mixture_jet_apply L hL μ 1 (t,y) ht,weighted_heat_mixture_jet_apply L hL μ 2 (t,y) ht,←integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun z => weighted_heat_jet_equation L z t y ht)
  rw [hj,scalar_space_second_jet F t y hs] at hd
  exact hd

/-- The actual heat equation for a Borel payoff of exponential growth,
with derivatives justified by the preceding finite-measure construction. -/
theorem exponential_payoff_heat_equation (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ z,0≤f z) (C m : ℝ) (hC : 0≤C) (hb : ∀ z,f z≤C*(1+Real.exp (m*z)))
    (t y : ℝ) (ht : 0<t) :
    HasDerivAt (fun s => ∫ z,f z*heatLogKernel z (s,y))
      ((1/2:ℝ)*deriv (deriv (fun a => ∫ z,f z*heatLogKernel z (t,a))) y) t := by
  let L := t+1
  have hL : 0<L := by dsimp [L];linarith
  obtain ⟨μ,hμ,he⟩ := exponential_payoff_heat_finite_representation f hf hn C m L hC hL hb
  letI := hμ
  have hh := weighted_heat_mixture_equation L hL μ t y ⟨ht,by dsimp [L];linarith⟩
  simp_rw [he] at hh
  exact hh

end Asakura.Chapter11
