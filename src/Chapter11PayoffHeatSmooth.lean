import Chapter11WeightedHeatSmooth
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

noncomputable def heatLogKernel (z : ℝ) (q : ℝ × ℝ) : ℝ :=
  Real.exp (-(1:ℝ)/2*Real.log (2*Real.pi*q.1)-(q.2-z)^2/(2*q.1))

/-- Exponential growth is integrable against every strictly decaying
Gaussian weight; no derivatives of the payoff are needed. -/
theorem exponential_growth_gaussian_weight (f : ℝ → ℝ) (hf : Measurable f)
    (C m c : ℝ) (hC : 0≤C) (hc : 0<c) (hb : ∀ z,|f z|≤C*(1+Real.exp (m*z))) :
    Integrable (fun z => f z*Real.exp (-c*z^2)) volume := by
  have hdom := (integrable_exp_neg_mul_sq (show 0<c/2 by positivity)).const_mul
    (C*(1+Real.exp (m^2/(2*c))))
  apply hdom.mono' (by fun_prop)
  apply ae_of_all
  intro z
  have hy : m*z-c*z^2/2≤m^2/(2*c) := by
    apply (le_div_iff₀ (by positivity : 0<2*c)).mpr
    nlinarith [sq_nonneg (c*z-m)]
  have h0 : Real.exp (-c*z^2)≤Real.exp (-(c/2)*z^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hc.le (sq_nonneg z)]
  have h1 : Real.exp (m*z)*Real.exp (-c*z^2)≤Real.exp (m^2/(2*c))*Real.exp (-(c/2)*z^2) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (C*(1+Real.exp (m*z)))*Real.exp (-c*z^2) := mul_le_mul_of_nonneg_right (hb z) (Real.exp_pos _).le
    _ = C*(Real.exp (-c*z^2)+Real.exp (m*z)*Real.exp (-c*z^2)) := by ring
    _ ≤ C*(Real.exp (-(c/2)*z^2)+Real.exp (m^2/(2*c))*Real.exp (-(c/2)*z^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 h1) hC
    _ = _ := by ring

/-- Gaussian reweighting turns an exponentially growing payoff into a
finite measure, without changing its heat convolution. -/
theorem exponential_payoff_heat_finite_representation (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ z,0≤f z) (C m L : ℝ) (hC : 0≤C) (hL : 0<L)
    (hb : ∀ z,f z≤C*(1+Real.exp (m*z))) :
    ∃ μ : Measure ℝ,IsFiniteMeasure μ ∧ ∀ p : ℝ × ℝ,
      (∫ z,Real.exp (weightedHeatExponent L z p) ∂μ)=(∫ z,f z*heatLogKernel z p) := by
  let w := fun z => f z*Real.exp (-(1/(8*L))*z^2)
  have hwm : Measurable w := by fun_prop
  have hwn z : 0≤w z := mul_nonneg (hn z) (Real.exp_pos _).le
  have hwi : Integrable w volume := exponential_growth_gaussian_weight f hf C m (1/(8*L)) hC
    (by positivity) (fun z => by rw [abs_of_nonneg (hn z)];exact hb z)
  let μ := volume.withDensity (fun z => ENNReal.ofReal (w z))
  letI : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have he p : (∫ z,Real.exp (weightedHeatExponent L z p) ∂μ)=(∫ z,f z*heatLogKernel z p) := by
    rw [integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change (ENNReal.ofReal (w z)).toReal • Real.exp (weightedHeatExponent L z p)=f z*heatLogKernel z p
    rw [ENNReal.toReal_ofReal (hwn z)]
    dsimp only [w,weightedHeatExponent,heatLogKernel,smul_eq_mul]
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  exact ⟨μ,inferInstance,he⟩

/-- The actual heat convolution of a nonnegative exponentially growing
Borel payoff is jointly smooth at every positive time. -/
theorem exponential_payoff_heat_smooth (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ z,0≤f z) (C m : ℝ) (hC : 0≤C) (hb : ∀ z,f z≤C*(1+Real.exp (m*z))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => ∫ z,f z*heatLogKernel z q) {q | 0<q.1} := by
  intro q hq
  change 0<q.1 at hq
  let L := q.1+1
  have hL : 0<L := by dsimp [L];linarith
  obtain ⟨μ,hμ,he⟩ := exponential_payoff_heat_finite_representation f hf hn C m L hC hL hb
  letI := hμ
  let U := {p : ℝ × ℝ | 0<p.1 ∧ p.1<L}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hqU : q∈U := ⟨hq,by dsimp [L];linarith⟩
  have hs := weighted_heat_mixture_smooth L hL μ
  have hs' : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ∫ z,f z*heatLogKernel z p) U := by
    apply hs.congr
    intro p hp
    exact (he p).symm
  exact (hs'.contDiffAt (hU.mem_nhds hqU)).contDiffWithinAt

end Asakura.Chapter11
