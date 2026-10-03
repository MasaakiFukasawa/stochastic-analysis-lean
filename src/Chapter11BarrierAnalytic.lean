import Chapter11BarrierHeatReflection
import Chapter11HeatBrownianCalculus
import Chapter11BarrierBounds

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false

/-- The difference of two actual smooth heat solutions again solves the
heat equation, including the second spatial derivative. -/
theorem heat_difference_equation (F G : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1}) (hG : ContDiffOn ℝ ∞ G {q | 0<q.1})
    (hpF : ∀ t y,0<t → deriv (fun s => F (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => F (t,a))) y)
    (hpG : ∀ t y,0<t → deriv (fun s => G (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => G (t,a))) y)
    (t y : ℝ) (ht : 0<t) :
    deriv (fun s => F (s,y)-G (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => F (t,a)-G (t,a))) y := by
  have hsF a : ContDiffAt ℝ ∞ F (t,a) := hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have hsG a : ContDiffAt ℝ ∞ G (t,a) := hG.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have hxF : ContDiff ℝ ∞ (fun a => F (t,a)) := contDiff_iff_contDiffAt.mpr fun a => (hsF a).comp a (contDiffAt_const.prodMk contDiffAt_id)
  have hxG : ContDiff ℝ ∞ (fun a => G (t,a)) := contDiff_iff_contDiffAt.mpr fun a => (hsG a).comp a (contDiffAt_const.prodMk contDiffAt_id)
  have he : deriv (fun a => F (t,a)-G (t,a))=(fun a => deriv (fun a => F (t,a)) a-deriv (fun a => G (t,a)) a) := by
    funext a
    exact deriv_sub ((hxF.differentiable (by simp)).differentiableAt) ((hxG.differentiable (by simp)).differentiableAt)
  have htF : DifferentiableAt ℝ (fun s => F (s,y)) t := ((hsF y).comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have htG : DifferentiableAt ℝ (fun s => G (s,y)) t := ((hsG y).comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hdt : deriv (fun s => F (s,y)-G (s,y)) t=deriv (fun s => F (s,y)) t-deriv (fun s => G (s,y)) t := deriv_sub htF htG
  have hdF := ((contDiff_infty_iff_deriv.mp hxF).2.differentiable (by simp)).differentiableAt (x:=y)
  have hdG := ((contDiff_infty_iff_deriv.mp hxG).2.differentiable (by simp)).differentiableAt (x:=y)
  have hdd : deriv (fun a => deriv (fun a => F (t,a)) a-deriv (fun a => G (t,a)) a) y=
      deriv (deriv (fun a => F (t,a))) y-deriv (deriv (fun a => G (t,a))) y := deriv_sub hdF hdG
  rw [hdt,hpF t y ht,hpG t y ht,he,hdd]
  ring

noncomputable def imageHeat (f : ℝ → ℝ) (ν : ℝ) (q : ℝ × ℝ) : ℝ :=
  (∫ z,f z*heatLogKernel z q)-(∫ z,(Real.exp (-ν*z)*f (-z))*heatLogKernel z q)

/-- The image solution is built from the actual bounded Borel payoff,
without assuming its differentiability or continuity at the barrier. -/
theorem image_heat_smooth_harmonic (f : ℝ → ℝ) (hf : Measurable f)
    (K ν A σ T c : ℝ) (hK : 0≤K) (hn : ∀ z,0≤f z) (hb : ∀ z,f z≤K) (hσ : σ≠0) :
    ContDiffOn ℝ ∞ (imageHeat f ν) {q | 0<q.1} ∧
      ContDiffOn ℝ 2 (brownianHeatPrice (imageHeat f ν) A σ T c) {q | q 0<T} ∧
      ∀ t x,t<T → fderiv ℝ (brownianHeatPrice (imageHeat f ν) A σ T c) ![t,x] (Pi.single 0 1)+
        fderiv ℝ (fderiv ℝ (brownianHeatPrice (imageHeat f ν) A σ T c)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=0 := by
  have hb' z : f z≤K*(1+Real.exp ((0:ℝ)*z)) := by simpa using (hb z).trans (by linarith : K≤K*(1+1))
  obtain ⟨hgm,hgn,hgb⟩ := reflected_payoff_exponential_bound f hf K ν hK hn hb
  have hF := exponential_payoff_heat_smooth f hf hn K 0 hK hb'
  have hG := exponential_payoff_heat_smooth _ hgm hgn K (-ν) hK hgb
  have hFp t y (ht : 0<t) := (exponential_payoff_heat_equation f hf hn K 0 hK hb' t y ht).deriv
  have hGp t y (ht : 0<t) := (exponential_payoff_heat_equation _ hgm hgn K (-ν) hK hgb t y ht).deriv
  have hS : ContDiffOn ℝ ∞ (imageHeat f ν) {q | 0<q.1} := hF.sub hG
  have hP t y (ht : 0<t) := heat_difference_equation _ _ hF hG hFp hGp t y ht
  refine ⟨hS,?_,?_⟩
  · intro q hq
    exact ((brownian_heat_smooth_at _ hS A σ T c hσ q hq).of_le (by simp)).contDiffWithinAt
  · intro t x ht
    exact brownian_heat_harmonic _ hS hP A σ T c hσ t x ht

/-- The smooth heat difference equals the weighted reflected Gaussian
price appearing in the manuscript. -/
theorem image_heat_gaussian_formula (f : ℝ → ℝ) (a θ ν y v : ℝ)
    (hv : 0<v) (hν : ν*v=2*a*θ) :
    imageHeat f ν (v,y+a*θ)=
      (∫ z,f z*gaussianPDFReal (y+a*θ) (NNReal.mk v hv.le) z)-
      Real.exp (-ν*y)*(∫ z,f z*gaussianPDFReal (-y+a*θ) (NNReal.mk v hv.le) z) := by
  dsimp only [imageHeat]
  simp_rw [heat_log_kernel_pdf v (y+a*θ) _ hv]
  rw [barrier_reflected_heat_integral f a θ ν y (NNReal.mk v hv.le) (by
    intro h;have hh := congrArg (fun q : ℝ≥0 => (q:ℝ)) h;exact hv.ne' hh) hν]

end Asakura.Chapter11
