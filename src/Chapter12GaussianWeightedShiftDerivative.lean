import Chapter12GaussianTranslationIntegrable

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Differentiating the first Gaussian score produces the mixed second
score. L4 integrability of the payoff suffices; it may be discontinuous. -/
theorem finite_gaussian_weighted_shift_derivative {d : ℕ} (q v : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hm : Measurable f)
    (hf : MemLp f 4 (Measure.pi (fun _ : Fin d => gaussianReal 0 1))) :
    HasDerivAt
      (fun t : ℝ => ∫ z,f (t • v+z)*(∑ i,q i*z i) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (∫ z,f z*((∑ i,q i*z i)*(∑ i,v i*z i)-(∑ i,q i*v i))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) 0 := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let Q : ℝ := ∑ i,q i*v i
  let fq : (Fin d → ℝ) → ℝ := fun z => f z*(∑ i,q i*z i)
  have hlq : MemLp (fun z : Fin d → ℝ => ∑ i,q i*z i) 4 μ := by
    simpa using (finite_gaussian_linear_score_law q).memLp_comp (memLp_id_gaussianReal 4)
  have hlv : MemLp (fun z : Fin d → ℝ => ∑ i,v i*z i) 2 μ := by
    simpa using (finite_gaussian_linear_score_law v).memLp_comp (memLp_id_gaussianReal 2)
  have hf2 : MemLp f 2 μ := hf.mono_exponent (by norm_num)
  have hfq : MemLp fq 2 μ := hf.mul hlq
  have hmq : Measurable fq := hm.mul (by fun_prop)
  have hdf := finite_gaussian_translation_derivative_zero v f hm hf2
  have hdq := finite_gaussian_translation_derivative_zero v fq hmq hfq
  have hd := hdq.sub (((hasDerivAt_id (0:ℝ)).mul_const Q).mul hdf)
  have he (t : ℝ) :
      (∫ z,f (t • v+z)*(∑ i,q i*z i) ∂μ)=
        (∫ z,fq (t • v+z) ∂μ)-t*Q*(∫ z,f (t • v+z) ∂μ) := by
    have hI := finite_gaussian_translation_integrable v t f hm hf2
    have hIQ := finite_gaussian_translation_integrable v t fq hmq hfq
    rw [← integral_const_mul,← integral_sub hIQ (hI.const_mul (t*Q))]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    have hlin : (∑ i,q i*(t • v+z) i)=t*Q+(∑ i,q i*z i) := by
      dsimp only [Q]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    dsimp only [fq,Pi.sub_apply]
    rw [hlin]
    ring
  have hgoal := hd.congr_of_eventuallyEq (Eventually.of_forall he)
  convert hgoal using 1
  simp only [zero_smul,zero_add,id_eq,zero_mul,mul_zero,add_zero,one_mul]
  have hprod : Integrable (fun z => fq z*(∑ i,v i*z i)) μ := hfq.integrable_mul hlv
  rw [← integral_const_mul,← integral_sub hprod ((hf2.integrable (by norm_num)).const_mul Q)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by dsimp only [fq,Q,Pi.sub_apply,Pi.mul_apply]; ring)

end Asakura.Chapter12
