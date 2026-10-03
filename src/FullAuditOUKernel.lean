import FullAuditOUExercise
import FullAuditChapter4Gronwall

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 500000

theorem ou_variance_nonnegative (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    0 ≤ σ^2*(1-Real.exp (-2*κ*(t:ℝ)))/(2*κ) := by
  apply div_nonneg (mul_nonneg (sq_nonneg _) _) (by positivity)
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) t.property))

noncomputable def ouVariance (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨σ^2*(1-Real.exp (-2*κ*(t:ℝ)))/(2*κ),ou_variance_nonnegative κ σ hκ t⟩

/-- Variance of the deterministic Wiener integral in the explicit OU solution. -/
theorem ou_kernel_variance_integral (κ σ T : ℝ) (hκ : 0 < κ) :
    (∫ s in 0..T, σ^2*Real.exp (-2*κ*(T-s))) = σ^2*(1-Real.exp (-2*κ*T))/(2*κ) := by
  let F := fun s => σ^2/(2*κ)*Real.exp (-2*κ*(T-s))
  have hF (s : ℝ) : HasDerivAt F (σ^2*Real.exp (-2*κ*(T-s))) s := by
    have h := ((((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul (-2*κ)).exp).const_mul (σ^2/(2*κ))
    convert h using 1
    · rfl
    · simp only [Pi.sub_apply,id_eq]
      norm_num only
      field_simp
  have hi : IntervalIntegrable (fun s => σ^2*Real.exp (-2*κ*(T-s))) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => σ^2*Real.exp (-2*κ*(T-s)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) hi]
  simp only [F,sub_self,mul_zero,Real.exp_zero,mul_one,sub_zero]
  ring

noncomputable def ouKernel (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (x : ℝ) : Measure ℝ :=
  gaussianReal (Real.exp (-κ*(t:ℝ))*x) (ouVariance κ σ hκ t)

theorem ou_variance_composition (κ σ : ℝ) (hκ : 0 < κ) (s t : ℝ≥0) :
    (Real.exp (-κ*(t:ℝ)))^2*(ouVariance κ σ hκ s:ℝ)+(ouVariance κ σ hκ t:ℝ) =
      (ouVariance κ σ hκ (s+t):ℝ) := by
  change Real.exp (-κ*(t:ℝ))^2*(σ^2*(1-Real.exp (-2*κ*(s:ℝ)))/(2*κ))+
    σ^2*(1-Real.exp (-2*κ*(t:ℝ)))/(2*κ) = σ^2*(1-Real.exp (-2*κ*((s+t:ℝ≥0):ℝ)))/(2*κ)
  rw [NNReal.coe_add,pow_two,← Real.exp_add,show -κ*(t:ℝ)+ -κ*(t:ℝ) = -2*κ*(t:ℝ) by ring,
    show -2*κ*((s:ℝ)+(t:ℝ)) = -2*κ*(s:ℝ)+ -2*κ*(t:ℝ) by ring,Real.exp_add]
  ring

/-- Direct composition of the Gaussian transition laws, with both their means
 and variances computed. This is the requested check of Chapman-Kolmogorov. -/
theorem ou_kernel_composition (κ σ : ℝ) (hκ : 0 < κ) (s t : ℝ≥0) (x : ℝ) :
    (ouKernel κ σ hκ s x).map (fun y => Real.exp (-κ*(t:ℝ))*y) ∗
      gaussianReal 0 (ouVariance κ σ hκ t) = ouKernel κ σ hκ (s+t) x := by
  rw [ouKernel,gaussianReal_map_const_mul,gaussianReal_conv_gaussianReal]
  apply congrArg₂ gaussianReal
  · simp only [add_zero,NNReal.coe_add]
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  · apply Subtype.ext
    change Real.exp (-κ*(t:ℝ))^2*(ouVariance κ σ hκ s:ℝ)+(ouVariance κ σ hκ t:ℝ) = _
    exact ou_variance_composition κ σ hκ s t

theorem ou_kernel_initial (κ σ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    ouKernel κ σ hκ 0 x = Measure.dirac x := by
  have hv : ouVariance κ σ hκ 0 = 0 := by
    apply Subtype.ext
    change σ^2*(1-Real.exp (-2*κ*(0:ℝ)))/(2*κ) = 0
    simp
  simp only [ouKernel,NNReal.coe_zero,mul_zero,Real.exp_zero,one_mul,hv,gaussianReal_zero_var]

/-- The explicit solution's deterministic mean plus its centered Gaussian
 Wiener integral has precisely the transition law used above. -/
theorem ou_explicit_solution_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ σ x : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (I : Ω → ℝ)
    (hI : HasLaw I (gaussianReal 0 (ouVariance κ σ hκ t)) P) :
    HasLaw (fun ω => Real.exp (-κ*(t:ℝ))*x+I ω) (ouKernel κ σ hκ t x) P := by
  simpa only [zero_add,ouKernel] using gaussianReal_const_add hI (Real.exp (-κ*(t:ℝ))*x)

end Asakura.FullAudit
