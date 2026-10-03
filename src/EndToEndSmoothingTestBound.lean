import Chapter12ConvolutionWeakLimit

open MeasureTheory Set
open scoped Topology BoundedContinuousFunction NNReal
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The error estimate used twice in the printed Gaussian smoothing proof;
 its bound is independent of the law being smoothed. -/
theorem smoothing_test_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hg : Integrable (fun z : E => ‖z‖) γ)
    (φ : E →ᵇ ℝ) (L : ℝ≥0) (hL : LipschitzWith L φ) (r : ℝ) :
    |(∫ z : E × E,φ (z.1+r • z.2) ∂μ.prod γ)-(∫ x,φ x ∂μ)| ≤
      (L:ℝ)*|r| *(∫ z,‖z‖ ∂γ) := by
  have hi : Integrable (fun z : E × E => φ (z.1+r • z.2)) (μ.prod γ) :=
    Integrable.of_bound (by fun_prop) ‖φ‖ (.of_forall (fun z => φ.norm_coe_le_norm _))
  have hi0 : Integrable (fun z : E × E => φ z.1) (μ.prod γ) := (φ.integrable μ).comp_fst γ
  have hf : (∫ z : E × E,φ z.1 ∂μ.prod γ)=(∫ x,φ x ∂μ) := by
    rw [integral_prod _ hi0]
    simp
  rw [← hf,← integral_sub hi hi0]
  have hb (z : E × E) : ‖φ (z.1+r • z.2)-φ z.1‖ ≤ (L:ℝ)*|r| *‖z.2‖ := by
    have h := hL.norm_sub_le (z.1+r • z.2) z.1
    simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,mul_assoc] using h
  have hib : Integrable (fun z : E × E => (L:ℝ)*|r| *‖z.2‖) (μ.prod γ) :=
    (hg.const_mul ((L:ℝ)*|r|)).comp_snd μ
  calc
    _ ≤ ∫ z : E × E,‖φ (z.1+r • z.2)-φ z.1‖ ∂μ.prod γ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z : E × E => φ (z.1+r • z.2)-φ z.1)
    _ ≤ ∫ z : E × E,(L:ℝ)*|r| *‖z.2‖ ∂μ.prod γ :=
      integral_mono (hi.sub hi0).norm hib hb
    _ = (L:ℝ)*|r| *(∫ z,‖z‖ ∂γ) := by
      rw [integral_prod _ hib]
      simp only [integral_const_mul,integral_const,probReal_univ,one_smul]

#print axioms smoothing_test_bound
end Asakura.EndToEnd
