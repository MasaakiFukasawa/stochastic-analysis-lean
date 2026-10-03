import Chapter9ReverseGeneratorBound
import Chapter9ReverseKernelBound

open MeasureTheory Set
open scoped ContDiff NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The derivative of the reverse-kernel test integral stays bounded all
the way to its lower time endpoint, by compact support and Gaussian integration. -/
theorem reverse_generator_integral_uniform_bound {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (τ b : ℝ) (hb : 0<b) (hbτ : b<τ) (x : Fin d → ℝ) :
    let p := fun t y => ∫ z,Real.exp (ouExponent z (t,y)) ∂μ
    ∃ C : ℝ,0≤C ∧ ∀ h∈Ioc 0 b,
      ‖(∫ y,p (τ-h) y*reverseTest (p (τ-h)) f y*
        gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x)/p τ x‖≤C := by
  let p := fun z => ∫ w,Real.exp (ouExponent w z) ∂μ
  have hsm : ContDiffOn ℝ ∞ p (Ioi 0 ×ˢ univ) :=
    (ou_gaussian_mixture_smooth μ).mono (fun z hz => hz.1)
  have hp (z : ℝ × (Fin d → ℝ)) (hz : z∈Ioi 0 ×ˢ univ) : p z≠0 := by
    have hv := ou_variance_positive z.1 hz.1
    exact (gaussian_mixture_positive μ (Real.exp (-z.1)) ⟨1-Real.exp (-2*z.1),hv.le⟩
      (by intro hz; exact hv.ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) hz)) z.2).2.ne'
  let q := fun h y => p (τ-h,y)*reverseTest (fun z => p (τ-h,z)) f y
  have hc : ContinuousOn q.uncurry (Iio τ ×ˢ univ) := by
    have hc0 := hsm.continuousOn.mul (reverse_test_joint_continuous p (Ioi 0) isOpen_Ioi hsm hp f hf)
    exact hc0.comp (show ContinuousOn (fun z : ℝ × (Fin d → ℝ) => (τ-z.1,z.2)) (Iio τ ×ˢ univ) by fun_prop)
      (fun z hz => by
        change 0<τ-z.1 ∧ z.2∈univ
        exact ⟨sub_pos.mpr hz.1,mem_univ _⟩)
  have hK : IsCompact (Icc 0 b ×ˢ tsupport f) := isCompact_Icc.prod hfc.isCompact
  have hsub : Icc 0 b ×ˢ tsupport f ⊆ Iio τ ×ˢ univ :=
    fun z hz => ⟨lt_of_le_of_lt hz.1.2 hbτ,mem_univ _⟩
  obtain ⟨M,hM⟩ := hK.bddAbove_image (hc.norm.mono hsub)
  have hbound h (hh : h∈Ioc 0 b) y : ‖q h y‖≤max 0 M := by
    by_cases hy : y∈tsupport f
    · exact (hM (mem_image_of_mem _ (show (h,y)∈Icc 0 b ×ˢ tsupport f from ⟨⟨hh.1.le,hh.2⟩,hy⟩))).trans (le_max_right _ _)
    · simp only [q,reverse_test_zero_outside _ f y hy,mul_zero,norm_zero]
      exact le_max_left _ _
  refine ⟨Real.exp ((d:ℝ)*b)*max 0 M/‖p (τ,x)‖,by positivity,?_⟩
  intro h hh
  have hq : Continuous (q h) := hc.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨lt_of_le_of_lt hh.2 hbτ,mem_univ _⟩)
  have hi := reverse_gaussian_integral_bound h b hh.1 hh.2 x (q h) hq (max 0 M)
    (le_max_left _ _) (hbound h hh)
  rw [norm_div]
  exact div_le_div_of_nonneg_right hi (norm_nonneg _)
end Asakura.Chapter9
