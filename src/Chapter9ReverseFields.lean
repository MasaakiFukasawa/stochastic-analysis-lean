import Chapter9ReverseGeneratorBound
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory Set
open scoped ContDiff NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

noncomputable def ouCoordinateDensity {d : ℕ} (μ : Measure (Fin d → ℝ))
    (z : ℝ × (Fin d → ℝ)) : ℝ := ∫ x,Real.exp (ouExponent x z) ∂μ

noncomputable def ouReverseDrift {d : ℕ} (μ : Measure (Fin d → ℝ))
    (z : ℝ × (Fin d → ℝ)) : Fin d → ℝ := fun i => z.2 i+
      2*(fderiv ℝ (ouCoordinateDensity μ) z ((0:ℝ),Pi.single i 1))/ouCoordinateDensity μ z

noncomputable def ouReverseGenerator {d : ℕ} (μ : Measure (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (z : ℝ × (Fin d → ℝ)) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin d =>
    directional (directional f (Pi.single i 1)) (Pi.single i 1) z.2+
      ouReverseDrift μ z i*directional f (Pi.single i 1) z.2)

theorem ou_coordinate_density_measurable {d : ℕ} (μ : Measure (Fin d → ℝ)) [SFinite μ] :
    Measurable (ouCoordinateDensity μ) := by
  have hm : Measurable (fun z : (ℝ × (Fin d → ℝ)) × (Fin d → ℝ) => Real.exp (ouExponent z.2 z.1)) := by
    unfold ouExponent
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem ou_coordinate_density_positive {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0<t) (y : Fin d → ℝ) : 0<ouCoordinateDensity μ (t,y) := by
  have hv := ou_variance_positive t ht
  exact (gaussian_mixture_positive μ (Real.exp (-t)) ⟨1-Real.exp (-2*t),hv.le⟩
    (by intro h; exact hv.ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) h)) y).2

theorem ou_reverse_drift_measurable {d : ℕ} (μ : Measure (Fin d → ℝ)) [SFinite μ] :
    Measurable (ouReverseDrift μ) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).add
    ((measurable_const.mul (measurable_fderiv_apply_const ℝ (ouCoordinateDensity μ) ((0:ℝ),Pi.single i 1))).div
      (ou_coordinate_density_measurable μ))

theorem ou_reverse_generator_measurable {d : ℕ} (μ : Measure (Fin d → ℝ)) [SFinite μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) : Measurable (ouReverseGenerator μ f) := by
  unfold ouReverseGenerator
  apply Finset.measurable_sum
  intro i _
  exact (((directional_smooth _ (directional_smooth f hf _) _).continuous.measurable).comp measurable_snd).add
    (((measurable_pi_apply i).comp (ou_reverse_drift_measurable μ)).mul
      ((directional_smooth f hf _).continuous.measurable.comp measurable_snd))

theorem ou_reverse_generator_eq {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (t : ℝ) (ht : 0<t) (y : Fin d → ℝ) :
    ouReverseGenerator μ f (t,y)=reverseTest (fun x => ouCoordinateDensity μ (t,x)) f y := by
  have hsm : ContDiffAt ℝ ∞ (ouCoordinateDensity μ) (t,y) :=
    (ou_gaussian_mixture_smooth μ).contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have he i : fderiv ℝ (ouCoordinateDensity μ) (t,y) ((0:ℝ),Pi.single i 1)=
      directional (fun x => ouCoordinateDensity μ (t,x)) (Pi.single i 1) y := by
    simpa only [iteratedFDeriv_one_apply] using spatial_slice_first_jet (ouCoordinateDensity μ) t y (Pi.single i 1) hsm
  unfold ouReverseGenerator reverseTest ouReverseDrift
  simp_rw [he]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ou_reverse_generator_continuous {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContinuousOn (ouReverseGenerator μ f) (Ioi 0 ×ˢ univ) := by
  have hp z (hz : z∈Ioi 0 ×ˢ (univ : Set (Fin d → ℝ))) : ouCoordinateDensity μ z≠0 :=
    (ou_coordinate_density_positive μ z.1 hz.1 z.2).ne'
  have hh := reverse_test_joint_continuous (ouCoordinateDensity μ) (Ioi 0) isOpen_Ioi
    ((ou_gaussian_mixture_smooth μ).mono (fun z hz => hz.1)) hp f hf
  exact hh.congr (fun z hz => ou_reverse_generator_eq μ f z.1 hz.1 z.2)

theorem ou_reverse_generator_bound {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (ε T : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0≤C ∧ ∀ t∈Icc ε T,∀ y,‖ouReverseGenerator μ f (t,y)‖≤C := by
  obtain ⟨C,hC,hbound⟩ := ou_reverse_generator_uniform_bound μ f hf hfc ε T hε
  refine ⟨C,hC,?_⟩
  intro t ht y
  rw [ou_reverse_generator_eq μ f t (hε.trans_le ht.1) y]
  exact hbound t ht y
end Asakura.Chapter9
