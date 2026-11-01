import Chapter9ProbabilityFlowMarginals
import Chapter9TransitionDensity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter9
open Asakura.Chapter9 Asakura.FullAudit
set_option maxHeartbeats 1800000

/-- Coordinate changes preserve densities when they preserve volume. -/
theorem density_toLp {d : ℕ} (k : (Fin d → ℝ) → ℝ≥0∞) (hk : Measurable k) :
    ((volume : Measure (Fin d → ℝ)).withDensity k).map (WithLp.toLp 2) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity (fun x => k x.ofLp) := by
  ext S hS
  rw [Measure.map_apply (WithLp.measurable_toLp 2 _) hS,
    withDensity_apply _ ((WithLp.measurable_toLp 2 _) hS),withDensity_apply _ hS]
  have h := (PiLp.volume_preserving_toLp (Fin d)).setLIntegral_comp_preimage
    hS (hk.comp (WithLp.measurable_ofLp 2 _))
  simpa using h

/-- The Gaussian affine law and the density transported by the ODE are the same measure. -/
theorem gaussian_affine_density {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    gaussianAffineLaw μ a (Real.sqrt (v:ℝ)) =
      volume.withDensity (fun y => ENNReal.ofReal
        (∫ x,gaussianKernel a v x.ofLp y.ofLp ∂μ)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let k := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    ENNReal.ofReal (gaussianKernel a v z.1.ofLp z.2.ofLp)
  have hk : Measurable k := by unfold k gaussianKernel; fun_prop
  have hf (x : EuclideanSpace ℝ (Fin d)) :
      γ.map (fun y => a • x+Real.sqrt (v:ℝ) • y) =
        volume.withDensity (fun y => k (x,y)) := by
    rw [show γ=(Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (WithLp.toLp 2) by
      exact map_pi_eq_stdGaussian.symm]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have he : (fun y : Fin d → ℝ => a • x+Real.sqrt (v:ℝ) • WithLp.toLp 2 y) =
      (WithLp.toLp 2) ∘ (fun y i => a*x i+Real.sqrt (v:ℝ)*y i) := rfl
    change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
      (fun y : Fin d → ℝ => a • x+Real.sqrt (v:ℝ) • WithLp.toLp 2 y)=_
    rw [he,←Measure.map_map (by fun_prop) (by fun_prop),
      gaussian_affine_coordinate_law,gaussian_kernel_density a v hv,density_toLp _ (by unfold gaussianKernel; fun_prop)]
  have hj := joint_map_of_fiber_density μ γ volume
    (fun z => a • z.1+Real.sqrt (v:ℝ) • z.2) (by fun_prop) k hk hf
  have hm := congrArg (fun ν => ν.map Prod.snd) hj
  rw [Measure.map_map (by fun_prop) (by fun_prop),product_density_snd μ volume k hk] at hm
  change gaussianAffineLaw μ a (Real.sqrt (v:ℝ))=_ at hm
  rw [hm]
  congr 1
  funext y
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) => gaussianKernel a v x.ofLp y.ofLp) μ :=
    (integrable_const _).mono' (by unfold gaussianKernel; fun_prop)
      (ae_of_all _ (fun x => gaussian_kernel_bound a v hv x.ofLp y.ofLp))
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun x => (gaussian_kernel_positive a v x.ofLp y.ofLp).le))).symm

theorem ou_affine_density {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0<t) :
    gaussianAffineLaw μ (Real.exp (-t)) (Real.sqrt (1-Real.exp (-2*t))) =
      volume.withDensity (fun y => ENNReal.ofReal (ouEuclideanDensity μ (t,y))) := by
  have hv : 0<1-Real.exp (-2*t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  exact gaussian_affine_density μ (Real.exp (-t)) ⟨1-Real.exp (-2*t),hv.le⟩
    (by intro h; have hh := congrArg (fun x : ℝ≥0 => (x : ℝ)) h; exact hv.ne' hh)

/-- The final cutoff conclusion in the new theorem 9.3.1, for the very same
positive-time densities as in probability_flow_marginals. -/
theorem probability_flow_density_cutoff {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (R : ℝ) (hb : ∀ᵐ x ∂μ, ‖x‖≤R) :
    Tendsto (fun t : ℝ => transportDistance
      (volume.withDensity (fun y => ENNReal.ofReal (ouEuclideanDensity μ (t,y)))) μ)
      (𝓝[>] 0) (𝓝 0) := by
  have hμ : MemLp (fun x => x) 2 μ := MemLp.of_bound measurable_id.aestronglyMeasurable R hb
  have h := (probability_flow_cutoff μ hμ).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [ou_affine_density μ t ht]

end Asakura.Chapter9
