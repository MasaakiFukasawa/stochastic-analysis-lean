import Chapter5LinearImageAverage
import Chapter5GaussianSubspaceTrace
import Chapter5VectorHeatEndpoint

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The heat operator acts only in the noise directions Q e_i; frozen
past parameters receive no second-order term. The averaging measure is
the image of the genuine product standard normal law under Q. -/
theorem gaussian_subspace_heat_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (Q : (Fin (n+1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (x : E) (t : ℝ) (ht : 0<t) :
    let ν := (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map Q
    let A := fun s y => ∫ z,f (y+Real.sqrt s • z) ∂ν
    HasDerivAt (fun s => A s x)
      ((1/2:ℝ)*∑ i,fderiv ℝ (fderiv ℝ (A t)) x (Q (Pi.single i 1)) (Q (Pi.single i 1))) t := by
  let : ContinuousENorm (E →L[ℝ] E →L[ℝ] ℝ) := SeminormedAddGroup.toContinuousENorm (E := E →L[ℝ] E →L[ℝ] ℝ)
  let : ContinuousENorm (E →L[ℝ] ℝ) := SeminormedAddGroup.toContinuousENorm (E := E →L[ℝ] ℝ)
  dsimp only
  let μ := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let ν := μ.map Q
  have hi : Integrable (fun z : E => z) ν :=
    (linear_image_second_moment μ Q (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))).integrable (by norm_num)
  obtain ⟨h0,_,_,_⟩ := averaged_bounded_fderiv ν hi f D hd hDc C hD
  obtain ⟨h1,_,_,_⟩ := averaged_bounded_fderiv ν hi D DD hdd hDDc K hDD
  have he : fderiv ℝ (fun y => ∫ z,f (y+Real.sqrt t • z) ∂ν) =
      (fun y => ∫ z,D (y+Real.sqrt t • z) ∂ν) := funext (fun y => (h0 y t).fderiv)
  have hDDi : Integrable (fun z => DD (x+Real.sqrt t • z)) ν :=
    Integrable.of_bound (f := fun z => DD (x+Real.sqrt t • z)) (μ := ν) (hDDc.comp (by fun_prop)).aestronglyMeasurable K (ae_of_all _ fun z => hDD _)
  have hess (i : Fin (n+1)) :
      fderiv ℝ (fderiv ℝ (fun y => ∫ z,f (y+Real.sqrt t • z) ∂ν)) x (Q (Pi.single i 1)) (Q (Pi.single i 1)) =
      ∫ z,DD (x+Real.sqrt t • Q z) (Q (Pi.single i 1)) (Q (Pi.single i 1)) ∂μ := by
    rw [he,(h1 x t).fderiv,ContinuousLinearMap.integral_apply hDDi]
    have hDie : Integrable (fun z => DD (x+Real.sqrt t • z) (Q (Pi.single i 1))) ν :=
      Integrable.of_bound (f := fun z => DD (x+Real.sqrt t • z) (Q (Pi.single i 1))) (μ := ν) ((hDDc.comp (by fun_prop)).clm_apply continuous_const).aestronglyMeasurable
        ((K:ℝ)*‖Q (Pi.single i 1)‖) (ae_of_all _ fun z =>
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hDD _) (norm_nonneg _)))
    rw [ContinuousLinearMap.integral_apply hDie]
    exact linear_image_average_integral μ Q _
      ((hDDc.clm_apply continuous_const).clm_apply continuous_const) x t
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hd y).differentiableAt) (fun y => by rw [(hd y).fderiv]; exact_mod_cast hD y)
  have hfi := vector_lipschitz_average_integrable ν hi f C hl x t
  have htD := vector_average_time_derivative_of_integrable ν hi f D hd hDc C hD x t ht hfi
  have hm : (∫ z,D (x+Real.sqrt t • z) z ∂ν) = ∫ z,D (x+Real.sqrt t • Q z) (Q z) ∂μ :=
    integral_map Q.continuous.measurable.aemeasurable
      ((hDc.comp (by fun_prop)).clm_apply continuous_id).aestronglyMeasurable
  have htrace := gaussian_subspace_gradient_trace n Q D DD hdd hDc hDDc C K hD hDD x t
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  convert htD using 1
  dsimp only [ν,μ] at hess
  simp_rw [hess]
  rw [integral_div,hm,htrace]
  field_simp

end Asakura.Chapter5
