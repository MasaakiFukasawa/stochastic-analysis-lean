import Chapter9DenoisingConnection

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_affine_coordinate_law {d : ℕ} (a : ℝ) (v : ℝ≥0) (x : Fin d → ℝ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
      (fun ξ i => a*x i+Real.sqrt (v:ℝ)*ξ i)=
        Measure.pi (fun i => gaussianReal (a*x i) v) := by
  let f := fun i : Fin d => fun z : ℝ => a*x i+Real.sqrt (v:ℝ)*z
  have hf i : Measurable (f i) := by dsimp [f]; fun_prop
  letI : ∀ i : Fin d, IsProbabilityMeasure ((gaussianReal 0 1).map (f i)) :=
    fun i => (Measure.isProbabilityMeasure_map_iff (hf i).aemeasurable).mpr inferInstance
  change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (fun ξ i => f i (ξ i))=_
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  congr 1
  funext i
  have he : f i=(fun z => a*x i+z) ∘ (fun z => Real.sqrt (v:ℝ)*z) := rfl
  rw [he,←Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero,zero_add]
  congr 1
  apply Subtype.ext
  change (Real.sqrt (v:ℝ))^2*1=(v:ℝ)
  simpa using Real.sq_sqrt v.coe_nonneg


/-- A fiberwise density identifies the joint pushforward on rectangles;
finite-measure uniqueness then gives equality on the full product sigma algebra. -/
theorem joint_map_of_fiber_density {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ρ : Measure B) (ν : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [SFinite ν]
    (F : A × B → C) (hF : Measurable F) (k : A × C → ℝ≥0∞) (hk : Measurable k)
    (hLaw : ∀ x,ρ.map (fun y => F (x,y))=ν.withDensity (fun z => k (x,z))) :
    (μ.prod ρ).map (fun z => (z.1,F z))=(μ.prod ν).withDensity k := by
  have hmap : Measurable (fun z : A × B => (z.1,F z)) := measurable_fst.prodMk hF
  haveI : IsProbabilityMeasure ((μ.prod ρ).map (fun z => (z.1,F z))) :=
    (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).mpr inferInstance
  apply Measure.ext_prod
  intro S T hS hT
  rw [Measure.map_apply hmap (hS.prod hT),Measure.prod_apply (hmap (hS.prod hT)),
    withDensity_apply k (hS.prod hT),←Measure.prod_restrict,lintegral_prod _ hk.aemeasurable]
  rw [←lintegral_indicator hS]
  apply lintegral_congr
  intro x
  by_cases hx : x∈S
  · have he : (Prod.mk x) ⁻¹' ((fun z : A × B => (z.1,F z)) ⁻¹' (S ×ˢ T))=
        (fun y => F (x,y)) ⁻¹' T := by ext y; simp [hx]
    have hFx : Measurable (fun y => F (x,y)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [he,indicator_of_mem hx,←Measure.map_apply hFx hT,hLaw x,withDensity_apply _ hT]
  · have he : (Prod.mk x) ⁻¹' ((fun z : A × B => (z.1,F z)) ⁻¹' (S ×ˢ T))=∅ := by
      ext y
      simp [hx]
    rw [he,measure_empty,indicator_of_notMem hx]

theorem gaussian_observation_joint_law {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    (μ.prod (Measure.pi (fun _ : Fin d => gaussianReal 0 1))).map
      (fun z => (z.1,fun i => a*z.1 i+Real.sqrt (v:ℝ)*z.2 i))=
      (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2)) := by
  apply joint_map_of_fiber_density μ (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) volume
    (fun z i => a*z.1 i+Real.sqrt (v:ℝ)*z.2 i) (by fun_prop)
    (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
    (by unfold gaussianKernel; fun_prop)
  intro x
  rw [gaussian_affine_coordinate_law,gaussian_kernel_density a v hv x]

theorem component_score_noise {d : ℕ} (a v : ℝ) (hv : 0<v) (x ξ : Fin d → ℝ) :
    componentScore a v (x,fun i => a*x i+Real.sqrt v*ξ i)=
      (-1/Real.sqrt v) • WithLp.toLp 2 ξ := by
  have hs : Real.sqrt v≠0 := (Real.sqrt_pos.mpr hv).ne'
  have hsq := Real.sq_sqrt hv.le
  ext i
  simp only [componentScore,PiLp.smul_apply,WithLp.ofLp_toLp,smul_eq_mul]
  field_simp
  nlinarith [congrArg (fun r : ℝ => r*ξ i) hsq]

/-- The score is an admissible observable competitor in the loss problem. -/
theorem gaussian_score_observable {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    AEStronglyMeasurable[MeasurableSpace.comap Prod.snd inferInstance]
      (fun z => mixtureScore μ a v z.2)
      ((μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))) :=
  stronglyMeasurable_condExp.aestronglyMeasurable.congr (gaussian_denoising_score μ a v hv)

/-- The loss under the independent-noise sampling procedure is exactly
the loss under the constructed observation law used in the projection proof. -/
theorem gaussian_training_loss {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (s : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) (hs : StronglyMeasurable s) :
    (∫ z,‖s (fun i => a*z.1 i+Real.sqrt (v:ℝ)*z.2 i)+
      (1/Real.sqrt (v:ℝ)) • WithLp.toLp 2 z.2‖^2
      ∂μ.prod (Measure.pi (fun _ : Fin d => gaussianReal 0 1)))=
    ∫ z,‖s z.2-componentScore a v z‖^2
      ∂(μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2)) := by
  have hSc : Continuous (componentScore (d := d) a v) := by unfold componentScore; fun_prop
  have hm : StronglyMeasurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) =>
      ‖s z.2-componentScore a v z‖^2) :=
    ((hs.comp_measurable measurable_snd).sub hSc.stronglyMeasurable).norm.pow 2
  rw [←gaussian_observation_joint_law μ a v hv,
    integral_map (by fun_prop) hm.aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [component_score_noise a v (by exact_mod_cast (pos_iff_ne_zero.mpr hv))]
  simp only [neg_div,neg_smul,sub_neg_eq_add]
end Asakura.Chapter9
