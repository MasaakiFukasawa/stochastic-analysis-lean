import Chapter4DriftMomentBound
import FullAuditPathSpaceExercise

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4.Vector
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Joint evaluation on a clamped real interval, including its endpoints. -/
theorem clamped_path_evaluation_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (d : ℝ) (hd : 0 ≤ d)
    (Y : Ω → C(Icc (0:ℝ) d,Fin n → ℝ)) (hY : Measurable Y) :
    Measurable (fun z : Ω × ℝ => Y z.1 (projIcc 0 d hd z.2)) := by
  exact continuous_eval.measurable.comp
    ((hY.comp measurable_fst).prodMk ((show Continuous (projIcc 0 d hd) from continuous_projIcc).measurable.comp measurable_snd))

/-- The coefficient differences have finite time-probability L2 energy.
This derives integrability from the original squared Lipschitz hypothesis
and the L2 path norms, instead of adding it to the SDE assumptions. -/
theorem coefficient_difference_energy
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (d L : ℝ) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (μ σ : (Fin n → ℝ) → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y, (μ x-μ y)^2+(σ x-σ y)^2 ≤ L*‖x-y‖^2)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) d,Fin n → ℝ))
    (hm₁ : Measurable Y₁) (hm₂ : Measurable Y₂)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P) :
    let ν := P.prod (volume.restrict (Ioc (0:ℝ) d))
    let V := fun z : Ω × ℝ => Y₁ z.1 (projIcc 0 d hd z.2)-Y₂ z.1 (projIcc 0 d hd z.2)
    let U := fun z : Ω × ℝ => μ (Y₁ z.1 (projIcc 0 d hd z.2))-μ (Y₂ z.1 (projIcc 0 d hd z.2))
    let H := fun z : Ω × ℝ => σ (Y₁ z.1 (projIcc 0 d hd z.2))-σ (Y₂ z.1 (projIcc 0 d hd z.2))
    MemLp V 2 ν ∧ MemLp U 2 ν ∧ MemLp H 2 ν ∧
      (∫ z, (U z^2+H z^2) ∂ν) ≤ L*∫ z, ‖V z‖^2 ∂ν := by
  dsimp only
  let ν := P.prod (volume.restrict (Ioc (0:ℝ) d))
  let x₁ := fun z : Ω × ℝ => Y₁ z.1 (projIcc 0 d hd z.2)
  let x₂ := fun z : Ω × ℝ => Y₂ z.1 (projIcc 0 d hd z.2)
  have hx₁ : Measurable x₁ := clamped_path_evaluation_measurable d hd Y₁ hm₁
  have hx₂ : Measurable x₂ := clamped_path_evaluation_measurable d hd Y₂ hm₂
  have hiNorm : Integrable (fun z : Ω × ℝ => ‖Y₁ z.1-Y₂ z.1‖^2) ν :=
    ((hi₁.sub hi₂).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).comp_fst _
  have hpoint (z : Ω × ℝ) : ‖x₁ z-x₂ z‖^2 ≤ ‖Y₁ z.1-Y₂ z.1‖^2 := by
    have h := ContinuousMap.norm_coe_le_norm (Y₁ z.1-Y₂ z.1) (projIcc 0 d hd z.2)
    change ‖x₁ z-x₂ z‖ ≤ ‖Y₁ z.1-Y₂ z.1‖ at h
    simpa only using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hiV : Integrable (fun z => ‖x₁ z-x₂ z‖^2) ν := by
    apply hiNorm.mono' ((hx₁.sub hx₂).norm.pow_const 2).aestronglyMeasurable
    exact .of_forall (fun z => by simpa only [Pi.sub_apply,Pi.pow_apply,Real.norm_eq_abs,abs_sq] using hpoint z)
  have hb z := hLip (x₁ z) (x₂ z)
  have hiU : Integrable (fun z => (μ (x₁ z)-μ (x₂ z))^2) ν := by
    apply (hiV.const_mul L).mono' (((hμ.measurable.comp hx₁).sub (hμ.measurable.comp hx₂)).pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_sq]
    change (μ (x₁ z)-μ (x₂ z))^2 ≤ L*‖x₁ z-x₂ z‖^2
    nlinarith [hb z,sq_nonneg (σ (x₁ z)-σ (x₂ z))]
  have hiH : Integrable (fun z => (σ (x₁ z)-σ (x₂ z))^2) ν := by
    apply (hiV.const_mul L).mono' (((hσ.measurable.comp hx₁).sub (hσ.measurable.comp hx₂)).pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_sq]
    change (σ (x₁ z)-σ (x₂ z))^2 ≤ L*‖x₁ z-x₂ z‖^2
    nlinarith [hb z,sq_nonneg (μ (x₁ z)-μ (x₂ z))]
  refine ⟨(memLp_two_iff_integrable_sq_norm (hx₁.sub hx₂).aestronglyMeasurable).2 hiV,
    (memLp_two_iff_integrable_sq ((hμ.measurable.comp hx₁).sub (hμ.measurable.comp hx₂)).aestronglyMeasurable).2 hiU,
    (memLp_two_iff_integrable_sq ((hσ.measurable.comp hx₁).sub (hσ.measurable.comp hx₂)).aestronglyMeasurable).2 hiH,?_⟩
  rw [← integral_const_mul]
  exact integral_mono (hiU.add hiH) (hiV.const_mul L) hb

/-- The Picard map's coefficient energy is finite even when the coefficients
do not vanish at zero. This supplies the first-iterate and closure hypotheses. -/
theorem coefficient_path_memLp
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (d L : ℝ) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (μ σ : (Fin n → ℝ) → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y, (μ x-μ y)^2+(σ x-σ y)^2 ≤ L*‖x-y‖^2)
    (Y : Ω → C(Icc (0:ℝ) d,Fin n → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) :
    MemLp (fun z : Ω × ℝ => μ (Y z.1 (projIcc 0 d hd z.2))) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) d))) ∧
    MemLp (fun z : Ω × ℝ => σ (Y z.1 (projIcc 0 d hd z.2))) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) d))) := by
  obtain ⟨_,hU,hH,_⟩ := coefficient_difference_energy P d L hd hL μ σ hμ hσ hLip
    Y (fun _ => 0) hm measurable_const hi (memLp_const 0)
  constructor
  · convert hU.add (memLp_const (μ 0)) using 1
    ext z
    simp
  · convert hH.add (memLp_const (σ 0)) using 1
    ext z
    simp

end Asakura.Chapter4.Vector
