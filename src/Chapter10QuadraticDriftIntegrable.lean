import Chapter10LinearDriftFubini

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The L2 norm of the actual continuous state dominates each quadratic
drift on a compact time interval, giving the product-space integrability
needed for conditional Fubini. -/
theorem quadratic_drift_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (T : ℝ) (hT : 0≤T) (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hm : Measurable X) (hX : MemLp X 2 P)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (i j : Fin d) (s t : Icc (0:ℝ) T) :
    Integrable (fun z : Ω × ℝ => X z.1 (projIcc 0 T hT z.2) j*
      (A z.2 (X z.1 (projIcc 0 T hT z.2))) i)
      (P.prod (volume.restrict (Ioc s.val t.val))) := by
  let U := fun u w => X w (projIcc 0 T hT u)
  have hUc w : Continuous (fun u => U u w) := (X w).continuous.comp continuous_projIcc
  have hUm u : Measurable (U u) := (continuous_eval_const _).measurable.comp hm
  have hRc w : Continuous (fun u => U u w j*(A u (U u w)) i) :=
    ((continuous_apply j).comp (hUc w)).mul
      ((continuous_apply i).comp (hA.clm_apply (hUc w)))
  have hRm u : Measurable (fun w => U u w j*(A u (U u w)) i) :=
    ((measurable_pi_apply j).comp (hUm u)).mul
      ((measurable_pi_apply i).comp ((A u).continuous.measurable.comp (hUm u)))
  have hjoint := (measurable_uncurry_of_continuous_of_measurable hRc hRm).comp measurable_swap
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K := max C 0
  let ν := volume.restrict (Ioc s.val t.val)
  apply ((hX.norm.integrable_sq.const_mul K).comp_fst ν).mono' hjoint.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with z hz
  have hu : z.2∈Icc (0:ℝ) T := ⟨s.property.1.trans hz.1.le,hz.2.trans t.property.2⟩
  have hx : ‖U z.2 z.1‖≤‖X z.1‖ := (X z.1).norm_coe_le_norm _
  have hj : ‖U z.2 z.1 j‖≤‖X z.1‖ := (norm_le_pi_norm _ j).trans hx
  have ha : ‖(A z.2 (U z.2 z.1)) i‖≤K*‖X z.1‖ :=
    (norm_le_pi_norm _ i).trans (((A z.2).le_opNorm _).trans
      (mul_le_mul ((hC _ hu).trans (le_max_left C 0)) hx (norm_nonneg _) (le_max_right C 0)))
  change ‖U z.2 z.1 j*(A z.2 (U z.2 z.1)) i‖≤K*‖X z.1‖^2
  rw [norm_mul]
  have hh := mul_le_mul hj ha (norm_nonneg _) (norm_nonneg (X z.1))
  nlinarith

end Asakura.Chapter10
