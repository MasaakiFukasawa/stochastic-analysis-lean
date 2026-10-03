import Chapter4VectorBorelCoefficientDomain

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma real_borel_coefficient_domain
    {Ω : Type*} [MeasurableSpace Ω] {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ℝ → Ω → Fin dim → ℝ) (hm : ∀ r,Measurable (X r))
    (hc : ∀ w,Continuous (fun r => X r w))
    (ha : ∀ r,0≤r → Measurable[F (realTimeClamp r)] (X r))
    (b : (Fin dim → ℝ) → ℝ) (hb : Measurable b)
    (L : ℝ) (hL : 0≤L) (hg : ∀ x,(b x)^2≤L*(1+‖x‖^2)) :
    let H := fun z : Ω × ℝ => b (X z.2 z.1)
    Measurable H ∧
    (∀ c,0≤c → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) c => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) c => H (z.1,z.2.val))) ∧
    (∀ c,0≤c → ∀ w,IntervalIntegrable (fun r => H (w,r)^2) volume 0 c) := by
  have hHm : Measurable (fun z : Ω × ℝ => b (X z.2 z.1)) :=
    hb.comp ((measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap)
  refine ⟨hHm,?_,?_⟩
  · intro c hc0
    letI : MeasurableSpace (Ω × Icc (0:ℝ) c) := progressiveSpace (fun t : Icc (0:ℝ) c => F (realTimeClamp t.val))
    apply hb.comp
    apply measurable_pi_iff.mpr
    intro i
    exact continuous_adapted_real_progressive F hF (fun z => X z.2 z.1 i) c hc0
      (fun r hr => (measurable_pi_apply i).comp (ha r hr.1))
      (fun w => ((continuous_apply i).comp (hc w)).continuousOn)
  · intro c hc0 w
    let Y : C(Icc (0:ℝ) c,Fin dim → ℝ) := ⟨fun r => X r.val w,(hc w).comp continuous_subtype_val⟩
    have hme : Measurable (fun r => b (X r w)^2) :=
      (hHm.comp (measurable_const.prodMk measurable_id)).pow_const 2
    have hbound : ∀ᵐ r ∂volume.restrict (Ioc (0:ℝ) c),|b (X r w)^2|≤L*(1+‖Y‖^2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [abs_of_nonneg (sq_nonneg _)]
      apply (hg _).trans
      apply mul_le_mul_of_nonneg_left _ hL
      apply add_le_add le_rfl
      exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm Y ⟨r,hr.1.le,hr.2⟩) 2
    constructor
    · exact (integrable_const (L*(1+‖Y‖^2))).mono' hme.aestronglyMeasurable hbound
    · change Integrable _ (volume.restrict (Ioc c 0))
      rw [Ioc_eq_empty_of_le hc0,Measure.restrict_empty]
      exact integrable_zero_measure

end Asakura.Chapter4.Vector
