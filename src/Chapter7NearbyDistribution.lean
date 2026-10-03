import Chapter7JointClockDistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Bounded Lipschitz tests transfer a law limit between random variables
whose distance tends to zero almost everywhere. No vector-space structure
on the state space is required. -/
theorem nearby_distribution
    {Ω Γ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X Y : ℕ → Ω → E) (Z : Γ → E)
    (hX : ∀ n,Measurable (X n)) (hY : ∀ n,Measurable (Y n))
    (hlim : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hd : ∀ᵐ w ∂P,Tendsto (fun n => dist (X n w) (Y n w)) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z (fun _ => P) Q := by
  refine ⟨fun n => (hY n).aemeasurable,hlim.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hφb hφl
  obtain ⟨C,hC⟩ := hφb
  obtain ⟨L,hL⟩ := hφl
  let e : E := Classical.choice inferInstance
  have hb x : |φ x| ≤ |φ e|+C := by
    have hh := norm_sub_le (φ x-φ e) (-φ e)
    have hbound := hC x e
    rw [Real.dist_eq] at hbound
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,Real.norm_eq_abs] at hh
    linarith
  have hi (V : Ω → E) (hm : Measurable V) : Integrable (fun w => φ (V w)) P :=
    Integrable.of_bound (hL.continuous.measurable.comp hm).aestronglyMeasurable _
      (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hb (V w))
  have hm n : AEStronglyMeasurable (fun w => φ (Y n w)-φ (X n w)) P :=
    ((hL.continuous.measurable.comp (hY n)).sub (hL.continuous.measurable.comp (hX n))).aestronglyMeasurable
  have hbound n : ∀ᵐ w ∂P,‖φ (Y n w)-φ (X n w)‖ ≤ C := by
    exact ae_of_all _ fun w => by simpa only [Real.norm_eq_abs,← Real.dist_eq] using hC (Y n w) (X n w)
  have hp : ∀ᵐ w ∂P,Tendsto (fun n => φ (Y n w)-φ (X n w)) atTop (𝓝 0) := by
    filter_upwards [hd] with w hw
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [mul_zero] using hw.const_mul (L:ℝ))
    simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_comm] using hL.dist_le_mul (Y n w) (X n w)
  have hdiff := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => C)
    hm (integrable_const _) hbound hp
  simp only [integral_zero] at hdiff
  have hbase := tendsto_iff_forall_lipschitz_integral_tendsto.mp hlim.tendsto φ ⟨C,hC⟩ ⟨L,hL⟩
  have hmapX n : (∫ x,φ x ∂P.map (X n)) = ∫ w,φ (X n w) ∂P :=
    integral_map (hX n).aemeasurable hL.continuous.measurable.aestronglyMeasurable
  have hmapY n : (∫ x,φ x ∂P.map (Y n)) = ∫ w,φ (Y n w) ∂P :=
    integral_map (hY n).aemeasurable hL.continuous.measurable.aestronglyMeasurable
  change Tendsto (fun n => ∫ x,φ x ∂P.map (Y n)) atTop (𝓝 (∫ x,φ x ∂Q.map Z))
  change Tendsto (fun n => ∫ x,φ x ∂P.map (X n)) atTop (𝓝 (∫ x,φ x ∂Q.map Z)) at hbase
  simp only [hmapX] at hbase
  have hs := hdiff.add hbase
  simp only [integral_sub (hi _ (hY _)) (hi _ (hX _)),sub_add_cancel,zero_add] at hs
  simpa only [hmapY] using hs

end Asakura.Chapter7
