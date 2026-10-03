import Chapter7JointClockTests
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The actual joint distribution limit for an unchanged marginal law and
a clock converging to a constant. No independence is assumed, and the
spaces need not carry vector-space structures. -/
theorem joint_clock_distribution
    {Ω E H : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nonempty E]
    [MetricSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Ω → E) (A : ℕ → Ω → H) (B0 : Ω → E) (c : H)
    (hB : ∀ n,Measurable (B n)) (hA : ∀ n,Measurable (A n)) (hB0 : Measurable B0)
    (hLaw : ∀ n,IdentDistrib (B n) B0 P P)
    (hp : TendstoInMeasure P A atTop (fun _ => c)) :
    TendstoInDistribution (fun n w => (B n w,A n w)) atTop (fun w => (B0 w,c)) (fun _ => P) P := by
  classical
  refine ⟨fun n => ((hB n).prodMk (hA n)).aemeasurable,
    (hB0.prodMk measurable_const).aemeasurable,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hφb hφl
  obtain ⟨C,hC⟩ := hφb
  obtain ⟨L,hL⟩ := hφl
  let e : E := Classical.choice inferInstance
  have hb x : |φ x| ≤ |φ (e,c)|+C := by
    have hh := norm_sub_le (φ x-φ (e,c)) (-φ (e,c))
    have hbound := hC x (e,c)
    rw [Real.dist_eq] at hbound
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,Real.norm_eq_abs] at hh
    linarith
  have hlim := joint_clock_test_limit P B A c hB hA hp φ hL.uniformContinuous _ hb
  have he n : (∫ w,φ (B n w,c) ∂P) = ∫ w,φ (B0 w,c) ∂P :=
    ((hLaw n).comp (hL.continuous.measurable.comp (measurable_id.prodMk measurable_const))).integral_eq
  simp only [he] at hlim
  have hlim' := hlim.add (tendsto_const_nhds (x := ∫ w,φ (B0 w,c) ∂P))
  simp only [sub_add_cancel,zero_add] at hlim'
  have hmap n : (∫ x,φ x ∂P.map (fun w => (B n w,A n w))) = ∫ w,φ (B n w,A n w) ∂P :=
    integral_map ((hB n).prodMk (hA n)).aemeasurable hL.continuous.measurable.aestronglyMeasurable
  have hmap0 : (∫ x,φ x ∂P.map (fun w => (B0 w,c))) = ∫ w,φ (B0 w,c) ∂P :=
    integral_map (hB0.prodMk measurable_const).aemeasurable hL.continuous.measurable.aestronglyMeasurable
  change Tendsto (fun n => ∫ x,φ x ∂P.map (fun w => (B n w,A n w))) atTop
    (𝓝 (∫ x,φ x ∂P.map (fun w => (B0 w,c))))
  simpa only [hmap,hmap0] using hlim'

end Asakura.Chapter7
