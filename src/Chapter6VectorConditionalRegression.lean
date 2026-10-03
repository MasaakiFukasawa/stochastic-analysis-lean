import Chapter6WeightedConditionalRegression

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem vector_weighted_conditional_regression {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (X Y b : Fin d → Ω → ℝ) (hX : ∀ i,Integrable (X i) P) (hY : ∀ i,Integrable (Y i) P)
    (G H : MeasurableSpace Ω) (hGH : G≤H) (hH : H≤m)
    (hb : ∀ i,Measurable[H] (b i)) (K : ℝ) (hbb : ∀ i,∀ᵐ w ∂P,‖b i w‖≤K)
    (he : ∀ i,P[X i|H]=ᵐ[P] Y i) :
    P[(fun w => ∑ i,b i w*X i w)|G]=ᵐ[P] P[(fun w => ∑ i,b i w*Y i w)|G] := by
  letI : MeasurableSpace Ω := m
  have hm i : AEStronglyMeasurable (b i) P := ((hb i).mono hH le_rfl).aestronglyMeasurable
  have hiX i := (hX i).bdd_mul (hm i) (hbb i)
  have hiY i := (hY i).bdd_mul (hm i) (hbb i)
  have hx := condExp_finsetSum (s := univ) (fun i _ => hiX i) G
  have hy := condExp_finsetSum (s := univ) (fun i _ => hiY i) G
  have hr i := weighted_conditional_regression P G H hGH hH (X i) (Y i) (b i) (hX i) (hb i) K (hbb i) (he i)
  filter_upwards [hx,hy,ae_all_iff.2 hr] with w hx hy hr
  simp only [Finset.sum_fn,Finset.sum_apply,Pi.mul_apply] at hx hy
  rw [hx,hy]
  exact sum_congr rfl (fun i _ => hr i)

end Asakura.Chapter6
