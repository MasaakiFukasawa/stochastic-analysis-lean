import Chapter6L2WeightedRegression

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem vector_L2_weighted_conditional_regression {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (X Y b : Fin d → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 P) (hY : ∀ i,MemLp (Y i) 2 P)
    (G H : MeasurableSpace Ω) (hGH : G≤H) (hH : H≤m)
    (hb : ∀ i,Measurable[H] (b i)) (hbb : ∀ i,MemLp (b i) 2 P)
    (he : ∀ i,P[X i|H]=ᵐ[P] Y i) :
    P[(fun w => ∑ i,b i w*X i w)|G]=ᵐ[P] P[(fun w => ∑ i,b i w*Y i w)|G] := by
  letI : MeasurableSpace Ω := m
  have hiX i := (hbb i).integrable_mul (hX i)
  have hiY i := (hbb i).integrable_mul (hY i)
  have hx := condExp_finsetSum (s := univ) (fun i _ => hiX i) G
  have hy := condExp_finsetSum (s := univ) (fun i _ => hiY i) G
  have hr i := L2_weighted_conditional_regression P (X i) (Y i) (b i) (hX i) (hY i) (hbb i) G H hGH hH (hb i) (he i)
  filter_upwards [hx,hy,ae_all_iff.2 hr] with w hx hy hr
  simp only [Finset.sum_fn,Finset.sum_apply,Pi.mul_apply] at hx hy
  rw [hx,hy]
  exact sum_congr rfl (fun i _ => hr i)

end Asakura.Chapter6
