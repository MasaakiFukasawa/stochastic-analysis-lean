import Chapter5RepresentationExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000

/-- Finite sums of represented, mean-zero variables produce the actual
expectation-centered L² class. The centering constant is derived by integration. -/
theorem finite_integral_representation_centered
    {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : H →ₗᵢ[ℝ] Lp ℝ 2 P) (s : Finset ι)
    (g : ι → Ω → ℝ) (hg : ∀ i,MemLp (g i) 2 P)
    (hmean : ∀ i,(∫ w,g i w ∂P)=0)
    (hreal : ∀ i,∃ x,L x=(hg i).toLp (g i))
    (f : Ω → ℝ) (hf : MemLp f 2 P) (c : ℝ)
    (hrep : f =ᵐ[P] fun w => c+∑ i∈s,g i w) :
    ∃ x,L x=hf.toLp f-(condExpL2 ℝ ℝ bot_le (hf.toLp f) : Lp ℝ 2 P) := by
  classical
  choose x hx using hreal
  have hsum : ((L (∑ i∈s,x i) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun w => ∑ i∈s,g i w := by
    rw [map_sum]
    have he : (∑ i∈s,((L (x i) : Lp ℝ 2 P) : Ω → ℝ)) =ᵐ[P] (∑ i∈s,g i) :=
      eventuallyEq_sum (fun i _ => by rw [hx i]; exact (hg i).coeFn_toLp)
    apply (Lp.coeFn_fun_finsetSum s (fun i => L (x i))).trans
    filter_upwards [he] with w hw
    simpa only [Finset.sum_apply] using hw
  have hgi i : Integrable (g i) P := (hg i).integrable (by norm_num)
  have hsi : Integrable (fun w => ∑ i∈s,g i w) P := integrable_finsetSum s (fun i _ => hgi i)
  have he : (∫ w,f w ∂P)=c := by
    rw [integral_congr_ae hrep,integral_add (integrable_const c) hsi,
      integral_finsetSum s (fun i _ => hgi i)]
    simp [hmean]
  have hc := centered_L2_is_subtract_expectation P (hf.toLp f)
  have hei : (∫ w,(hf.toLp f) w ∂P)=c := (integral_congr_ae hf.coeFn_toLp).trans he
  refine ⟨∑ i∈s,x i,Lp.ext ?_⟩
  filter_upwards [hsum,hc,hf.coeFn_toLp,hrep] with w hsw hcw hfw hrw
  rw [hcw,hfw,hei,hsw,hrw]
  ring

end Asakura.Chapter5
