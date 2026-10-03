import Chapter2WeightedBoundedApproximation
import Chapter2WeightedIntegralFormula

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b))
    (hr : ∀ ω x, x ∈ Icc 0 b → ContinuousWithinAt (A ω) (Icc 0 b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω 0 ≤ K)
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)

include hK hF hm hle

/-- Choose an actual elementary process with arbitrarily small expected
pathwise pth-power error under a bounded finite-interval Stieltjes measure. -/
theorem finite_expected_step_approximation
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b)) (hK0 : 0 ≤ K)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (H : Ω × Icc (0:ℝ) b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ q, |H q| ≤ L)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ (N : ℕ) (u : ℕ → Icc (0:ℝ) b) (V : ℕ → Ω → ℝ),
      StrictMonoOn u (Iic N) ∧
      (∀ j < N, Measurable[F (u j)] (V j) ∧ MemLp (V j) ∞ P) ∧
      (∀ q : Ω × Icc (0:ℝ) b, |∑ j ∈ Finset.range N,
        (Ico (u j) (u (j+1))).indicator (fun _ => V j q.1) q.2| ≤ L) ∧
      let R := fun ω => ∫ r,
        |(∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => V j ω)
            (projIcc 0 b hb.le r))-H (ω,projIcc 0 b hb.le r)| ^ p
          ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω) (hr ω)).measure
      Integrable R P ∧ (∫ ω, R ω ∂P) < ε := by
  classical
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
  let μ0 := weightedPathMeasure P 0 b hb.le A hA hr hm
  letI : @IsFiniteMeasure (Ω × Icc (0:ℝ) b) (MeasurableSpace.prod inferInstance inferInstance) μ0 :=
    weighted_path_measure_finite P 0 b hb.le A hA hr hm K hK
  let μ := μ0.trim (progressive_space_le_product F hle)
  letI : IsFiniteMeasure μ := inferInstance
  obtain ⟨N,u,V,hmono,hVm,hVbound,hlim⟩ :=
    weighted_bounded_step_approximation P b hb A hA hr hm K hK F hF hle hc hK0 had hnull
      H hH L hL (.of_forall hbound)
  obtain ⟨k,hk⟩ := ((hlim p hp).eventually (gt_mem_nhds hε)).exists
  let J := fun q : Ω × Icc (0:ℝ) b => ∑ j ∈ Finset.range (N k),
    (Ico (u k j) (u k (j+1))).indicator (fun _ => V k j q.1) q.2
  have hJ : Measurable J := by
    apply Finset.measurable_sum
    intro j hj
    exact progressive_elementary_measurable 0 b F hF _ _ _ ((hVm k j (Finset.mem_range.1 hj)).1)
  let f := fun q => |J q-H q| ^ p
  have hf : Measurable f := by
    convert ((hJ.sub hH).norm.pow_const p) using 1
  have hfi : Integrable f μ := by
    apply Integrable.of_bound hf.aestronglyMeasurable ((2*L)^p)
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    have hj := hVbound k q
    have hh := hbound q
    change |J q| ≤ L at hj
    calc
      |J q-H q| ≤ |J q|+|H q| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (J q) 0 (H q)
      _ ≤ 2*L := by linarith
  refine ⟨N k,u k,V k,hmono k,hVm k,hVbound k,?_,?_⟩
  · exact weighted_progressive_path_integrable P 0 b hb.le A hA hr hm K hK F hle f hf hfi
  · have he := weighted_progressive_integral_formula P 0 b hb.le A hA hr hm K hK F hle f hf hfi
    rw [← he]
    exact hk

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_expected_step_approximation
