import Chapter2WeightedL2Approximation
import Chapter2ClippedApproximation

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

include hK hF

/-- The bounded finite-interval part of the manuscript density lemma,
with an actual sequence of elementary processes and every finite positive
Lp error limit. Hilbert density, finite representations and clipping are
all constructed in the preceding checked proofs. -/
theorem weighted_bounded_step_approximation
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b)) (hK0 : 0 ≤ K)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
    let μ := (weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle)
    ∀ (H : Ω × Icc (0:ℝ) b → ℝ), Measurable H →
    ∀ L ≥ 0, (∀ᵐ p ∂μ, |H p| ≤ L) →
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → Icc (0:ℝ) b) (V : ℕ → ℕ → Ω → ℝ),
      (∀ k, StrictMonoOn (u k) (Iic (N k))) ∧
      (∀ k j, j < N k → Measurable[F (u k j)] (V k j) ∧ MemLp (V k j) ∞ P) ∧
      (∀ k (q : Ω × Icc (0:ℝ) b), |∑ j ∈ Finset.range (N k),
        (Ico (u k j) (u k (j+1))).indicator (fun _ => V k j q.1) q.2| ≤ L) ∧
      ∀ (p : ℝ), p > 0 → Tendsto (fun k => ∫ q,
        |(∑ j ∈ Finset.range (N k),
          (Ico (u k j) (u k (j+1))).indicator (fun _ => V k j q.1) q.2)-H q| ^ p ∂μ)
        atTop (𝓝 0) := by
  classical
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
  intro μ H hH L hL hbound
  let μ0 := weightedPathMeasure P 0 b hb.le A hA hr hm
  letI : @IsFiniteMeasure (Ω × Icc (0:ℝ) b) (MeasurableSpace.prod inferInstance inferInstance) μ0 :=
    weighted_path_measure_finite P 0 b hb.le A hA hr hm K hK
  letI : IsFiniteMeasure μ := inferInstance
  have hH2 : MemLp H 2 μ := MemLp.of_bound hH.aestronglyMeasurable L
    (by simpa only [Real.norm_eq_abs] using hbound)
  obtain ⟨n,a,d,G,hord,hadapt,hG,herr,hlim⟩ :=
    weighted_L2_step_approximation P b hb A hA hr hm K hK F hF hle hc hK0 had hnull H hH2
  let J := fun k (q : Ω × Icc (0:ℝ) b) => ∑ i, (Ico (a k i) (d k i)).indicator (fun _ => G k i q.1) q.2
  have hJm (k) : Measurable (J k) := by
    apply Finset.measurable_sum
    intro i hi
    exact progressive_elementary_measurable 0 b F hF (a k i) (d k i) (G k i) (hadapt k i)
  have hex (k) := finite_adapted_step_clipping P F hF hle Finset.univ (a k) (d k) (G k)
    (fun i _ => hord k i) (fun i _ => hadapt k i) ⊥ L hL
  choose N u V hmono hVm he using hex
  refine ⟨N,u,V,hmono,hVm,?_,?_⟩
  · intro k q
    rw [← he k q.1 q.2]
    exact abs_le.2 ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  intro p hp
  have h := clipped_L2_approximation_all_exponents μ H J hH.aestronglyMeasurable
    (fun k => (hJm k).aestronglyMeasurable) herr L hL hbound hlim p hp
  convert h using 1
  funext k
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  dsimp only [J]
  rw [he k q.1 q.2]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_bounded_step_approximation
