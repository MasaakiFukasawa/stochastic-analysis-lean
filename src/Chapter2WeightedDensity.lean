import Chapter2WeightedOrthogonalityAE
import Chapter2WeightedTestIntegral
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

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

noncomputable def weightedElementaryLp (s t : Icc (0:ℝ) b) (Z : Ω → ℝ)
    (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
    Lp ℝ 2 ((weightedPathMeasure P 0 b hb.le A hA hr hm).trim (progressive_space_le_product F hle)) :=
  (weighted_elementary_memLp_two P 0 b hb.le A hA hr hm K hK F hF hle s t Z hZ hZinf).toLp _

/-- Any closed subspace containing the elementary past-measurable
integrands is the entire progressive Hilbert space. This is the bounded
finite-interval L2 density conclusion of the manuscript proof. -/
theorem weighted_closed_subspace_eq_top
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b)) (hK0 : 0 ≤ K)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
    ∀ V : Submodule ℝ (Lp ℝ 2 ((weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle))), IsClosed V.carrier →
      (∀ s t Z hZ hZinf, weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf ∈ V) →
      V = ⊤ := by
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
  let μ := (weightedPathMeasure P 0 b hb.le A hA hr hm).trim (progressive_space_le_product F hle)
  letI : CompleteSpace (Lp ℝ 2 μ) := weighted_progressive_hilbert_complete P 0 b hb.le A hA hr hm F hle
  intro V hclosed hcontains
  letI : CompleteSpace V := hclosed.isComplete.completeSpace_coe
  apply (Submodule.orthogonal_eq_bot_iff).1
  apply le_antisymm _ bot_le
  intro H hH
  change H = 0
  have hzero : (H : Ω × Icc (0:ℝ) b → ℝ) =ᵐ[μ] 0 := by
    apply weighted_orthogonal_integrand_zero_ae P b hb A hA hr hc hm K hK0 hK F hF hle had
      H (Lp.stronglyMeasurable H).measurable (Lp.memLp H) hnull
    intro s t hst Z hZ hZinf
    have hi := (Submodule.mem_orthogonal V H).1 hH
      (weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf)
      (hcontains s t Z hZ hZinf)
    rw [L2.inner_def] at hi
    have hE := (weighted_elementary_memLp_two P 0 b hb.le A hA hr hm K hK F hF hle s t Z hZ hZinf).coeFn_toLp
    have he : (∫ p, ((Ico s t).indicator (fun _ => Z p.1) p.2) * H p ∂μ) = 0 := by
      calc
        _ = ∫ p, inner ℝ ((weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf) p) (H p) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hE] with p hp
          change _ = H p * _
          rw [show (weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf) p = _ from hp]
          simp only [star_trivial]
          ring
        _ = 0 := hi
    rw [weighted_elementary_test_integral P 0 b hb.le A hA hr hm K hK F hF hle s t Z hZ hZinf
      H (Lp.stronglyMeasurable H).measurable (Lp.memLp H)] at he
    exact he
  apply Lp.ext
  exact hzero.trans (Lp.coeFn_zero ℝ 2 μ).symm

/-- The finite linear span of the actual elementary integrands is dense. -/
theorem weighted_elementary_span_dense
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b)) (hK0 : 0 ≤ K)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
    let S : Set (Lp ℝ 2 ((weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle))) :=
      {J | ∃ (s t : Icc (0:ℝ) b) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P),
        J = weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf}
    Dense (Submodule.span ℝ S).carrier := by
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
  intro S
  apply Submodule.dense_iff_topologicalClosure_eq_top.2
  apply weighted_closed_subspace_eq_top P b hb A hA hr hm K hK F hF hle hc hK0 had hnull
    (Submodule.span ℝ S).topologicalClosure (Submodule.isClosed_topologicalClosure _)
  intro s t Z hZ hZinf
  apply (Submodule.span ℝ S).le_topologicalClosure
  exact Submodule.subset_span ⟨s,t,Z,hZ,hZinf,rfl⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_closed_subspace_eq_top

#print axioms Asakura.Chapter2Complete.weighted_elementary_span_dense
