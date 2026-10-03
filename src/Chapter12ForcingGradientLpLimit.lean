import Chapter12ForcingGradientContinuity
import Chapter12DominatedLpLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem forcing_gradient_Lp_limit {Ω H E K:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]
    (P:Measure Ω) [IsProbabilityMeasure P] (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
    (S:C(K,E) → C(K,E)) (hS:ContDiff ℝ ∞ S)
    (C:ℝ) (hC:0≤C) (hb:∀a,‖fderiv ℝ S a‖≤C)
    (ell:E →L[ℝ] ℝ) (t:K)
    (a:ℕ → Ω → C(K,E)) (b:Ω → C(K,E))
    (ham:∀n,AEStronglyMeasurable (a n) P) (hbm:AEStronglyMeasurable b P)
    (ha:∀ᵐw∂P,Tendsto (fun n => a n w) atTop (𝓝 (b w)))
    (R:ℕ → H →L[ℝ] C(K,E)) (Q:H →L[ℝ] C(K,E)) (hR:Tendsto R atTop (𝓝 Q)) :
    ∃(hm:∀n,MemLp (fun w => forcingGradient S (a n w) (R n) ell t) p P)
      (hg:MemLp (fun w => forcingGradient S (b w) Q ell t) p P),
      Tendsto (fun n => (hm n).toLp _) atTop (𝓝 (hg.toLp _)) := by
  obtain ⟨M,hM⟩ := hR.cauchySeq.isBounded_range.exists_norm_le
  have hM0:0≤M := (norm_nonneg (R 0)).trans (hM _ (mem_range_self 0))
  have hQ:‖Q‖≤M := le_of_tendsto hR.norm (Eventually.of_forall (fun n => hM _ (mem_range_self n)))
  let B := ‖ell.comp (ContinuousMap.evalCLM ℝ t)‖*C*M
  have hB:0≤B := mul_nonneg (mul_nonneg (norm_nonneg _) hC) hM0
  have hgm:AEStronglyMeasurable (fun w => forcingGradient S (b w) Q ell t) P :=
    (forcingGradient_continuous S hS ell t).comp_aestronglyMeasurable (hbm.prodMk aestronglyMeasurable_const)
  have hfm n:AEStronglyMeasurable (fun w => forcingGradient S (a n w) (R n) ell t) P :=
    (forcingGradient_continuous S hS ell t).comp_aestronglyMeasurable ((ham n).prodMk aestronglyMeasurable_const)
  have hfb n w:‖forcingGradient S (a n w) (R n) ell t‖≤B :=
    (forcingGradient_norm_bound S (a n w) (R n) ell t C hC (hb _)).trans
      (mul_le_mul_of_nonneg_left (hM _ (mem_range_self n)) (mul_nonneg (norm_nonneg _) hC))
  have hgb w:‖forcingGradient S (b w) Q ell t‖≤B :=
    (forcingGradient_norm_bound S (b w) Q ell t C hC (hb _)).trans
      (mul_le_mul_of_nonneg_left hQ (mul_nonneg (norm_nonneg _) hC))
  have hm n := MemLp.of_bound (p:=p) (hfm n) B (Eventually.of_forall (hfb n))
  have hg := MemLp.of_bound (p:=p) hgm B (Eventually.of_forall hgb)
  obtain ⟨v,hv⟩ := exists_norm_eq H hB
  refine ⟨hm,hg,?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hm _ hg).mpr
  apply dominated_Lp_limit P p Fact.out hp _ _ (fun _ => v) (memLp_const v) hfm hg
  · intro n
    exact Eventually.of_forall (fun w => by rw [hv];exact hfb n w)
  · filter_upwards [ha] with w hw
    exact forcingGradient_tendsto S hS ell t (fun n => a n w) (b w) hw R Q hR
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcing_gradient_Lp_limit
