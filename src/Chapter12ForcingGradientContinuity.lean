import Chapter12ForcingGradientRiesz

open Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {H E K:Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]

theorem forcingGradient_continuous
    (S:C(K,E) → C(K,E)) (hS:ContDiff ℝ ∞ S) (ell:E →L[ℝ] ℝ) (t:K) :
    Continuous (fun ar:C(K,E)×(H →L[ℝ] C(K,E)) => forcingGradient S ar.1 ar.2 ell t) := by
  unfold forcingGradient
  apply (InnerProductSpace.toDual ℝ H).symm.continuous.comp
  exact continuous_const.clm_comp
    (((hS.fderiv_right (m:=∞) (by simp)).continuous.comp continuous_fst).clm_comp continuous_snd)

theorem forcingGradient_norm_bound
    (S:C(K,E) → C(K,E)) (a:C(K,E)) (R:H →L[ℝ] C(K,E))
    (ell:E →L[ℝ] ℝ) (t:K) (C:ℝ) (hC:0≤C) (hb:‖fderiv ℝ S a‖≤C) :
    ‖forcingGradient S a R ell t‖≤‖ell.comp (ContinuousMap.evalCLM ℝ t)‖*C*‖R‖ := by
  rw [forcingGradient,LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖ell.comp (ContinuousMap.evalCLM ℝ t)‖*‖(fderiv ℝ S a).comp R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖ell.comp (ContinuousMap.evalCLM ℝ t)‖*(C*‖R‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by ring

attribute [local irreducible] forcingGradient

theorem forcingGradient_tendsto
    (S:C(K,E) → C(K,E)) (hS:ContDiff ℝ ∞ S) (ell:E →L[ℝ] ℝ) (t:K)
    (a:ℕ → C(K,E)) (b:C(K,E)) (ha:Tendsto a atTop (𝓝 b))
    (R:ℕ → (H →L[ℝ] C(K,E))) (Q:H →L[ℝ] C(K,E)) (hR:Tendsto R atTop (𝓝 Q)) :
    Tendsto (fun n => forcingGradient S (a n) (R n) ell t) atTop (𝓝 (forcingGradient S b Q ell t)) := by
  let f : C(K,E) × (H →L[ℝ] C(K,E)) → H :=
    fun ar => forcingGradient S ar.1 ar.2 ell t
  have hf : Continuous f := forcingGradient_continuous (H:=H) (E:=E) (K:=K) S hS ell t
  have hp : Tendsto (fun n => (a n, R n)) atTop (𝓝 (b,Q)) := ha.prodMk_nhds hR
  exact (hf.tendsto (b,Q)).comp hp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcingGradient_tendsto
