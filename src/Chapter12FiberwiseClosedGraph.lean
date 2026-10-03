import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Passing to a joint L2 limit preserves a timewise continuous linear
identity. A subsequence in the time variable converges in the Hilbert space
of random variables, so no point evaluation on an L2 class is assumed continuous. -/
theorem fiberwise_linear_identity_limit {S E H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ν : Measure S) (A : S → E →L[ℝ] H)
    (u : ℕ → Lp E 2 ν) (q : ℕ → Lp H 2 ν) (U : Lp E 2 ν) (Q : Lp H 2 ν)
    (hu : Tendsto u atTop (𝓝 U)) (hq : Tendsto q atTop (𝓝 Q))
    (he : ∀ n,∀ᵐ t ∂ν,q n t=A t (u n t)) :
    ∀ᵐ t ∂ν,Q t=A t (U t) := by
  obtain ⟨ns,hns,hun⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  obtain ⟨ms,hms,hqn⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hq.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ t ∂ν,∀ n,q n t=A t (u n t) := ae_all_iff.mpr he
  filter_upwards [hun,hqn,hall] with t ht hqt het
  have hau := (A t).continuous.continuousAt.tendsto.comp (ht.comp hms.tendsto_atTop)
  have heq : (fun k => q (ns (ms k)) t) = fun k => A t (u (ns (ms k)) t) :=
    funext fun k => het _
  simp only [Function.comp_apply] at hqt
  rw [heq] at hqt
  exact tendsto_nhds_unique hqt hau

end Asakura.Chapter12
