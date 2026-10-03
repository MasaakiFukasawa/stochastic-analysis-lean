import Chapter2LocalProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- The dominated-convergence martingale step used in Proposition prop244
and in the completeness proof. Conditional expectations are established
from the test-set integrals; no martingale property of the limit is assumed. -/
theorem dominated_continuous_martingale_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ m)
    (X : ℕ → ClosedTime T → Ω → ℝ)
    (hX : ∀ n, ContinuousM2Witness P F (X n))
    (Y : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (Y t))
    (hc : ∀ ω, Continuous (fun t => Y t ω))
    (B : Ω → ℝ) (hB : MemLp B 2 P)
    (hbound : ∀ n t, ∀ᵐ ω ∂P, ‖X n t ω‖ ≤ B ω)
    (hconv : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => X n t ω) atTop (𝓝 (Y t ω))) :
    ContinuousM2Witness P F Y := by
  have hYbound (t) : ∀ᵐ ω ∂P, ‖Y t ω‖ ≤ B ω := by
    filter_upwards [hconv t, ae_all_iff.2 (fun n => hbound n t)] with ω hω hb
    exact le_of_tendsto hω.norm (Filter.Eventually.of_forall hb)
  have hY2 (t) : MemLp (Y t) 2 P := by
    apply hB.of_le ((hm t).mono (hle t) le_rfl).aestronglyMeasurable
    filter_upwards [hYbound t] with ω hω
    exact hω.trans (le_abs_self (B ω))
  refine ⟨hm,hY2,hc,?_,?_⟩
  · intro s t hst
    apply Filter.EventuallyEq.symm
    apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) ((hY2 t).integrable (by norm_num))
      (fun _ _ _ => ((hY2 s).integrable (by norm_num)).integrableOn) _
      (hm s).stronglyMeasurable.aestronglyMeasurable
    intro A hA _
    have hAm := hle s _ hA
    have hlim (r : ClosedTime T) : Tendsto (fun n => ∫ ω in A, X n r ω ∂P)
        atTop (𝓝 (∫ ω in A, Y r ω ∂P)) := by
      apply tendsto_integral_of_dominated_convergence B
        (fun n => ((hX n).moment r).aestronglyMeasurable.restrict)
        (hB.integrable (by norm_num)).integrableOn
        (fun n => ae_restrict_of_ae (hbound n r))
        (ae_restrict_of_ae (hconv r))
    have he (n) : (∫ ω in A, X n s ω ∂P) = ∫ ω in A, X n t ω ∂P := by
      calc
        _ = ∫ ω in A, P[X n t | F s] ω ∂P :=
          setIntegral_congr_ae hAm (((hX n).martingale s t hst).symm.mono fun ω hω _ => hω)
        _ = _ := setIntegral_condExp (hle s) (((hX n).moment t).integrable (by norm_num)) hA
    have hls := hlim s
    simp only [he] at hls
    exact tendsto_nhds_unique hls (hlim t)
  · filter_upwards [hconv ⊥, ae_all_iff.2 (fun n => (hX n).initial)] with ω hω hz
    have hzero : Tendsto (fun n => X n ⊥ ω) atTop (𝓝 (0:ℝ)) := by
      simpa only [hz, Pi.zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hω hzero

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.dominated_continuous_martingale_limit
