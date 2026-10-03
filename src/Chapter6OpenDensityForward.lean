import Chapter6OpenDensityBounded
import Chapter6LocalFromStopped

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Forward local-martingale product criterion on the manuscript’s half-open density interval.
The Q-localizers are used first, then bounded P-localizers are constructed. -/
theorem open_density_times_local_martingale
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (M X : ClosedTime T → Ω → ℝ)
    (hMa : ∀ t,Measurable[F t] (M t)) (hMc : ∀ w t,t < ⊤ → ContinuousAt (fun s => M s w) t)
    (hME : ∀ t,M t =ᵐ[P] P[(fun w => (d w : ℝ))|F t])
    (hXa : ∀ t,Measurable[F t] (X t))
    (hX : LocalMProcessWitness Q F X)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n,u n < ⊤)
    (huc : ∀ t,t < ⊤ → ∃ n,t < u n) :
    LocalMProcessWitness P F (fun t w => M t w*X t w) := by
  obtain ⟨τ,hs,hm,ht,hco,hb⟩ := hX.localizers
  have hzeroQ : X ⊥ =ᵐ[Q] 0 := by simpa only [min_bot_right] using (hb 0).1.initial
  have hzeroP : X ⊥ =ᵐ[P] 0 := by
    rw [hQ] at hzeroQ
    exact (positive_density_ae_iff P d hd hp _).mp hzeroQ
  have hy0 : (fun w => M ⊥ w*X ⊥ w) =ᵐ[P] 0 := by
    filter_upwards [hzeroP] with w hw
    simp only [hw,Pi.zero_apply,mul_zero]
  apply local_of_local_stopped P hT F hF hle _
    (fun t => (hMa t).mul (hXa t))
    (fun w t htt => (hMc w t htt).mul (hX.path Q F w t htt))
    hy0 τ hm hco
  intro n
  have hl := open_density_times_martingale_local P Q hT F hF hle d hd hdi hp hQ M
    (fun t w => X (min (τ n w) t) w) hMa hMc hME (hb n).1.adapted (hb n).1.path
    (fun t => ((hb n).1.moment t).integrable (by norm_num))
    (hb n).1.martingale (hb n).1.initial u hu hut huc
  have hh := hl.stopped P F hF hle (τ n) (hs n)
  simpa [min_assoc] using hh

end Asakura.Chapter6
