import Chapter2ItoCovarianceProcessFormula
import Chapter2OneSidedStoppedCovariance
import Chapter2StochasticIntervalIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Covariance separation proves the stopping-interval identity for the
actual constructed local martingale integrals. The same signed measure is
used for both integrands, and all random evaluation times lie in a fixed
finite horizon, where the covariance formula holds simultaneously. -/
theorem ito_stochastic_interval_identity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hZ : LocalMProcessWitness P F Z) (hH : ∀ ω, Measurable (fun r => H (ω,r)))
    (σ τ : Ω → ℝ) (hσ0 : ∀ ω, 0 ≤ σ ω) (hτ0 : ∀ ω, 0 ≤ τ ω)
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (σ ω) ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (τ ω) ≤ t})
    (hy : ItoCovarianceFormula P F X H Y)
    (hz : ItoCovarianceFormula P F X
      (fun z => (Ioc (σ z.1) (τ z.1)).indicator (fun r => H (z.1,r)) z.2) Z) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      Z t ω = Y (min (realTimeClamp (τ ω)) t) ω - Y (min (realTimeClamp (σ ω)) t) ω := by
  let Ys := fun t ω => Y (min (realTimeClamp (σ ω)) t) ω
  let Yt := fun t ω => Y (min (realTimeClamp (τ ω)) t) ω
  let W := fun t ω => (-1:ℝ)*Ys t ω+Yt t ω
  have hsM := hY.stopped P F hF hle (fun ω => realTimeClamp (σ ω)) hσ
  have htM := hY.stopped P F hF hle (fun ω => realTimeClamp (τ ω)) hτ
  have hW : LocalMProcessWitness P F W := (hsM.smul P F (-1)).add P F hF hle htM
  have hZW : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Z t ω = W t ω := by
    apply local_covariance_separates P F hF hle Z W hZ hW
    intro N hN
    obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X N hX hN
    obtain ⟨D,hD,hDp⟩ := hy.finite_process_formula P F X Y H hY hH N C hN hC
    obtain ⟨E,hE,hEp⟩ := hz N C hN hC
    obtain ⟨Ds,hDs⟩ := local_covariance_witness_exists P F hF hle hnull Ys N hsM hN
    obtain ⟨Dt,hDt⟩ := local_covariance_witness_exists P F hF hle hnull Yt N htM hN
    let K := fun t ω => (-1:ℝ)*Ds t ω+Dt t ω
    have hK : LocalCovarianceWitness P F W N K := hDs.bilinear P F hF hle hDt (-1)
    have hDsE := local_covariance_one_sided_stopping P F hF hle hnull Y N D Ds hY hN hD
      (fun ω => realTimeClamp (σ ω)) hσ hDs
    have hDtE := local_covariance_one_sided_stopping P F hF hle hnull Y N D Dt hY hN hD
      (fun ω => realTimeClamp (τ ω)) hτ hDt
    refine ⟨E,K,hE,hK,?_⟩
    apply local_covariance_common_time_equality P hT F Z N E K hZ hN hE
      (hK.continuous_open_paths P F W N K hW hN)
    intro t ht
    obtain ⟨d,hd0,hdT,rfl⟩ := finite_closed_time_real t ht
    obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hDp d hd0 hdT
    obtain ⟨κ,hκ,hκ0,hκi,hκE⟩ := hEp d hd0 hdT
    filter_upwards [hν0,hνi,hνD,hκ0,hκE,hDsE,hDtE] with ω hn0 hni hnD hk0 hkE hsE htE
    have heq : κ ω = ν ω := signed_measure_ext_positive_Ioc _ _ hk0 hn0
      (fun a b ha hab => (hκ ω a b ha hab).trans (hν ω a b ha hab).symm)
    have hνr : ν ω = (ν ω).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) ω)
        d d hd0 le_rfl (ν ω) (ν ω) hn0 hn0
      all_goals
        intro a b ha hab
        simpa only [real_time_clamp_mono.map_min] using hν ω a b ha hab
    let J := (Ioc (σ ω) (τ ω)).indicator (fun r => H (ω,r))
    have hJ : Measurable J := (hH ω).indicator measurableSet_Ioc
    have hJi : Integrable J (ν ω).totalVariation := hni.indicator measurableSet_Ioc
    have hclip : signedIntegralRaw (ν ω) J = signedCumulative (ν ω) J d := by
      calc
        _ = signedIntegralRaw ((ν ω).restrict (Iic d)) J := congrArg (fun v => signedIntegralRaw v J) hνr
        _ = _ := signed_integral_restrict (ν ω) measurableSet_Iic J hJ hJi.integrableOn
    have hsd := hnD (min (σ ω) d) ⟨le_min (hσ0 ω) hd0,min_le_right _ _⟩
    have htd := hnD (min (τ ω) d) ⟨le_min (hτ0 ω) hd0,min_le_right _ _⟩
    simp only [real_time_clamp_mono.map_min] at hsd htd
    change E (realTimeClamp d) ω = (-1:ℝ)*Ds (realTimeClamp d) ω+Dt (realTimeClamp d) ω
    rw [hkE,heq,hsE _ ht,htE _ ht]
    change signedIntegralRaw (ν ω) J = _
    rw [hclip,signed_cumulative_stochastic_interval (ν ω) _ hni _ _ _ (hστ ω),← hsd,← htd]
    ring
  filter_upwards [hZW] with ω hω
  intro t ht
  have h := hω t ht
  dsimp only [W,Ys,Yt] at h
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_stochastic_interval_identity
