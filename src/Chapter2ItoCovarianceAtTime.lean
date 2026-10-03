import Chapter2ItoEnergyIdentification
import Chapter2PathMetricAnyTime
import Chapter2CovarianceAbsoluteContinuity
import Chapter2ItoCovarianceLimit
import Chapter2CanonicalCovarianceData

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The general covariance formula for the actual Ito approximation limit,
with the covariance Stieltjes measure explicitly constructed. -/
theorem ito_approximation_covariance_at_time
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ)
    (hu : ∀ n, StrictMonoOn (u n) (Iic (N n)))
    (hub : ∀ n i, i ≤ N n → u n i ∈ Icc 0 (c n))
    (hVm : ∀ n i, i < N n → Measurable[F (realTimeClamp (u n i))] (V n i))
    (hVi : ∀ n i, i < N n → MemLp (V n i) ∞ P)
    (Z : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ)) (Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hZ : ∀ n ω t, Z n ω t = ∑ i ∈ Finset.range (N n), V n i ω*
      stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun s => X s ω) t.val)
    (hY : LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t))
    (hlim : Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc)
      (Z n ω) (Y ω) ∂P) atTop (𝓝 0))
    (Y0 B C D : ClosedTime T → Ω → ℝ)
    (hY0 : LocalMProcessWitness P F Y0)
    (hB : LocalCovarianceWitness P F Y0 Y0 B)
    (hC : LocalCovarianceWitness P F X Y0 C)
    (hD : LocalCovarianceWitness P F (fun t ω => extendOpenPath (Y ω) t) Y0 D)
    (H : Ω → ℝ → ℝ) (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hAdm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 d))
    (hAdc : ∀ ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 d))
    (hHm : ∀ ω, Measurable (H ω))
    (hBm : ∀ ω, MonotoneOn (fun r => B (realTimeClamp r) ω) (Icc 0 d))
    (hBc : ∀ ω, ContinuousOn (fun r => B (realTimeClamp r) ω) (Icc 0 d))
    (hH : ∀ᵐ ω ∂P, MemLp (H ω) 2
      (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
        (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure)
    (he : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ ∫ r,
      ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H ω r)^2
      ∂(intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
        (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) :
    ∃ ν : Ω → SignedMeasure ℝ,
      (∀ ω a b, 0 ≤ a → a ≤ b → ν ω (Ioc a b) =
        C (min (realTimeClamp b) (realTimeClamp d)) ω-C (min (realTimeClamp a) (realTimeClamp d)) ω) ∧
      (∀ᵐ ω ∂P, (ν ω).totalVariation ≪
        (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
          (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure) ∧
      (∀ᵐ ω ∂P, Integrable (H ω) (ν ω).totalVariation) ∧
      D (realTimeClamp d) =ᵐ[P] fun ω => signedIntegralRaw (ν ω) (H ω) := by
  classical
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  let α := fun ω => (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
    (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure
  let β := fun ω => (intervalStieltjes 0 d hd (fun r => B (realTimeClamp r) ω) (hBm ω)
    (fun r hr => (hBc ω r hr).mono inter_subset_left)).measure
  letI (ω : Ω) : IsFiniteMeasure (α ω) := intervalStieltjes_finite _ _ _ _ _ _
  letI (ω : Ω) : IsFiniteMeasure (β ω) := intervalStieltjes_finite _ _ _ _ _ _
  letI (ω : Ω) : NullSingletonClass (α ω) := interval_stieltjes_no_atoms_on _ _ _ _ _ _ (hAdc ω)
  obtain ⟨ν,hcs,hν,hβ⟩ := canonical_covariance_measure_data P F hF hle hnull X Y0 A B C
    hX hY0 hA hB hC d hd hdT hAdm hBm hAdc hBc
  refine ⟨ν,hν,?_,?_,?_⟩
  · exact hcs.mono (fun ω hω => signed_cs_absolute_continuity (α ω) (β ω) (ν ω) hω)
  · filter_upwards [hcs,hH] with ω hcsω hHω
    have hi := signed_stieltjes_integral_square_bound (α ω) (β ω) (ν ω) hcsω
      (H ω) (fun _ => 1) (hHm ω) measurable_const
      ((memLp_two_iff_integrable_sq hHω.aestronglyMeasurable).1 hHω)
      (by simpa only [one_pow] using integrable_const (1:ℝ))
    simpa only [mul_one] using hi.1
  let a := fun n (i : Fin (N n)) => u n i.val
  let b := fun n (i : Fin (N n)) => u n (i.val+1)
  let G := fun n (i : Fin (N n)) => V n i.val
  have hab n (i : Fin (N n)) : a n i ≤ b n i :=
    (hu n).monotoneOn i.isLt.le (show i.val+1 ∈ Iic (N n) by change i.val+1 ≤ N n; omega) (by omega)
  let W := fun n t ω => ∑ i ∈ Finset.range (N n), V n i ω*
    stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun s => X s ω) t
  have hWM n : LocalMProcessWitness P F (W n) :=
    (elementary_grid_local_energy P F hF hle hnull X A hX hA c hc hcm hcT hAm hAc N u V hu hub hVm hVi n 0).1
  have hcon n t (ht : t < ⊤) : W n t = fun ω => extendOpenPath (Z n ω) t := by
    funext ω
    dsimp only [extendOpenPath]
    rw [dif_pos ht]
    exact (hZ n ω ⟨t,ht⟩).symm
  have hZM n := (hWM n).congr_before_terminal P F (hcon n)
  have hp := stopped_probability_limit_of_path_metric_at_time P (fun n => realTimeClamp (c n)) hct hcut hcc
    Z (fun _ => Y) (fun n => local_martingale_path_measurable P F hle (Z n) (hZM n))
    (fun _ => local_martingale_path_measurable P F hle Y hY) hlim (realTimeClamp d) hdt
  refine ito_covariance_from_elementary_limits P F hF hle hnull X Y0 C B
    (fun t ω => extendOpenPath (Y ω) t) D hX hY0 hY hC hB hD
    (realTimeClamp d) hdt α β ν hcs hβ N a b G hab
    (fun n i => hVm n i.val i.isLt) (fun n i => hVi n i.val i.isLt) ?_ H hHm hH ?_ ?_
  · intro n
    exact .of_forall (fun ω i => hν ω (a n i) (b n i) (hub n i.val i.isLt.le).1 (hab n i))
  · intro δ hδ
    have hsum n ω r := Fin.sum_univ_eq_sum_range
      (fun i => (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r) (N n)
    simpa only [a,b,G,hsum,α] using he δ hδ
  · intro ε hε
    have heq n ω s : (∑ i, G n i ω*(X (min (realTimeClamp (b n i)) (min (realTimeClamp d) s)) ω-
        X (min (realTimeClamp (a n i)) (min (realTimeClamp d) s)) ω)) =
        extendOpenPath (Z n ω) (min (realTimeClamp d) s) := by
      have hh := congrFun (hcon n (min (realTimeClamp d) s) ((min_le_left _ _).trans_lt hdt)) ω
      rw [← hh]
      dsimp only [W,a,b,G,stepIncrement]
      exact Fin.sum_univ_eq_sum_range (fun i => V n i ω*
        (X (min (realTimeClamp (u n (i+1))) (min (realTimeClamp d) s)) ω-
          X (min (realTimeClamp (u n i)) (min (realTimeClamp d) s)) ω)) (N n)
    simpa only [heq] using hp ε hε

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_approximation_covariance_at_time
