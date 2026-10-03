import Chapter2ElementaryLocalEnergy
import Chapter2QuadraticVariationContinuity
import Chapter2IntegralSquareContinuity
import Chapter2PathMetricProbability
import Chapter2LocalCovarianceCongruence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The actual quadratic variation of the Ito approximation limit is its
Stieltjes square energy at each finite exhaustion time. The elementary
covariations, their probability convergence, and uniqueness of probability
limits are proved upstream; no energy identity of the limit is assumed. -/
theorem ito_approximation_energy_at_horizon
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
    (B : ClosedTime T → Ω → ℝ)
    (hB : LocalCovarianceWitness P F (fun t ω => extendOpenPath (Y ω) t)
      (fun t ω => extendOpenPath (Y ω) t) B)
    (H : Ω → ℝ → ℝ) (j : ℕ)
    (hH : ∀ᵐ ω ∂P, MemLp (H ω) 2
      (intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure)
    (hm : Measurable (fun ω => ∫ r, H ω r^2
      ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure))
    (he : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ ∫ r,
      ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H ω r)^2
      ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) :
    B (realTimeClamp (c j)) =ᵐ[P] fun ω => ∫ r, H ω r^2
      ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure := by
  classical
  let μ := fun ω => (intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
    (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure
  let J := fun n ω r => ∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r
  let W := fun n t ω => ∑ i ∈ Finset.range (N n), V n i ω*
    stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun s => X s ω) t
  have hall n := elementary_grid_local_energy P F hF hle hnull X A hX hA c hc hcm hcT hAm hAc N u V hu hub hVm hVi n j
  choose Q hQ hQi using fun n => (hall n).2
  have hcon n t (ht : t < ⊤) : W n t = fun ω => extendOpenPath (Z n ω) t := by
    funext ω
    dsimp only [extendOpenPath]
    rw [dif_pos ht]
    exact (hZ n ω ⟨t,ht⟩).symm
  have hZM n : LocalMProcessWitness P F (fun t ω => extendOpenPath (Z n ω) t) :=
    (hall n).1.congr_before_terminal P F (hcon n)
  have hZQ n := (hQ n).congr_processes_before_terminal P F (hcon n) (hcon n)
  have hprob := stopped_probability_limit_of_path_metric P (fun n => realTimeClamp (c n)) hct hcut hcc
    Z (fun _ => Y) (fun n => local_martingale_path_measurable P F hle (Z n) (hZM n))
    (fun _ => local_martingale_path_measurable P F hle Y hY) hlim j
  have hqp := quadratic_variation_probability_continuity P F hF hle hnull
    (fun n t ω => extendOpenPath (Z n ω) t) Q (fun t ω => extendOpenPath (Y ω) t) B hZM hY hZQ hB
    (realTimeClamp (c j)) (hcut j) hprob
  have hJ n : ∀ᵐ ω ∂P, MemLp (J n ω) 2 (μ ω) := by
    apply ae_of_all
    intro ω
    letI : IsFiniteMeasure (μ ω) := intervalStieltjes_finite _ _ _ _ _ _
    apply memLp_finsetSum
    intro i hi
    exact (memLp_const (V n i ω)).indicator measurableSet_Ico
  have hsp := square_integral_probability_continuity P μ J H hJ hH hm he
  have hq : TendstoInMeasure P (fun n => Q n (realTimeClamp (c j))) atTop (B (realTimeClamp (c j))) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using hqp
  have hs : TendstoInMeasure P (fun n ω => ∫ r, J n ω r^2 ∂μ ω) atTop (fun ω => ∫ r, H ω r^2 ∂μ ω) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using hsp
  have heq n : Q n (realTimeClamp (c j)) =ᵐ[P] (fun ω => ∫ r, J n ω r^2 ∂μ ω) := hQi n
  exact tendstoInMeasure_ae_unique hq (hs.congr_left (fun n => (heq n).symm))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_approximation_energy_at_horizon
