import Chapter2ElementaryDifferenceEnergy
import Chapter2LocalCovarianceCongruence
import Chapter2QuadraticCauchyLimit
import Chapter2ApproximationCauchy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Construct an actual local martingale as the limit of actual elementary
Ito integrals approximating H. The proof supplies the difference quadratic
variations, Lenglart estimates, two-index Cauchy argument and M_loc limit. -/
theorem elementary_approximation_local_martingale_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
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
    (H : Ω → ℝ → ℝ)
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r =>
      ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H ω r)^2)
      (intervalStieltjes 0 (c n) (hc n) (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (hprob : ∀ j (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ ∫ r,
      ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H ω r)^2
      ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) :
    ∃ (Z : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ)) (Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ)),
      (∀ n ω t, Z n ω t = ∑ i ∈ Finset.range (N n), V n i ω*
        stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun s => X s ω) t.val) ∧
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) ∧
      Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc)
        (Z n ω) (Y ω) ∂P) atTop (𝓝 0) := by
  classical
  let J := fun n ω r => ∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r
  let μ := fun j ω => (intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
    (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure
  let Z := fun n t ω => ∑ i ∈ Finset.range (N n), V n i ω*
    stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun t => X t ω) t
  have hZ n : LocalMProcessWitness P F (Z n) :=
    (real_elementary_grid_energy P F hF hle hnull X A hX hA (c n) (hc n) (hcT n) (hAm n)
      (N n) (u n) (hu n) (hub n) (V n) (hVm n) (hVi n)).1
  let Zp := fun n ω => localOpenPath P F (hZ n) ω
  have hZp n : LocalMProcessWitness P F (fun t ω => extendOpenPath (Zp n ω) t) := local_open_path_witness P F (hZ n)
  have hpair := elementary_difference_energy P F hF hle hnull X A hX hA c hc hcm.monotone hcT hAm hAc N u V hu hub hVm hVi
  choose Q hQ hQi using hpair
  have heZp n t (ht : t < ⊤) ω : extendOpenPath (Zp n ω) t = Z n t ω := by
    simp only [extendOpenPath,dif_pos ht]
    rfl
  have hQp n k : LocalCovarianceWitness P F
      (fun t ω => extendOpenPath (Zp n ω) t-extendOpenPath (Zp k ω) t)
      (fun t ω => extendOpenPath (Zp n ω) t-extendOpenPath (Zp k ω) t) (Q n k) := by
    apply (hQ n k).congr_processes_before_terminal P F
    · intro t ht
      funext ω
      rw [heZp n t ht ω,heZp k t ht ω]
    · intro t ht
      funext ω
      rw [heZp n t ht ω,heZp k t ht ω]
  have hsmall (a b : ℕ → ℕ) (ha : ∀ n, n ≤ a n) (hb : ∀ n, n ≤ b n)
      (j : ℕ) (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => P {ω | δ ≤ Q (a n) (b n) (realTimeClamp (c j)) ω}) atTop (𝓝 0) := by
    have hai : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
    have hbi : Tendsto b atTop atTop := tendsto_atTop_mono hb tendsto_id
    have hij : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, Integrable (fun r => (J n ω r-H ω r)^2) (μ j ω) := by
      filter_upwards [eventually_ge_atTop j] with n hjn
      filter_upwards [hi n] with ω hiω
      have hr := interval_stieltjes_restrict_Iic 0 (c n) (c j) (hc j) (hcm.monotone hjn)
        (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)
      change Integrable _ (intervalStieltjes 0 (c j) (hc j) _ _ _).measure
      rw [hr]
      exact hiω.integrableOn
    have hl := square_error_tail_difference_limit P (μ j) J H hij (hprob j) a b hai hbi δ hδ
    have he : (fun n => P {ω | δ ≤ Q (a n) (b n) (realTimeClamp (c j)) ω}) =ᶠ[atTop]
        (fun n => P {ω | δ ≤ ∫ r, (J (a n) ω r-J (b n) ω r)^2 ∂μ j ω}) := by
      filter_upwards [eventually_ge_atTop j] with n hjn
      apply measure_congr
      filter_upwards [hQi (a n) (b n)] with ω hω
      change (δ ≤ Q (a n) (b n) (realTimeClamp (c j)) ω) = _
      rw [hω j (hjn.trans ((ha n).trans (le_max_left _ _)))]
    exact hl.congr' he.symm
  obtain ⟨Y,hY,hlim⟩ := local_martingale_limit_of_quadratic_cauchy P hT F hF hle hnull
    (fun n => realTimeClamp (c n)) hct hcut hcc Zp hZp Q hQp hsmall
  exact ⟨Zp,Y,(fun _ _ _ => rfl),hY,hlim⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_approximation_local_martingale_limit
