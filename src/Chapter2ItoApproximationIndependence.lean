import Chapter2IndexedDifferenceEnergy
import Chapter2ApproximationPair
import Chapter2LocalCovarianceCongruence
import Chapter2QuadraticCauchyLimit
import Chapter2PathLimitUniqueness

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Independence of the actual elementary approximation sequence in the
Ito construction. Both families approximate the same H; the conclusion is
indistinguishability of their local-martingale limits on [0,T). -/
theorem ito_approximation_limits_independent
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
    (N : Bool → ℕ → ℕ) (u : Bool → ℕ → ℕ → ℝ) (V : Bool → ℕ → ℕ → Ω → ℝ)
    (hu : ∀ q n, StrictMonoOn (u q n) (Iic (N q n)))
    (hub : ∀ q n i, i ≤ N q n → u q n i ∈ Icc 0 (c n))
    (hVm : ∀ q n i, i < N q n → Measurable[F (realTimeClamp (u q n i))] (V q n i))
    (hVi : ∀ q n i, i < N q n → MemLp (V q n i) ∞ P)
    (H : Ω → ℝ → ℝ)
    (hi : ∀ q n, ∀ᵐ ω ∂P, Integrable (fun r =>
      ((∑ i ∈ Finset.range (N q n), (Ico (u q n i) (u q n (i+1))).indicator (fun _ => V q n i ω) r)-H ω r)^2)
      (intervalStieltjes 0 (c n) (hc n) (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (hprob : ∀ q j (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ ∫ r,
      ((∑ i ∈ Finset.range (N q n), (Ico (u q n i) (u q n (i+1))).indicator (fun _ => V q n i ω) r)-H ω r)^2
      ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0))
    (Z : Bool → ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hgain : ∀ q n ω t, Z q n ω t = ∑ i ∈ Finset.range (N q n), V q n i ω*
      stepIncrement (realTimeClamp (u q n i)) (realTimeClamp (u q n (i+1))) (fun s => X s ω) t.val)
    (Y : Bool → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hY : ∀ q, LocalMProcessWitness P F (fun t ω => extendOpenPath (Y q ω) t))
    (hlim : ∀ q, Tendsto (fun n => ∫ ω,
      pathDistance (intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc) (Z q n ω) (Y q ω) ∂P)
      atTop (𝓝 0)) : Y false =ᵐ[P] Y true := by
  classical
  let K := intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  let J := fun q n ω r => ∑ i ∈ Finset.range (N q n),
    (Ico (u q n i) (u q n (i+1))).indicator (fun _ => V q n i ω) r
  let W := fun q n t ω => ∑ i ∈ Finset.range (N q n), V q n i ω*
    stepIncrement (realTimeClamp (u q n i)) (realTimeClamp (u q n (i+1))) (fun s => X s ω) t
  let μ := fun j ω => (intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
    (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure
  have heZ q n t (ht : t < ⊤) ω : extendOpenPath (Z q n ω) t = W q n t ω := by
    simp only [extendOpenPath,dif_pos ht]
    exact hgain q n ω ⟨t,ht⟩
  have hW q n : LocalMProcessWitness P F (W q n) :=
    (real_elementary_grid_energy P F hF hle hnull X A hX hA (c n) (hc n) (hcT n) (hAm n)
      (N q n) (u q n) (hu q n) (hub q n) (V q n) (hVm q n) (hVi q n)).1
  have hZ q n : LocalMProcessWitness P F (fun t ω => extendOpenPath (Z q n ω) t) := by
    apply (hW q n).congr_before_terminal P F
    intro t ht
    exact funext (fun ω => (heZ q n t ht ω).symm)
  have hip q j : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, Integrable (fun r => (J q n ω r-H ω r)^2) (μ j ω) := by
    filter_upwards [eventually_ge_atTop j] with n hjn
    filter_upwards [hi q n] with ω hiω
    have hr := interval_stieltjes_restrict_Iic 0 (c n) (c j) (hc j) (hcm hjn)
      (fun r => A (realTimeClamp r) ω) (hAm n ω)
      (fun r hr => (hAc n ω r hr).mono inter_subset_left) (hAm j ω)
      (fun r hr => (hAc j ω r hr).mono inter_subset_left)
    change Integrable _ (intervalStieltjes 0 (c j) (hc j) _ _ _).measure
    rw [hr]
    exact hiω.integrableOn
  have hpair := indexed_elementary_difference_energy P F hF hle hnull X A hX hA c hc hcm hcT hAm hAc
    (fun z : Bool × ℕ => z.2) (fun z => N z.1 z.2) (fun z => u z.1 z.2) (fun z => V z.1 z.2)
    (fun z => hu z.1 z.2) (fun z => hub z.1 z.2) (fun z => hVm z.1 z.2) (fun z => hVi z.1 z.2)
  have hex n := hpair (false,n) (true,n)
  choose Q hQ hQi using hex
  let D := fun n t ω => extendOpenPath (Z false n ω) t-extendOpenPath (Z true n ω) t
  have hD n : LocalMProcessWitness P F (D n) := by
    have h := (hZ false n).add P F hF hle ((hZ true n).smul P F (-1))
    convert h using 1
    funext t ω
    change _-_ = _+(-1)*_
    ring
  have hQd n : LocalCovarianceWitness P F (D n) (D n) (Q n) := by
    apply (hQ n).congr_processes_before_terminal P F
    · intro t ht
      funext ω
      change W false n t ω-W true n t ω = extendOpenPath (Z false n ω) t-extendOpenPath (Z true n ω) t
      rw [heZ false n t ht ω,heZ true n t ht ω]
    · intro t ht
      funext ω
      change W false n t ω-W true n t ω = extendOpenPath (Z false n ω) t-extendOpenPath (Z true n ω) t
      rw [heZ false n t ht ω,heZ true n t ht ω]
  have hQsmall j δ (hδ : 0 < δ) : Tendsto (fun n => P {ω | δ ≤ Q n (realTimeClamp (c j)) ω}) atTop (𝓝 0) := by
    have hl := square_error_two_approximations_limit P (μ j) (J false) (J true) H
      (hip false j) (hprob false j) (hip true j) (hprob true j) δ hδ
    have he : (fun n => P {ω | δ ≤ Q n (realTimeClamp (c j)) ω}) =ᶠ[atTop]
        (fun n => P {ω | δ ≤ ∫ r, (J false n ω r-J true n ω r)^2 ∂μ j ω}) := by
      filter_upwards [eventually_ge_atTop j] with n hjn
      apply measure_congr
      filter_upwards [hQi n] with ω hω
      change (δ ≤ Q n (realTimeClamp (c j)) ω) = _
      rw [hω j (by simpa only [max_self] using hjn)]
    exact hl.congr' he.symm
  have hdist : Tendsto (fun n => ∫ ω, pathDistance K (Z false n ω) (Z true n ω) ∂P) atTop (𝓝 0) := by
    apply path_metric_limit_of_probability P K (Z false) (Z true)
      (fun n => local_martingale_path_measurable P F hle (Z false n) (hZ false n))
      (fun n => local_martingale_path_measurable P F hle (Z true n) (hZ true n))
    intro j ε hε
    have hσ t : MeasurableSet[F t] {ω : Ω | realTimeClamp (c j) ≤ t} := by
      by_cases ht : realTimeClamp (c j) ≤ t <;> simp [ht]
    have hl := local_martingale_probability_of_quadratic_variation P F hF hle hnull D Q hD hQd
      (fun _ => realTimeClamp (c j)) hσ (fun _ => hcut j) (hQsmall j) ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => bot_le)
    intro n
    apply measure_mono
    intro ω hω
    exact hω.trans (interval_stage_distance_le_stopped_sup (fun n => realTimeClamp (c n)) hct hcut hcc
      (Z false n ω) (Z true n ω) j)
  exact expected_path_limits_equal P K (Z false) (Z true) (Y false) (Y true)
    (fun n => local_martingale_path_measurable P F hle (Z false n) (hZ false n))
    (fun n => local_martingale_path_measurable P F hle (Z true n) (hZ true n))
    (local_martingale_path_measurable P F hle (Y false) (hY false))
    (local_martingale_path_measurable P F hle (Y true) (hY true)) (hlim false) (hlim true) hdist

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_approximation_limits_independent
