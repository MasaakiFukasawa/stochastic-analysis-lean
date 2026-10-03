import Chapter3RegularizedBDGReverseSmallP
import Chapter3RunningMaximum
import Chapter3ShiftedMomentLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The full reverse small-p BDG argument with the actual running maximum and alpha limit. -/
theorem bdg_reverse_small_p_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 0 < p) (hp2 : p < 2)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K)
    (L : ℝ) (hL : 0 ≤ L)
    (hXbound : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |X s ω| ≤ L) :
    Integrable (fun ω => runningMaximum X (hX.path P F) b ω^p) P ∧
    Integrable (fun ω => A b ω^(p/2)) P ∧
    (∫ ω, A b ω^(p/2) ∂P) ≤ (2/p)^p*(∫ ω, runningMaximum X (hX.path P F) b ω^p ∂P) := by
  let R := runningMaximum X (hX.path P F)
  have hRa := runningMaximum_adapted F hF X (hX.path P F) (hX.adapted P F)
  have hRc := runningMaximum_continuous hT X (hX.path P F)
  have hRm := runningMaximum_monotone X (hX.path P F)
  have hRp ω t (ht : t < ⊤) : 0 ≤ R t ω := runningMaximum_nonneg X (hX.path P F) t ω
  have hR0 := runningMaximum_initial_zero P hT X (hX.path P F)
    ((hX.initial P F).mono (fun ω hω => by simpa only [Pi.zero_apply] using hω))
  have hXR ω t (ht : t < ⊤) : |X t ω| ≤ R t ω :=
    (runningMaximum_bounds X (hX.path P F) t ht ω).1 t le_rfl
  have hRb : ∀ᵐ ω ∂P, R b ω ≤ L := hXbound.mono (fun ω hω =>
    (runningMaximum_bounds X (hX.path P F) b hb ω).2 L hL hω)
  have hRmeas : Measurable (R b) := (hRa b hb).mono (hle b) le_rfl
  have hRi : Integrable (fun ω => R b ω^p) P := by
    apply (integrable_const (L^p)).mono'
      ((Real.continuous_rpow_const hp.le).measurable.comp hRmeas).aestronglyMeasurable
    filter_upwards [hRb] with ω hω
    change ‖R b ω^p‖ ≤ L^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hRp ω b hb) _)]
    exact Real.rpow_le_rpow (hRp ω b hb) hω hp.le
  have hAp ω : 0 ≤ A b ω := by
    rw [← hA0 ω]
    exact hAm ω hT hb bot_le
  have hAi : Integrable (fun ω => A b ω^(p/2)) P := by
    apply (integrable_const (K^(p/2))).mono'
      ((Real.continuous_rpow_const (by positivity : 0 ≤ p/2)).measurable.comp
        ((hA.adapted P F hX hX b hb).mono (hle b) le_rfl)).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    change ‖A b ω^(p/2)‖ ≤ K^(p/2)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hAp ω) _)]
    exact Real.rpow_le_rpow (hAp ω) hω (by positivity)
  let α := fun n : ℕ => (1/2:ℝ)^n
  have hαp n : 0 < α n := pow_pos (by norm_num) n
  have hαb n : 0 ≤ α n ∧ α n ≤ 1 :=
    ⟨(hαp n).le,pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hαlim : Tendsto α atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim := shifted_moment_limit_ae P (R b) hRmeas (fun ω => hRp ω b hb) L p hp hRb α hαlim hαb
  have hineq n := regularized_bdg_reverse_small_p P hT F hF hle hnull X A R hX hA hAm hAc hA0
    hRa hRc hRm hRp hR0 hXR (α n) p (hαp n) hp hp2 b hb K hK hbound L hL hRb
  exact ⟨hRi,hAi,ge_of_tendsto' (hlim.const_mul ((2/p)^p)) hineq⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_reverse_small_p_bounded
