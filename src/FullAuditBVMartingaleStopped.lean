import FullAuditVariationStopping
import FullAuditTimeCompactification
import FullAuditStoppedSquareEnergy

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- DCT for the actual stopped square sums, and optional sampling for X²-Q.
 All bounds come from stopping the actual path variation. -/
theorem bv_martingale_stopped_zero {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (h2 : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⟨0,le_rfl,hT.le⟩ =ᵐ[P] 0) {k : ℝ} (hk : 0 ≤ k) :
    (fun ω => X (variationStop X k ω) ω) =ᵐ[P] 0 := by
  let τ := variationStop X k
  have hτ := variation_stop_stopping F hF X hm hc hb k
  let ρ := closedTimeUnitIso hT
  let π := fun n j => ρ (uniformPartition n j)
  let Q := fun n ω => partitionSquares X (π n) (n+1) (τ ω) ω
  let G := fun ω t => X (min t (τ ω)) ω
  have hGv (ω) : eVariationOn (G ω) univ ≤ ENNReal.ofReal k := stopped_path_variation_bound X hc hb hk ω
  have hGb (ω) : BoundedVariationOn (G ω) univ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hGv ω)
  have hGreal (ω) : (eVariationOn (G ω) univ).toReal ≤ k := ENNReal.toReal_le_of_le_ofReal hk (hGv ω)
  have hGc (ω) : Continuous (G ω) := (hc ω).comp (continuous_id.min continuous_const)
  have hmτ := stopped_value_measurable_right_continuous m hT.le F hF hle τ hτ X hm
    (fun ω t => (hc ω).continuousAt.continuousWithinAt)
  have hmτm : Measurable[m] (fun ω => X (τ ω) ω) := hmτ.mono (fun A hA => hA.1) le_rfl
  have hbound : ∀ᵐ ω ∂P, |X (τ ω) ω| ≤ k := by
    filter_upwards [hz] with ω hω
    change X ⊥ ω = 0 at hω
    have h := (hGb ω).dist_le (mem_univ (⊤ : ClosedTime T)) (mem_univ ⊥)
    simp only [G,min_top_left,min_bot_left,Real.dist_eq,hω,Pi.zero_apply,sub_zero] at h
    exact h.trans (hGreal ω)
  have hsq : Integrable (fun ω => X (τ ω) ω ^ 2) P := by
    apply Integrable.of_bound (hmτm.pow_const 2).aestronglyMeasurable (k^2)
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hπ (n) : Monotone (π n) := ρ.monotone.comp (uniform_partition_mono n)
  have hπ0 (n) : π n 0 = ⊥ := by simp only [π,(uniform_partition_endpoints n).1,OrderIso.map_bot]
  have hπN (n) : π n (n+1) = ⊤ := by simp only [π,(uniform_partition_endpoints n).2,OrderIso.map_top]
  have henergy (n) : Integrable (Q n) P ∧ (∫ ω, Q n ω ∂P) = ∫ ω, X (τ ω) ω ^ 2 ∂P :=
    stopped_partition_energy P F hF hle X hm h2 hc hmart hz (π n) (hπ n) (hπ0 n) (n+1) (hπN n) τ hτ hsq
  have hsum (n ω) : ∑ j ∈ Finset.range (n+1), |G ω (π n (j+1))-G ω (π n j)| ≤ k :=
    (finite_variation_real_bound (G ω) (hGb ω) (π n) (hπ n) (n+1)).trans (hGreal ω)
  have hQbound (n ω) : ‖Q n ω‖ ≤ k^2 := by
    have hinc (j) (hj : j < n+1) : |G ω (π n (j+1))-G ω (π n j)| ≤ k :=
      (Finset.single_le_sum (fun i _ => abs_nonneg (G ω (π n (i+1))-G ω (π n i)))
        (Finset.mem_range.mpr hj)).trans (hsum n ω)
    have h := finite_square_sum_bound (fun j => G ω (π n j)) (n+1) k k hk hinc (hsum n ω)
    have hpos : 0 ≤ Q n ω := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hpos]
    simpa only [Q,partitionSquares,G,min_comm,pow_two] using h
  have hlim (ω) : Tendsto (fun n => Q n ω) atTop (𝓝 0) := by
    have h := continuous_bv_square_sums_zero ρ (G ω) (hGc ω) (hGb ω)
    simpa only [Q,partitionSquares,G,π,min_comm] using h
  have hint : Tendsto (fun n => ∫ ω, Q n ω ∂P) atTop (𝓝 (∫ _ : Ω, (0:ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => k^2)
    · intro n; exact (henergy n).1.aestronglyMeasurable
    · exact integrable_const _
    · intro n; exact ae_of_all _ (hQbound n)
    · exact ae_of_all _ hlim
  simp only [integral_zero,(henergy _).2] at hint
  have hzero : (∫ ω, X (τ ω) ω ^ 2 ∂P) = 0 := tendsto_nhds_unique tendsto_const_nhds hint
  have hsqzero := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg (X (τ ω) ω)) hsq).mp hzero
  filter_upwards [hsqzero] with ω hω
  exact (sq_eq_zero_iff).mp hω

end Asakura.FullAudit
