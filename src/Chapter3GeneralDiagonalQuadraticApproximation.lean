import Chapter3StoppedQuadraticApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The diagonal weighted quadratic-variation approximation with no
boundedness assumption on H or Q. The proof constructs common localizers,
applies the bounded theorem, and transfers back on each finite prefix.
Clipping H at ±2k avoids imposing boundedness of the random initial H₀;
it is eventually the identity on the chosen prefix. -/
theorem general_diagonal_quadratic_approximation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (hb : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (hHosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∀ᵐ ω ∂P, QuadraticPathApproximation
      (fun t => X t ω) (fun t => Q t ω) (fun t => H t ω)
      (fun n j => τ n j ω) d hd := by
  obtain ⟨σ,hσ,hσm,hσt,hσco,hσb⟩ := quadratic_approximation_bounded_localizers
    P F hF hle hnull X Q H hX hQ hHm hHc c hcm hct hcc
  have hk (k : ℕ) := stopped_clipped_quadratic_approximation P F hF hle hnull
    X Q H hX hQ hHm hHc c hcm hct hcc τ hτ hτmono hτtop hτ0 hcofinal hb hHosc
    (σ k) (hσ k) (hσt k) (k:ℝ) ((hσb k).mono (fun ω hω t => (hω t).2))
    (2*(k:ℝ)) (by positivity) d hd hdT
  filter_upwards [ae_all_iff.mpr hk,ae_all_iff.mpr hσb,
    local_quadratic_variation_monotone P F hF hle hnull X Q hX hQ] with ω hkω hbound hmono
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨N,hN⟩ := hσco ω (realTimeClamp d) hdt
  obtain ⟨J,hJ⟩ := exists_nat_gt |H ⊥ ω|
  let k := max N J
  have hdk : realTimeClamp (T := T) d ≤ σ k ω := hN.le.trans (hσm ω (le_max_left _ _))
  have hH0 : |H ⊥ ω| ≤ (k:ℝ) := hJ.le.trans (by exact_mod_cast le_max_right N J)
  have hrt (r : ℝ) (hr : r ∈ Icc (0:ℝ) d) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hdT
  have hQm : MonotoneOn (fun r => Q (realTimeClamp r) ω) (Icc 0 d) :=
    fun a ha b hb hab => hmono (hrt a ha) (hrt b hb) (real_time_clamp_mono hab)
  have hQr : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r) ω) (Icc 0 d ∩ Ici x) x :=
    fun x hx => (covariance_real_continuous_on P F X X Q hX hX hQ d hdT ω x hx).mono inter_subset_left
  apply quadratic_path_approximation_congr (fun t => X t ω) (fun t => Q t ω) (fun t => H t ω)
    (fun t => X (min (σ k ω) t) ω) (fun t => Q (min (σ k ω) t) ω)
    (fun t => intervalClamp (-(2*(k:ℝ))) (2*(k:ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k]) (H (min (σ k ω) t) ω))
    (fun n j => τ n j ω) (fun n => hτmono n ω) d hd hQm hQr
    (fun s hs => by rw [min_eq_right (hs.trans hdk)])
    (fun s hs => by rw [min_eq_right (hs.trans hdk)]) ?_ (hkω k)
  intro s hs
  have hsk : s ≤ σ k ω := hs.trans hdk
  rw [min_eq_right hsk]
  have hcenter := (hbound k s).1
  rw [min_eq_right hsk] at hcenter
  have hab : |H s ω| ≤ 2*(k:ℝ) := by
    have hh := abs_add_le (H s ω-H ⊥ ω) (H ⊥ ω)
    rw [sub_add_cancel] at hh
    linarith
  exact (intervalClamp_eq _ _ _ (abs_le.mp hab)).symm

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.general_diagonal_quadratic_approximation
