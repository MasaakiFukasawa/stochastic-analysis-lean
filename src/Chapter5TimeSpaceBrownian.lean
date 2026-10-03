import Chapter5TimeSpaceIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The time-space formula with Brownian quadratic variation. The
stochastic integral is constructed, and both variation integrals are
identified with ordinary Lebesgue integrals. -/
theorem time_space_clock_martingale_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → C (realTimeClamp r) w = r) :
    let K := fun t => (finitePrefixTime (T := T) R hR t).val
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F X
        (fun z => fderiv ℝ f ![K (realTimeClamp z.2),X (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ R →
        (fun w => f ![d,X (realTimeClamp d) w]) =ᵐ[P]
          fun w => f ![0,X ⊥ w] + N (realTimeClamp d) w +
            (∫ r in 0..d, fderiv ℝ f ![r,X (realTimeClamp r) w] (Pi.single 0 1)) +
            (∫ r in 0..d, fderiv ℝ (fderiv ℝ f) ![r,X (realTimeClamp r) w]
              (Pi.single 1 1) (Pi.single 1 1))/2 := by
  dsimp only
  obtain ⟨I,J,hI,hJ,he⟩ := time_space_ito_constructed P hT F hF hle hnull
    X (fun _ _ => 0) X C (local_martingale_semimartingale_decomposition P hT F hF X hX) hC
    R hR hRT f hf c hc hcm hcT hcc
  obtain ⟨D,N,hDN,hD,hN⟩ := hI
  have hd0 := hD.unique P c hc hcc _ D (fun _ _ => 0) _ (zero_variation_integral P c hc _)
  refine ⟨N,hDN.martingale,hN,?_⟩
  intro d hd hdR
  have hdT : (d:EReal) < T := (EReal.coe_le_coe hdR).trans_lt hRT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdc : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  have hjt := clock_variation_integral_at_time P C J _ c hc hcT hclock hJ j d hd hdc
  filter_upwards [he d hd hdR,hd0,hjt] with w hew hdw hjw
  rw [hDN.decomposition _ hdt w,hdw _ hdt,zero_add,hjw] at hew
  have hint : (∫ r in 0..d, fderiv ℝ (fderiv ℝ f)
      ![(finitePrefixTime (T := T) R hR (realTimeClamp r)).val,X (realTimeClamp r) w]
      (Pi.single 1 1) (Pi.single 1 1)) =
      ∫ r in 0..d, fderiv ℝ (fderiv ℝ f) ![r,X (realTimeClamp r) w]
        (Pi.single 1 1) (Pi.single 1 1) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 d := by simpa [uIcc_of_le hd] using hr
    dsimp only
    rw [finite_prefix_time_of_real R r hR (Icc_subset_Icc_right hdR hr') hRT.le]
  rw [hint] at hew
  linarith

end Asakura.Chapter5
