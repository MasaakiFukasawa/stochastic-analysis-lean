import Chapter5TimeSpaceBrownian

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Nonlinear Feynman--Kac for unit diffusion. This is a proved stochastic
BSDE identity, not just a formal substitution in differential notation.
The general diffusion coefficient and local C² extension are separate
steps in the chapter audit. -/
theorem nonlinear_feynman_kac_unit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiff ℝ 2 v)
    (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hterminal : ∀ x, v ![R,x] = g x)
    (hpde : ∀ r ∈ Icc 0 R, ∀ x,
      fderiv ℝ v ![r,x] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ v) ![r,x] (Pi.single 1 1) (Pi.single 1 1))/2 +
      f r (v ![r,x]) (fderiv ℝ v ![r,x] (Pi.single 1 1)) = 0)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → C (realTimeClamp r) w = r) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F X
        (fun z => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
          X (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ t ∈ Icc 0 R,
        (fun w => g (X (realTimeClamp R) w)) =ᵐ[P]
          fun w => v ![t,X (realTimeClamp t) w] -
            (∫ r in t..R, f r (v ![r,X (realTimeClamp r) w])
              (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1))) +
            (N (realTimeClamp R) w - N (realTimeClamp t) w) := by
  obtain ⟨N,hN,hNI,he⟩ := time_space_clock_martingale_ito P hT F hF hle hnull
    X C hX hC R hR hRT v hv c hc hcm hcT hcc hclock
  refine ⟨N,hN,hNI,?_⟩
  intro t ht
  filter_upwards [he R hR le_rfl,he t ht.1 ht.2] with w hRw htw
  let U := fun r => ![r,X (realTimeClamp r) w]
  let A := fun r => fderiv ℝ v (U r) (Pi.single 0 1)
  let B := fun r => fderiv ℝ (fderiv ℝ v) (U r) (Pi.single 1 1) (Pi.single 1 1)
  let D := fun r => f r (v (U r)) (fderiv ℝ v (U r) (Pi.single 1 1))
  have hUc : ContinuousOn U (Icc 0 R) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact continuousAt_id
    · have hrt : realTimeClamp (T := T) r < ⊤ := by
        change (realTimeClamp r : EReal) < T
        rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)]
        exact (EReal.coe_le_coe hr.2).trans_lt hRT
      exact (hX.path P F w _ hrt).comp real_time_clamp_continuous.continuousAt
  have hac : ContinuousOn A (Icc 0 R) :=
    ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp_continuousOn hUc
  have hbc : ContinuousOn B (Icc 0 R) :=
    ((((hv.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const).comp_continuousOn hUc
  have hd : ∀ r ∈ Icc 0 R, D r = -(A r+B r/2) := by
    intro r hr
    have h := hpde r hr (X (realTimeClamp r) w)
    dsimp [D,A,B,U]
    linarith
  have hdc : ContinuousOn D (Icc 0 R) := ((hac.add (hbc.div_const 2)).neg).congr hd
  have hcancel d (hd0 : 0 ≤ d) (hdR : d ≤ R) :
      (∫ r in 0..d, A r)+(∫ r in 0..d, B r)/2 = -(∫ r in 0..d, D r) := by
    have hai : IntervalIntegrable A volume 0 d := (hac.mono (Icc_subset_Icc_right hdR)).intervalIntegrable_of_Icc hd0
    have hbi : IntervalIntegrable B volume 0 d := (hbc.mono (Icc_subset_Icc_right hdR)).intervalIntegrable_of_Icc hd0
    rw [← intervalIntegral.integral_div,← intervalIntegral.integral_add hai (hbi.div_const 2),← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 R := Icc_subset_Icc_right hdR (by simpa [uIcc_of_le hd0] using hr)
    dsimp only
    rw [hd r hr',neg_neg]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hdc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    ((hdc.mono (Icc_subset_Icc_left ht.1)).intervalIntegrable_of_Icc ht.2)
  have hRcan := hcancel R hR le_rfl
  have htcan := hcancel t ht.1 ht.2
  rw [hterminal] at hRw
  change g (X (realTimeClamp R) w) = v ![t,X (realTimeClamp t) w] - (∫ r in t..R, D r) + _
  change v ![t,X (realTimeClamp t) w] = v ![0,X ⊥ w]+N (realTimeClamp t) w+(∫ r in 0..t,A r)+(∫ r in 0..t,B r)/2 at htw
  change g (X (realTimeClamp R) w) = v ![0,X ⊥ w]+N (realTimeClamp R) w+(∫ r in 0..R,A r)+(∫ r in 0..R,B r)/2 at hRw
  linarith

end Asakura.Chapter5
