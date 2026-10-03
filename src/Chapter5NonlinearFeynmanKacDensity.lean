import Chapter5TimeSpaceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- PDE cancellation for a general locally square-integrable diffusion
coefficient, with the actual stochastic integral constructed by Ito.
Brownian-integral associativity is a separate preceding-chapter step. -/
theorem nonlinear_feynman_kac_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X M C : ClosedTime T → Ω → ℝ) (U₀ : Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X (fun _ => U₀) M)
    (hC : LocalCovarianceWitness P F M M C)
    (G : Ω × ℝ → ℝ) (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiff ℝ 2 v)
    (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hterminal : ∀ x, v ![R,x] = g x)
    (hpde : ∀ᵐ w ∂P,∀ r,r ∈ Icc 0 R →
      fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ v) ![r,X (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*G (w,r)^2/2 +
      f r (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)) = 0)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hCG : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r, G (w,s)^2) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F M
        (fun z => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
          X (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ t ∈ Icc 0 R,
        (fun w => g (X (realTimeClamp R) w)) =ᵐ[P]
          fun w => v ![t,X (realTimeClamp t) w] -
            (∫ r in t..R, f r (v ![r,X (realTimeClamp r) w])
              (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r))) +
            (N (realTimeClamp R) w - N (realTimeClamp t) w) := by
  obtain ⟨N,hN,hNI,he⟩ := time_space_density_ito P hT F hF hle hnull
    X M C U₀ hX hC R hR hRT v hv c hc hcm hcT hcc
    (fun z => G z^2) (fun w => (hGm w).pow_const 2) hGi hCG
  have hRt : realTimeClamp (T := T) R < ⊤ := by
    change (realTimeClamp R : EReal) < T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  obtain ⟨j,hj⟩ := hcc _ hRt
  have hRj : R ≤ c j := by
    change (realTimeClamp R : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  refine ⟨N,hN,hNI,?_⟩
  intro t ht
  filter_upwards [he R hR le_rfl,he t ht.1 ht.2,hGi j,hpde] with w hRw htw hGiw hpdew
  let U := fun r => ![r,X (realTimeClamp r) w]
  let A := fun r => fderiv ℝ v (U r) (Pi.single 0 1)
  let B₀ := fun r => fderiv ℝ (fderiv ℝ v) (U r) (Pi.single 1 1) (Pi.single 1 1)
  let B := fun r => B₀ r*G (w,r)^2
  let D := fun r => f r (v (U r)) (fderiv ℝ v (U r) (Pi.single 1 1)*G (w,r))
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
      exact (hX.continuous w _ hrt).comp real_time_clamp_continuous.continuousAt
  have hac : ContinuousOn A (Icc 0 R) :=
    ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp_continuousOn hUc
  have hbc : ContinuousOn B₀ (Icc 0 R) :=
    ((((hv.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const).comp_continuousOn hUc
  have hd : ∀ r ∈ Icc 0 R, D r = -(A r+B r/2) := by
    intro r hr
    have h := hpdew r hr
    dsimp [D,A,B,B₀,U]
    linarith
  have hGri : IntervalIntegrable (fun r => G (w,r)^2) volume 0 R :=
    hGiw.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j)] using Icc_subset_Icc_right hRj)
  have hBm : Measurable B₀ := by
    apply (((hv.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const |>.measurable.comp
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact measurable_id
    · exact open_path_real_measurable _ (hX.continuous w)
  have hBi : IntervalIntegrable B volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    exact continuous_multiplier_integrable R hR _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩)
      B₀ (fun r => G (w,r)^2) hbc hBm hGri.1
  have hDi : IntervalIntegrable D volume 0 R := by
    apply ((hac.intervalIntegrable_of_Icc hR).add (hBi.div_const 2)).neg.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    have hr0 : r ∈ Ioc 0 R := by simpa [uIoc_of_le hR] using hr
    have hr' : r ∈ Icc 0 R := ⟨hr0.1.le,hr0.2⟩
    exact (hd r hr').symm
  have hcancel d (hd0 : 0 ≤ d) (hdR : d ≤ R) :
      (∫ r in 0..d, A r)+(∫ r in 0..d, B r)/2 = -(∫ r in 0..d, D r) := by
    have hai : IntervalIntegrable A volume 0 d := (hac.mono (Icc_subset_Icc_right hdR)).intervalIntegrable_of_Icc hd0
    have hbi : IntervalIntegrable B volume 0 d := hBi.mono_set (by simpa [uIcc_of_le hd0,uIcc_of_le hR] using Icc_subset_Icc_right hdR)
    rw [← intervalIntegral.integral_div,← intervalIntegral.integral_add hai (hbi.div_const 2),← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 R := Icc_subset_Icc_right hdR (by simpa [uIcc_of_le hd0] using hr)
    dsimp only
    rw [hd r hr',neg_neg]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := t) (c := R)
    (hDi.mono_set (by simpa [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
    (hDi.mono_set (by simpa [uIcc_of_le ht.2,uIcc_of_le hR] using Icc_subset_Icc_left ht.1))
  have hRcan := hcancel R hR le_rfl
  have htcan := hcancel t ht.1 ht.2
  rw [hterminal] at hRw
  change g (X (realTimeClamp R) w) = v ![t,X (realTimeClamp t) w] - (∫ r in t..R, D r) + _
  change v ![t,X (realTimeClamp t) w] = v ![0,X ⊥ w]+N (realTimeClamp t) w+(∫ r in 0..t,A r)+(∫ r in 0..t,B r)/2 at htw
  change g (X (realTimeClamp R) w) = v ![0,X ⊥ w]+N (realTimeClamp R) w+(∫ r in 0..R,A r)+(∫ r in 0..R,B r)/2 at hRw
  linarith

end Asakura.Chapter5
