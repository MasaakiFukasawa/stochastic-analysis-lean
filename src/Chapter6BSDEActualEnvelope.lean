import Chapter5BSDEEnergyConnection

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem bsde_actual_square_envelope
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A Y V M : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hA : LocalCovarianceWitness P F W W A)
    (hY : SemimartingaleDecomposition P F Y V M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G B : Ω × ℝ → ℝ) (hGm : Measurable G) (hBm : Measurable B)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hBi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => B (w,r)) volume 0 (c n))
    (hVB : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), V (realTimeClamp r) w = V ⊥ w + ∫ s in 0..r,B (w,s))
    (hMG : ItoCovarianceFormula P F W G M)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (hterminal : MemLp (Y (realTimeClamp R)) 2 P)
    (hGL : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hBL : MemLp B 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    ∃ U : Ω → ℝ,Integrable U P ∧ (∀ w,0≤U w) ∧
      (∀ᵐ w ∂P,∀ t∈Icc 0 R,Y (realTimeClamp t) w^2≤U w) := by
  obtain ⟨Q,hQ,hQG,hQGall⟩ := clock_ito_integral_bracket_common P hT F hF hle hnull
    W A M hW hA hY.martingale c hc hcm hcT hct hcut hcc hclock G hG hGi hMG
  obtain ⟨hGsec,hGe⟩ := finite_time_L2_sections P R hR G hGm hGL
  obtain ⟨hBsec,hBe⟩ := finite_time_L2_sections P R hR B hBm hBL
  have hfinite (r : ℝ) (hr : r ∈ Icc 0 R) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hRT
  have hRt := hfinite R ⟨hR,le_rfl⟩
  obtain ⟨j,hj⟩ := hcc _ hRt
  have hRj : R ≤ c j := by
    change (realTimeClamp R : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  have hback : ∀ᵐ w ∂P, ∀ t ∈ Icc 0 R,
      Y (realTimeClamp t) w = Y (realTimeClamp R) w + (∫ r in t..R,-B (w,r)) -
        (M (realTimeClamp R) w-M (realTimeClamp t) w) := by
    filter_upwards [hVB j,hBi j] with w hw hi
    have hir : IntervalIntegrable (fun r => B (w,r)) volume 0 R :=
      hi.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j).le] using Icc_subset_Icc_right hRj)
    intro t ht
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := t) (c := R)
      (hir.mono_set (by simpa [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
      (hir.mono_set (by simpa [uIcc_of_le ht.2,uIcc_of_le hR] using Icc_subset_Icc_left ht.1))
    rw [hY.decomposition _ (hfinite t ht),hY.decomposition _ hRt,
      hw t ⟨ht.1,ht.2.trans hRj⟩,hw R ⟨hR,hRj⟩,intervalIntegral.integral_neg]
    linarith
  have hQi : Integrable (Q (realTimeClamp R)) P := hGe.congr (hQG R hR hRT).symm
  have hQ0 : ∀ᵐ w ∂P, 0 ≤ Q (realTimeClamp R) w := by
    filter_upwards [hQG R hR hRT] with w hw
    rw [hw]
    exact intervalIntegral.integral_nonneg hR (fun r _ => sq_nonneg _)
  obtain ⟨U,hUi,hU0,hUbound⟩ := bsde_square_envelope P hT F hF hle hnull Y M Q hY.martingale hQ
    R hR hRT hQi hQ0 (Y (realTimeClamp R)) hterminal (fun z => -B z)
    (hBsec.mono fun w hw => hw.neg) (by simpa only [neg_sq] using hBe) hback
  exact ⟨U,hUi,hU0,hUbound⟩

end Asakura.Chapter6
