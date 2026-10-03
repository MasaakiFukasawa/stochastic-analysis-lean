import Chapter5WeightedEnergyBackward
import Chapter5BrownianBracketCommon
import Chapter5ComposedEnergyNoise
import Chapter5BSDESquareEnvelope
import Chapter5FiniteTimeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Connect the BSDE decomposition itself to the energy identity and the
zero-mean noise. The bracket, the integrable square envelope, and the
noise integrability are all derived, rather than hypotheses. -/
theorem bsde_constructed_energy_and_zero_mean
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
    (β : ℝ) (hβ : 0 ≤ β)
    (hterminal : MemLp (Y (realTimeClamp R)) 2 P)
    (hGL : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hBL : MemLp B 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    ∃ N : ClosedTime T → Ω → ℝ, LocalMProcessWitness P F N ∧
      (∀ t ∈ Icc 0 R, MemLp (Y (realTimeClamp t)) 2 P) ∧
      (∀ t ∈ Icc 0 R,
        (fun w => Real.exp (β*t)*(Y (realTimeClamp t) w)^2 +
            (∫ r in t..R, β*Real.exp (β*r)*(Y (realTimeClamp r) w)^2) +
            (∫ r in t..R, Real.exp (β*r)*G (w,r)^2)) =ᵐ[P]
          fun w => Real.exp (β*R)*(Y (realTimeClamp R) w)^2 -
            (∫ r in t..R, 2*Real.exp (β*r)*Y (realTimeClamp r) w*B (w,r)) -
            (N (realTimeClamp R) w-N (realTimeClamp t) w)) ∧
      (∀ t ∈ Icc 0 R,
        Integrable (fun w => N (realTimeClamp R) w-N (realTimeClamp t) w) P ∧
          (∫ w, N (realTimeClamp R) w-N (realTimeClamp t) w ∂P) = 0) := by
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
  obtain ⟨N,hN,hNI,he⟩ := weighted_energy_backward P hT F hF hle hnull Y V M Q hY hQ R hR hRT β
    c (fun n => (hc n).le) hcm.monotone hcT hcc B (fun w => hBm.comp measurable_prodMk_left) hBi hVB
    (fun z => G z^2) (fun w => (hGm.comp measurable_prodMk_left).pow_const 2) hGi hQGall
  refine ⟨N,hN,?_,he,?_⟩
  · intro t ht
    have hm : Measurable (Y (realTimeClamp t)) := by
      have heq : Y (realTimeClamp t) = fun w => V (realTimeClamp t) w+M (realTimeClamp t) w :=
        funext (hY.decomposition _ (hfinite t ht))
      rw [heq]
      exact ((hY.variation.adapted _ (hfinite t ht)).add
        (hY.martingale.adapted P F _ (hfinite t ht))).mono (hle _) le_rfl
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    apply hUi.mono' (hm.pow_const 2).aestronglyMeasurable
    filter_upwards [hUbound] with w hw
    simpa only [Real.norm_eq_abs,abs_sq] using hw t ht
  let H := fun z : Ω × ℝ => 2*Real.exp (β*(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val)*
    Y (realTimeClamp z.2) z.1
  obtain ⟨hHm,hHa,hHc⟩ := time_space_integrand_regularity P F Y V M hY R hR
    (fun x => 2*Real.exp (β*x 0)*x 1) (by fun_prop)
  have hbound : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 R, H (w,r)^2 ≤ (2*Real.exp (β*R))^2*U w := by
    filter_upwards [hUbound] with w hw
    intro r hr
    dsimp [H]
    rw [finite_prefix_time_of_real R r hR hr hRT.le,mul_pow]
    have he : (2*Real.exp (β*r))^2 ≤ (2*Real.exp (β*R))^2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2 hβ)) (by norm_num)) 2
    exact mul_le_mul he (hw r hr) (sq_nonneg _) (sq_nonneg _)
  intro t ht
  exact composed_energy_noise_mean_zero P hT F hF hle hnull W A M N hW hA hY.martingale hN
    c hc hcm hcT hct hcut hcc hclock G H hG hGi
    (fun w => hGm.comp measurable_prodMk_left) hHm hHa (fun n => hHc (c n) (hc n).le (hcT n)) hMG hNI
    R hR hRT U (2*Real.exp (β*R)) (by positivity) hUi (ae_of_all _ hU0) hGe hbound
    (realTimeClamp t) (real_time_clamp_mono ht.2)

end Asakura.Chapter5
