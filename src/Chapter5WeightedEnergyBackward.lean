import Chapter5WeightedEnergyIto

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the two constructed Ito identities. Local time-integrability
of every term is derived, so splitting the integrals at t is justified. -/
theorem weighted_energy_backward
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (β : ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (B : Ω × ℝ → ℝ) (hBm : ∀ w, Measurable (fun r => B (w,r)))
    (hBi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => B (w,r)) volume 0 (c n))
    (hAB : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), A (realTimeClamp r) w = A ⊥ w + ∫ s in 0..r, B (w,s))
    (G : Ω × ℝ → ℝ) (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)) volume 0 (c n))
    (hCG : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r, G (w,s)) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F M
        (fun z => 2*Real.exp (β*(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val)*
          X (realTimeClamp z.2) z.1) N ∧
      ∀ t ∈ Icc 0 R,
        (fun w => Real.exp (β*t)*(X (realTimeClamp t) w)^2 +
            (∫ r in t..R, β*Real.exp (β*r)*(X (realTimeClamp r) w)^2) +
            (∫ r in t..R, Real.exp (β*r)*G (w,r))) =ᵐ[P]
          fun w => Real.exp (β*R)*(X (realTimeClamp R) w)^2 -
            (∫ r in t..R, 2*Real.exp (β*r)*X (realTimeClamp r) w*B (w,r)) -
            (N (realTimeClamp R) w-N (realTimeClamp t) w) := by
  obtain ⟨N,hN,hNI,he⟩ := weighted_energy_ito P hT F hF hle hnull
    X A M C hX hC R hR hRT β c hc hcm hcT hcc B hBm hBi hAB G hGm hGi hCG
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
  filter_upwards [he R hR le_rfl,he t ht.1 ht.2,hBi j,hGi j] with w hRform htform hBiw hGiw
  have hYc : ContinuousOn (fun r => X (realTimeClamp r) w) (Icc 0 R) := by
    intro r hr
    have hrt : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r : EReal) < T
      rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)]
      exact (EReal.coe_le_coe hr.2).trans_lt hRT
    exact ((hX.continuous w _ hrt).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hYm := open_path_real_measurable _ (hX.continuous w)
  have hEc : Continuous (fun r : ℝ => Real.exp (β*r)) := by fun_prop
  have hBri : IntervalIntegrable (fun r => B (w,r)) volume 0 R :=
    hBiw.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j)] using Icc_subset_Icc_right hRj)
  have hGri : IntervalIntegrable (fun r => G (w,r)) volume 0 R :=
    hGiw.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j)] using Icc_subset_Icc_right hRj)
  let a := fun r => β*Real.exp (β*r)*(X (realTimeClamp r) w)^2
  let b := fun r => 2*Real.exp (β*r)*X (realTimeClamp r) w*B (w,r)
  let g := fun r => Real.exp (β*r)*G (w,r)
  have hai : IntervalIntegrable a volume 0 R :=
    ((hEc.continuousOn.const_mul β).mul (hYc.pow 2)).intervalIntegrable_of_Icc hR
  have hbi : IntervalIntegrable b volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    exact continuous_multiplier_integrable R hR _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩)
      (fun r => 2*Real.exp (β*r)*X (realTimeClamp r) w) (fun r => B (w,r))
      ((hEc.continuousOn.const_mul 2).mul hYc) ((hEc.measurable.const_mul 2).mul hYm) hBri.1
  have hgi : IntervalIntegrable g volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    exact continuous_multiplier_integrable R hR _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩)
      (fun r => Real.exp (β*r)) (fun r => G (w,r)) hEc.continuousOn hEc.measurable hGri.1
  have hsplit (q : ℝ → ℝ) (hq : IntervalIntegrable q volume 0 R) :
      (∫ r in 0..t, q r)+(∫ r in t..R, q r) = ∫ r in 0..R, q r :=
    intervalIntegral.integral_add_adjacent_intervals
      (hq.mono_set (by simpa [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
      (hq.mono_set (by simpa [uIcc_of_le ht.2,uIcc_of_le hR] using Icc_subset_Icc_left ht.1))
  have ha := hsplit a hai
  have hb := hsplit b hbi
  have hg := hsplit g hgi
  change Real.exp (β*t)*(X (realTimeClamp t) w)^2 + (∫ r in t..R,a r)+(∫ r in t..R,g r) =
    Real.exp (β*R)*(X (realTimeClamp R) w)^2-(∫ r in t..R,b r)-(N (realTimeClamp R) w-N (realTimeClamp t) w)
  change Real.exp (β*R)*(X (realTimeClamp R) w)^2 = (X ⊥ w)^2+N (realTimeClamp R) w+
    (∫ r in 0..R,a r)+(∫ r in 0..R,b r)+(∫ r in 0..R,g r) at hRform
  change Real.exp (β*t)*(X (realTimeClamp t) w)^2 = (X ⊥ w)^2+N (realTimeClamp t) w+
    (∫ r in 0..t,a r)+(∫ r in 0..t,b r)+(∫ r in 0..t,g r) at htform
  linarith

end Asakura.Chapter5
