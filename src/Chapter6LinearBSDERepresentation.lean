import Chapter6LinearBSDEChangedDrift
import Chapter6AdaptedIntegratingFactor
import Chapter6IntegratingFactorConditional
import Chapter6BoundedGirsanovData
import Chapter6BSDEActualEnvelope
import Chapter6SquareEnvelopeTransfer

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The conditional representation is derived from the actual BSDE
solution and the constructed exponential change of measure. -/
theorem linear_bsde_representation_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r,∃ n,r≤c n)
    (R : ℝ) (hR : 0≤R) (u : BSDEFiniteEnergyData P B.F (B.W 0) c R)
    (α φ : ℝ → Ω → ℝ) (β : Ω × ℝ → ℝ)
    (hαc : ∀ w,Continuous (fun r => α r w)) (hφc : ∀ w,Continuous (fun r => φ r w))
    (hαa : ∀ r∈Icc 0 R,Measurable[B.F (realTimeClamp r)] (α r))
    (hφa : ∀ r∈Icc 0 R,Measurable[B.F (realTimeClamp r)] (φ r))
    (hβm : Measurable β)
    (hβp : ∀ b,0<b → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => β (z.1,z.2.val)))
    (K : ℝ) (hK : 0≤K) (hβb : ∀ z,|β z|≤K)
    (hαb : ∀ w r,r∈Icc 0 R → |α r w|≤K) (hφb : ∀ w r,r∈Icc 0 R → |φ r w|≤K)
    (hdriver : ∀ w r,r∈Icc 0 R → u.B (w,r)= -(φ r w+α r w*u.Y (realTimeClamp r) w+β (w,r)*u.Z (w,r))) :
    ∃ (N C : HalfClosedTime → Ω → ℝ) (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
      ItoCovarianceFormula P B.F (B.W 0) β N ∧
      (∀ r : ℝ,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,β (w,s)^2) ∧
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (N (realTimeClamp R) w-C (realTimeClamp R) w/2))) ∧
      (∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) ∧
      (∀ s∈Icc 0 R,Q[(fun w => u.Y (realTimeClamp R) w*Real.exp (∫ r in s..R,α r w)+
        ∫ r in s..R,φ r w*Real.exp (∫ v in s..r,α v w))|B.F (realTimeClamp s)]=ᵐ[Q] u.Y (realTimeClamp s)) := by
  have hT : (0:EReal)<⊤ := by simp
  have hcT n : (c n:EReal)<⊤ := EReal.coe_lt_top _
  have hcut n : realTimeClamp (T := ⊤) (c n)<⊤ := changed_time_finite _ (hc n).le
  obtain ⟨Nv,C,hNv,hNI,hC,hCe,Q,hQp,hQ,hmean,hD2,hDsq,hPQ,BQ,hBQ,hBWe⟩ :=
    bounded_girsanov_density_data P B (fun _ => β) (fun _ => hβm) (fun _ => hβp) K hK (fun _ => hβb) R hR
  letI := hQp
  simp only [Fin.sum_univ_one] at hC hCe hQ hmean hD2 hDsq
  have hZsq b (hb : 0≤b) : ∀ᵐ w ∂P,IntervalIntegrable (fun r => u.Z (w,r)^2) volume 0 b := by
    obtain ⟨n,hn⟩ := hco b
    filter_upwards [u.squareZ n] with w hw
    exact hw.mono_set (by simpa only [uIcc_of_le hb,uIcc_of_le (hc n).le] using Icc_subset_Icc_right hn)
  have hVeq : ∀ᵐ w ∂P,∀ r∈Icc 0 R,u.V (realTimeClamp r) w=u.V ⊥ w+
      ∫ s in 0..r,-(φ s w+α s w*u.Y (realTimeClamp s) w+β (w,s)*u.Z (w,s)) := by
    obtain ⟨n,hn⟩ := hco R
    filter_upwards [u.drift n] with w hw
    intro r hr
    rw [hw r ⟨hr.1,hr.2.trans hn⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    exact hdriver w s ⟨hs.1,hs.2.trans hr.2⟩
  obtain ⟨VQ,MQ,hYQ,hVQ⟩ := linear_bsde_changed_drift P Q B hPQ β u.Z hβm u.measurableZ K hβb
    (Nv 0) u.M C u.Y u.V (hNv 0) u.decomposition (hNI 0) u.integral hC hZsq R hR hmean hQ α φ hαc hφc hVeq
  have hQnull t S (hS : MeasurableSet[m] S) (h0 : Q S=0) : MeasurableSet[B.F t] S := by
    apply B.null t S hS
    have hh : ∀ᵐ w ∂Q,w∉S := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using h0
    have hp := (hPQ _).mpr hh
    simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hp
  obtain ⟨A,hA,hAc,hAe,hApr⟩ := adapted_integrating_factor B.F B.mono α R hR hαa hαc
  have hz0 : realTimeClamp 0=(⊥ : HalfClosedTime) := by apply Subtype.ext; simp [realTimeClamp]
  have hA0 w : A ⊥ w=1 := by
    have hh := hAe (realTimeClamp 0) w
    rw [finite_prefix_time_of_real R 0 hR ⟨le_rfl,hR⟩ le_top] at hh
    simpa only [hz0,linearIntegratingFactor,intervalIntegral.integral_same,Real.exp_zero] using hh
  have hAr w r (hr : r∈Icc 0 R) : A (realTimeClamp r) w=linearIntegratingFactor (fun v => α v w) r := by
    rw [hAe,finite_prefix_time_of_real R r hR hr le_top]
  obtain ⟨L,hL,hLe⟩ := weighted_drift_cancellation Q B.F B.mono B.le hQnull u.Y VQ MQ A hYQ hA
    (fun w _ _ => (hAc w).continuousAt) α φ hαc hφc R hR hVQ (by
      intro w r hr
      rw [hA0]
      simpa only [finite_prefix_time_of_real R r hR hr le_top] using hApr (realTimeClamp r) w)
    c (fun n => (hc n).le) hcm.monotone hcc
  obtain ⟨U,hU,hUp,hUb⟩ := bsde_actual_square_envelope P hT B.F B.mono B.le B.null (B.W 0) (B.C 0 0)
    u.Y u.V u.M (B.martingale 0) (B.cov 0 0) u.decomposition c hc hcm hcT hct hcut hcc
    (fun n w r hr => by simpa using B.clock 0 0 w r hr.1)
    u.Z u.B u.measurableZ u.measurableB u.progressiveZ u.squareZ u.integrableB u.drift u.integral R hR (EReal.coe_lt_top R)
    u.terminal u.energyZ u.energyB
  let D := fun w => Real.exp (Nv 0 (realTimeClamp R) w-C (realTimeClamp R) w/2)
  have hDm : Measurable D :=
    (((hNv 0).adapted P B.F _ (changed_time_finite R hR)).mono (B.le _) le_rfl |>.sub
      (((covariance_adapted_variation P B.F B.mono B.le (hNv 0) (hNv 0) hC).adapted _ (changed_time_finite R hR)).mono (B.le _) le_rfl |>.div_const 2)).exp
  let d : Ω → ℝ≥0 := fun w => ⟨D w,Real.exp_nonneg _⟩
  have hd : Measurable d := hDm.subtype_mk
  have hdQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)) := by
    have he : (fun w => ENNReal.ofReal (D w))=(fun w => (d w:ℝ≥0∞)) :=
      funext (fun w => (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (d w:ℝ)=(d w:ℝ≥0∞)))
    rw [← he]
    exact hQ
  have hd2 : MemLp (fun w => (d w:ℝ)) 2 P := hD2
  have hUQ := square_envelope_density_transfer P Q d hd hdQ hd2 U hU hUp
  have hYb : ∀ᵐ w ∂Q,∀ r∈Icc 0 R,|u.Y (realTimeClamp r) w|≤Real.sqrt (U w) := by
    apply (hPQ _).mp
    filter_upwards [hUb] with w hw
    intro r hr
    exact by
      have hh := Real.sqrt_le_sqrt (hw r hr)
      simpa only [Real.sqrt_sq_eq_abs] using hh
  have hYa t (ht : t<⊤) : Measurable[B.F t] (u.Y t) := by
    have he : u.Y t=(fun w => u.V t w+u.M t w) := funext (u.decomposition.decomposition t ht)
    rw [he]; exact (u.decomposition.variation.adapted t ht).add (u.decomposition.martingale.adapted P B.F t ht)
  refine ⟨Nv 0,C,Q,hQp,hNI 0,hCe,hQ,hPQ,?_⟩
  intro s hs
  obtain ⟨hi,he⟩ := weighted_local_conditional Q B.F B.mono B.le u.Y A L hL hYa hA.adapted u.decomposition.continuous hAc
    φ hφc R hR hφa (Real.exp (K*R)) K (Real.exp_pos _).le hK (by
      intro w r hr
      rw [hAr w r hr,abs_of_pos (show 0<linearIntegratingFactor (fun v => α v w) r from Real.exp_pos _)]
      exact (integrating_factor_bounds _ K R hK (hαb w) r hr).2)
    hφb (fun w => Real.sqrt (U w)) hUQ hYb hLe s hs
  exact integrating_factor_conditional_formula Q (B.F (realTimeClamp s)) (B.le _) α φ hαc
    (fun r => A (realTimeClamp r)) R s K hK hs hαb hAr
    (hA.adapted _ (changed_time_finite s hs.1)) (u.Y (realTimeClamp R)) (u.Y (realTimeClamp s)) hi he

end Asakura.Chapter6
