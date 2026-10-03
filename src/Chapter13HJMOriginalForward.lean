import Chapter13HJMParameterExponent
import Chapter13HJMUnstoppedFubini
import Chapter13DeterministicParameterFubini
import Chapter13FixedTimeLocalTransfer

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

/-- HJM necessity for the original forward-rate integral representation.
N denotes the integrals of minus sigma. The price is defined by the actual
maturity integral, not assumed equal to the constructed exponential. -/
theorem hjm_drift_from_original_forward_integrals {Ω E:Type} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (μ:Measure E) [IsFiniteMeasure μ] (f0:E → ℝ) (hf0:Integrable f0 μ)
    (a:E × (Ω × ℝ) → ℝ) (σ:Fin d → E × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |σ i (x,(w,r))|≤K)
    (N:Fin d → E → HalfClosedTime → Ω → ℝ)
    (hN:∀i x,LocalMProcessWitness P B.F (N i x))
    (hNI:∀i x,ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x))
    (hNm:∀i,Measurable (fun z:E × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1)) :
    let Price:=fun (t:HalfClosedTime) w => Real.exp (-(∫x,f0 x+(∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w∂μ))
    LocalMProcessWitness P B.F (fun t w => Price t w-Price ⊥ w) →
      ∀R,0≤R → ∀ᵐw∂P,∀ᵐr∂volume,r∈Ioo 0 R →
        (∫x,a (x,(w,r))∂μ)=(∑i,(∫x,σ i (x,(w,r))∂μ)^2)/2 := by
  intro Price hPrice
  have hT:(0:EReal)<⊤ := by simp
  obtain ⟨M,X,A,hM,hMI,hX,hXe,hdrift⟩:=hjm_parameter_exponent P B μ (fun _ => -(∫x,f0 x∂μ)) measurable_const
    a σ ham hσm hap hσp hab hσb
  have hFub i r (hr:0≤r):∀ᵐw∂P,M i (realTimeClamp r) w=(∫x,N i x (realTimeClamp r) w∂μ) ∧
      Integrable (fun x => N i x (realTimeClamp r) w) μ := by
    have hMI':ItoCovarianceFormula P B.F (B.W i) (fun z => ∫x,-σ i (x,z)∂μ) (M i) := by
      simpa only [integral_neg] using hMI i
    exact hjm_unstopped_fubini P B i μ (fun z => -σ i z) (hσm i).neg
      (fun b hb => (hσp i b hb).neg)
      (fun w b hb => by simpa only [abs_neg] using hσb i w b hb)
      (N i) (hN i) (hNI i) (hNm i) (M i) (hM i) hMI' r hr
  have hExp r (hr:0≤r): (fun w => Real.exp (X (realTimeClamp r) w))=ᵐ[P] Price (realTimeClamp r) := by
    filter_upwards [ae_all_iff.mpr (fun i => hFub i r hr)] with w hw
    obtain ⟨K,hK,hbound⟩:=hab w r hr
    have hdet:=deterministic_parameter_fubini μ (fun z:E × ℝ => a (z.1,(w,z.2)))
      (ham.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) r hr K hbound
    have he:=integrated_forward_equation μ f0 (fun x => ∫s in 0..r,a (x,(w,s)))
      (fun i x => N i x (realTimeClamp r) w) hf0 hdet.1 (fun i => (hw i).2) _
      (fun i => M i (realTimeClamp r) w) hdet.2 (fun i => (hw i).1.symm)
    rw [hXe w r hr]
    dsimp only [Price]
    rw [real_time_clamp_eq r hr le_top,EReal.toReal_coe]
    exact congrArg Real.exp he.symm
  have hXm t (ht:t<⊤):Measurable[B.F t] (X t) := by
    have hh:Measurable[B.F t] (fun w => A t w+∑i,M i t w) :=
      (hX.variation.adapted t ht).add (hX.martingale.adapted P B.F t ht)
    convert hh using 1
    funext w
    exact hX.decomposition t ht w
  have hE:LocalMProcessWitness P B.F (fun t w => Real.exp (X t w)-Real.exp (X ⊥ w)) := by
    apply local_transfer_fixed_time P hT B.F B.mono _ _ hPrice
    · intro t ht
      exact (hXm t ht).exp.sub (((hXm ⊥ hT).exp).mono (B.mono bot_le) le_rfl)
    · intro w t ht
      exact (Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)).sub continuousAt_const
    · intro t ht
      obtain ⟨r,hr,_,hrt⟩:=finite_closed_time_real t ht
      have he:=hExp r hr
      rw [hrt] at he
      have he0:=hExp 0 le_rfl
      have hz:realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by apply Subtype.ext;rw [real_time_clamp_eq 0 le_rfl le_top];rfl
      rw [hz] at he0
      filter_upwards [he,he0] with w hw h0
      exact congrArg₂ (fun x y:ℝ => x-y) hw.symm h0.symm
  exact hdrift hE
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_drift_from_original_forward_integrals
