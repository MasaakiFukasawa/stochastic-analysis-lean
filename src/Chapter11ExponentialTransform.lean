import Chapter11ExponentialSDEIntegrable

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false

/-- Apply Ito to an exponential of the logarithm of wealth. This avoids
silently extending a real power through zero; the resulting noise is M2. -/
theorem exponential_power_transform_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)))
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K L x R a q : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hHb : ∀ z,|H z|≤K) (hbb : ∀ z,|b z|≤L) (hR : 0<R)
    (N V : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) H N)
    (hV : ∀ w t,t∈Icc 0 R → V (realTimeClamp t) w=Real.exp (x+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w)) :
    ∃ U M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F M ∧
      (∀ᵐ w ∂P,∀ t∈Icc 0 R,U (realTimeClamp t) w=Real.exp (a*(R-t))*(V (realTimeClamp t) w)^q) ∧
      (∀ t∈Icc 0 R,U (realTimeClamp t)=ᵐ[P] fun w => Real.exp (a*R+q*x)+
        (∫ s in 0..t,U (realTimeClamp s) w*(q*b (w,s)-a+(q*H (w,s))^2/2))+M (realTimeClamp t) w) ∧
      Measurable (fun z : Ω × ℝ => U (realTimeClamp z.2) z.1) ∧
      (∀ w t,0<U t w) ∧
      Integrable (fun z : Ω × ℝ => U (realTimeClamp z.2) z.1) (P.prod (volume.restrict (Icc 0 R))) ∧
      Integrable (U (realTimeClamp R)) P ∧ Integrable (M (realTimeClamp R)) P ∧ (∫ w,M (realTimeClamp R) w ∂P)=0 := by
  have hbb' z : |q*b z-a|≤|q| *L+|a| := by
    calc
      _ ≤ |q*b z|+|a| := abs_sub _ _
      _ ≤ |q| *L+|a| := by rw [abs_mul];gcongr;exact hbb z
  obtain ⟨U,N',M,hN',hM,hNI',hMI,hpos,he,hsde,hUm,htime,hmom,hM2,hMi,hM0⟩ :=
    exponential_sde_integrable_constructed P B (fun z => q*b z-a) (fun z => q*H z)
      ((hbm.const_mul q).sub_const a) (hHm.const_mul q)
      (fun d hd => ((hbp d hd).const_mul q).sub_const a) (fun d hd => (hHp d hd).const_mul q)
      (|q| *K) (|q| *L+|a|) (a*R+q*x) R (mul_nonneg (abs_nonneg _) hK)
      (add_nonneg (mul_nonneg (abs_nonneg _) hL) (abs_nonneg _))
      (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hHb z) (abs_nonneg _)) hbb' hR
  have hqI : ItoCovarianceFormula P B.F (B.W 0) (fun z => q*H z) (fun t w => q*N t w) := by
    have hh := hNI.add_smul P B.F B.mono B.le (B.W 0) N N H H hNI (q-1)
    convert hh using 1 <;> funext <;> ring
  have hNq := hNI'.unique P (by simp) B.F B.mono B.le B.null (B.W 0) N' (fun t w => q*N t w)
    (fun z => q*H z) (B.martingale 0) hN' (hN.smul P B.F q) hqI
  refine ⟨U,M,hM,?_,hsde,hUm,hpos,?_,?_,hMi,hM0⟩
  · filter_upwards [hNq] with w hw
    intro t ht
    rw [he w t ht,hV w t ht,hw _ (real_time_below t ht.1 (EReal.coe_lt_top t)),←Real.exp_mul,←Real.exp_add]
    have hi := bounded_time_integrable _ (hbm.comp measurable_prodMk_left) L (fun s => hbb (w,s)) t ht.1
    change IntervalIntegrable (fun s => b (w,s)) volume 0 t at hi
    rw [intervalIntegral.integral_sub (hi.const_mul q) (intervalIntegrable_const (c:=a)),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    congr 1
    simp only [sub_zero,smul_eq_mul]
    ring
  · simpa using htime (1:ℝ)
  · simpa using hmom (1:ℝ)

end Asakura.Chapter11
