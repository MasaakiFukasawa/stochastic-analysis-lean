import FullAuditChapter4Gronwall

open MeasureTheory Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem volterra_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U Q G : ℝ → E) (hcU : Continuous U)
    (T L B R : ℝ) (hT : 0≤T) (hL : 0≤L) (hB : 0≤B) (hR : 0≤R)
    (hQ : ∀t,t∈Icc 0 T → ‖Q t‖≤B)
    (hG : ∀t,t∈Icc 0 T → ‖G t‖≤L*‖U t‖+R)
    (heq : ∀t,t∈Icc 0 T → U t=Q t+∫s in 0..t,G s) :
    ∀t,t∈Icc 0 T → ‖U t‖≤(B+T*R)*Real.exp ((L+1)*T) := by
  have hi t (ht : t∈Icc 0 T) : ‖U t‖≤(B+T*R)+(L+1)*∫s in 0..t,‖U s‖ := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) (a:=(0:ℝ)) (b:=t)
      (f:=G) (g:=fun s => L*‖U s‖+R) ht.1
      (ae_of_all _ (fun s hs => hG s ⟨hs.1.le,hs.2.trans ht.2⟩))
      (((hcU.norm.const_mul L).add continuous_const).intervalIntegrable 0 t)
    rw [intervalIntegral.integral_add ((hcU.norm.const_mul L).intervalIntegrable 0 t) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    have hn : 0≤∫s in 0..t,‖U s‖ := intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
    have hb := norm_add_le (Q t) (∫s in 0..t,G s)
    rw [←heq t ht] at hb
    have htR := mul_le_mul_of_nonneg_right ht.2 hR
    linarith [hQ t ht]
  intro t ht
  have hh := Asakura.FullAudit.ch4_gronwall_written (fun s => ‖U s‖) (B+T*R) (L+1) T hT hcU.norm.continuousOn (by linarith) hi t ht
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))) (by positivity))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_norm_bound
