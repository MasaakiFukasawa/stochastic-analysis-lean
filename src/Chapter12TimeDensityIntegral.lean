import Chapter12ClockIntegralConstruction
import Chapter12VariationReverseAssociativity

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem variation_integrator_add_constant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)] (c : ℕ → ℝ) (hc : ∀ n,0≤c n)
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (a : Ω → ℝ)
    (hi : VariationIntegralFormula P c hc A H I) :
    VariationIntegralFormula P c hc (fun t w => A t w+a w) H I := by
  intro n
  obtain ⟨ξ,hs,hξ,hint,he⟩ := hi n
  refine ⟨ξ,hs,?_,hint,he⟩
  filter_upwards [hξ] with w hw
  intro s t hst
  rw [hw s t hst];ring

/-- Construct integration against an absolutely continuous bank account
from the actual local L1 condition on its time density. -/
theorem time_density_integral_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (C B : ClosedTime T → Ω → ℝ)
    (hC : ∀ n w r,r∈Icc 0 (c n) → C (realTimeClamp r) w=r)
    (H b : Ω × ℝ → ℝ)
    (hHm : ∀ w,Measurable (fun t => H (w,t))) (hbm : ∀ w,Measurable (fun t => b (w,t)))
    (hbp : ∀ n,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => b (z.1,z.2.val)))
    (hHp : ∀ n,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)*b (z.1,z.2.val)))
    (hbi : ∀ n,∀ᵐ w ∂P,Integrable (fun r => b (w,r)) (volume.restrict (Ioc 0 (c n))))
    (hHi : ∀ n,∀ᵐ w ∂P,Integrable (fun r => H (w,r)*b (w,r)) (volume.restrict (Ioc 0 (c n))))
    (heB : ∀ᵐ w ∂P,∀ n r,r∈Icc 0 (c n) → B (realTimeClamp r) w=B ⊥ w+∫ s in 0..r,b (w,s)) :
    ∃ E : ClosedTime T → Ω → ℝ,AdaptedLocalVariationWitness F E ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => E s w) t) ∧ VariationIntegralFormula P c hc B H E := by
  obtain ⟨J,_,_,hJ⟩ := clock_integral_constructed P F hF hnull c hc hcm hcT hcc C hC b hbp hbi
  obtain ⟨E,hE,hEc,hEI⟩ := clock_integral_constructed P F hF hnull c hc hcm hcT hcc C hC
    (fun z => H z*b z) hHp hHi
  have htime := clock_variation_integral_all_times P C J b c hc hcT hC hJ
  have hJB : ∀ᵐ w ∂P,∀ t,t<⊤ → J t w=B t w-B ⊥ w := by
    filter_upwards [htime,heB] with w hj hb
    intro t ht
    obtain ⟨n,hn⟩ := hcc t ht
    let hp := finitePrefixTime (c n) (hc n) t
    have heq : realTimeClamp hp.val=t := by
      dsimp only [hp]
      rw [finite_prefix_time_clamp (c n) (hc n) (hcT n).le,min_eq_right hn.le]
    have h1 := hj n hp.val hp.property
    have h2 := hb n hp.val hp.property
    rw [heq] at h1 h2
    linarith
  have hBJ := hJ.congr_integral P c hc hcT C J (fun t w => B t w-B ⊥ w) b hJB
  have houter := variation_reverse_associativity P c hc hcT C (fun t w => B t w-B ⊥ w) E H b
    hHm hbm hBJ hEI
  refine ⟨E,hE,hEc,?_⟩
  simpa only [sub_add_cancel] using variation_integrator_add_constant P c hc _ E H (B ⊥) houter

end Asakura.Chapter12
#print axioms Asakura.Chapter12.time_density_integral_constructed
