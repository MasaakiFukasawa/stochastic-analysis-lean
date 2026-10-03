import Chapter2HalfLineLocalization
import Chapter11ExponentialVariationDensity
import Chapter5ProgressiveDriftVariation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the bank account and its reciprocal from a progressive,
time-integrable rate. The density need not be continuous or bounded. -/
theorem bank_account_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (F : ClosedTime (⊤:EReal) → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (r : Ω × ℝ → ℝ) (hrm : ∀ w,Measurable (fun s => r (w,s)))
    (R : ℝ) (hR : 0≤R)
    (hrp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => r (z.1,z.2.val)))
    (hri : ∀ w,IntervalIntegrable (fun s => r (w,s)) volume 0 R) :
    ∃ B D : ClosedTime (⊤:EReal) → Ω → ℝ,
      AdaptedLocalVariationWitness F B ∧ AdaptedLocalVariationWitness F D ∧
      (∀ w,Continuous (fun t => B t w)) ∧ (∀ w,Continuous (fun t => D t w)) ∧
      (∀ w t,0<B t w ∧ 0<D t w ∧ B t w*D t w=1) ∧
      (∀ w,B ⊥ w=1 ∧ D ⊥ w=1) ∧
      (∀ w t,t∈Icc 0 R → B (realTimeClamp t) w=Real.exp (∫ s in 0..t,r (w,s))) ∧
      (∀ t∈Icc 0 R,B (realTimeClamp t)=ᵐ[P] fun w => 1+∫ s in 0..t,B (realTimeClamp s) w*r (w,s)) ∧
      (∀ t∈Icc 0 R,D (realTimeClamp t)=ᵐ[P] fun w => 1+∫ s in 0..t,D (realTimeClamp s) w*(-r (w,s))) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨A,hA,hAc,hAe⟩ := progressive_integrable_drift_variation hT F hF R hR le_top r hrp
    (fun w => (hri w).1)
  have he w t (ht : t∈Icc 0 R) : A (realTimeClamp t) w=∫ s in 0..t,r (w,s) := by
    rw [hAe,finite_prefix_time_of_real R t hR ht le_top]
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hA0 w : A ⊥ w=0 := by simpa only [hz,intervalIntegral.integral_same] using he w 0 ⟨le_rfl,hR⟩
  let B := fun t w => Real.exp (A t w)
  let D := fun t w => Real.exp (-A t w)
  have hAv : AdaptedLocalVariationWitness F (fun t w => -A t w) := by
    simpa only [neg_one_mul] using hA.smul (-1)
  have hB := exponential_continuous_local_variation F hF A hA (fun w t ht => (hAc w).continuousAt)
  have hD := exponential_continuous_local_variation F hF _ hAv (fun w t ht => (hAc w).continuousAt.neg)
  have hdB := exponential_variation_time_density P hT F hF hle hnull A hA (fun w t ht => (hAc w).continuousAt)
    r hrm R hR (EReal.coe_lt_top R) (ae_of_all _ hri) (ae_of_all _ fun w t ht => by rw [hA0,zero_add];exact he w t ht)
  have hdD := exponential_variation_time_density P hT F hF hle hnull _ hAv (fun w t ht => (hAc w).continuousAt.neg)
    (fun z => -r z) (fun w => (hrm w).neg) R hR (EReal.coe_lt_top R) (ae_of_all _ fun w => (hri w).neg)
    (ae_of_all _ fun w t ht => by rw [hA0,neg_zero,zero_add,he w t ht,intervalIntegral.integral_neg])
  refine ⟨B,D,hB,hD,fun w => Real.continuous_exp.comp (hAc w),fun w => Real.continuous_exp.comp (hAc w).neg,?_,?_,?_,?_,?_⟩
  · intro w t
    exact ⟨Real.exp_pos _,Real.exp_pos _,by dsimp [B,D];rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]⟩
  · intro w
    simp only [B,D,hA0,neg_zero,Real.exp_zero,and_self]
  · intro w t ht
    dsimp only [B]
    rw [he w t ht]
  · intro t ht
    simpa only [B,hA0,Real.exp_zero] using hdB t ht
  · intro t ht
    simpa only [D,hA0,neg_zero,Real.exp_zero] using hdD t ht

end Asakura.Chapter11
