import Chapter11FiniteLinearIdentification
import Chapter11InvestmentWealth

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Every finite-horizon investment SDE solution has the printed formula.
 Positivity follows from the formula; it is not an assumption on X. -/
theorem investment_solution_identified {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (R : ℝ) (hR : 0<R)
    (hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => π (z.1,z.2.val)))
    (K x r μ σ : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (X M N : HalfClosedTime → Ω → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hM : LocalMProcessWitness P B.F M)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*(σ*π z)) M)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*π z) N)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=x+
      (∫ s in 0..t,X (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) :
    ∀ t∈Icc 0 R,X (realTimeClamp t)=ᵐ[P] fun w => x*
      Real.exp ((∫ s in 0..t,r+π (w,s)*(μ-r)-σ^2*(π (w,s))^2/2)+N (realTimeClamp t) w) := by
  have hbb z : |r+π z*(μ-r)|≤|r|+K*|μ-r| := by
    calc
      _ ≤ |r|+|π z*(μ-r)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul];exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hb z) (abs_nonneg _))
  have hf := finite_linear_original_noise_formula P B R hR
    (fun z => r+π z*(μ-r)) (fun z => σ*π z)
    (measurable_const.add (hm.mul_const _)) (hm.const_mul _)
    (measurable_const.add (hp.mul_const _)) (hp.const_mul _)
    (|r|+K*|μ-r|) (|σ| *K) (by positivity) (by positivity) hbb
    (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg σ))
    X M N (fun _ => x) measurable_const hXa hXc hM hMI hN hNI he
  intro t ht
  filter_upwards [hf t ht] with w hw
  rw [hw]
  congr 2
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  ring

end Asakura.Chapter11
