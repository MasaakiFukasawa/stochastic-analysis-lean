import Chapter11AffineBarrierTerminal

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- A bounded local C1,2 solution equals the stopped payoff expectation.
 This joins the constructed Ito proof, compact exit exhaustion and terminal
 Gaussian no-atom argument. No stochastic representation is assumed. -/
theorem affine_barrier_candidate_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (y a σ a0 T : ℝ) (hy : y<0) (ha0 : a0<0) (hσ : 0<σ) (hT : 0<T)
    (v : ℝ → ℝ → ℝ) (vt : ℝ × ℝ → ℝ)
    (hv : ∀ t∈Ioo a0 T,ContDiffOn ℝ 2 (v t) (Iio 0))
    (hvt : ∀ t∈Ioo a0 T,∀ x<0,HasDerivAt (fun s => v s x) (vt (t,x)) t)
    (hvc : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Ioo a0 T ×ˢ Iio 0))
    (hvtc : ContinuousOn vt (Ioo a0 T ×ˢ Iio 0))
    (hdxc : ContinuousOn (fun z : ℝ × ℝ => deriv (v z.1) z.2) (Ioo a0 T ×ˢ Iio 0))
    (hxxc : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (v z.1)) z.2) (Ioo a0 T ×ˢ Iio 0))
    (hpde : ∀ t∈Ico 0 T,∀ z<0,vt (t,z)+deriv (v t) z*a+deriv (deriv (v t)) z*σ^2/2=0)
    (hbc : ∀ R∈Ico 0 T,ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Icc 0 R ×ˢ Iic 0))
    (K : ℝ) (hbound : ∀ t∈Ico 0 T,∀ z≤0,|v t z|≤K) 
    (payoff : ℝ → ℝ)
    (hboundary : ∀ t∈Ico 0 T,v t 0=0)
    (hterminal : ∀ z,z<0 → v T z=payoff z)
    (hcont : ∀ z,z<0 → ContinuousWithinAt (fun q : ℝ × ℝ => v q.1 q.2)
      (Icc 0 T ×ˢ Iic 0) (T,z)) :
    let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
    let Y := fun w => if realTimeClamp T<upperBarrierHit (fun t => X t w)
      then payoff (X (realTimeClamp T) w) else 0
    Integrable Y P ∧ (∫ w,Y w ∂P)=v 0 y := by
  apply affine_barrier_terminal_expectation P B y a σ T hy hσ hT v payoff
    hboundary hterminal hcont K hbound
  intro R hR
  exact affine_barrier_preterminal_expectation P B y a σ a0 R T hy ha0 hR.1 hR.2
    v vt hv hvt hvc hvtc hdxc hxxc
    (fun t ht => hpde t ⟨ht.1,ht.2.trans_lt hR.2⟩)
    (hbc R hR) K (fun t ht => hbound t ⟨ht.1,ht.2.trans_lt hR.2⟩)

end Asakura.Chapter11
