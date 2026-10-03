import Chapter11DiscountLogDerivatives

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3800000

/-- The printed C1,2 uniqueness class, expressed by its partial derivatives.
 Boundary continuity excludes only the terminal barrier corner. -/
structure StockBarrierCandidate (T b r σ : ℝ) (payoff : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  space : ∀ t∈Ioo 0 T,ContDiffOn ℝ 2 (u t) (Ioo 0 b)
  time : ∀ t∈Ioo 0 T,∀ x∈Ioo 0 b,DifferentiableAt ℝ (fun s => u s x) t
  joint : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (Ioo 0 T ×ˢ Ioo 0 b)
  dt : ContinuousOn (fun z : ℝ × ℝ => deriv (fun s => u s z.2) z.1) (Ioo 0 T ×ˢ Ioo 0 b)
  dx : ContinuousOn (fun z : ℝ × ℝ => deriv (u z.1) z.2) (Ioo 0 T ×ˢ Ioo 0 b)
  dxx : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (u z.1)) z.2) (Ioo 0 T ×ˢ Ioo 0 b)
  pde : ∀ t∈Ioo 0 T,∀ x∈Ioo 0 b,
    deriv (fun s => u s x) t+r*x*deriv (u t) x+σ^2*x^2/2*deriv (deriv (u t)) x-r*u t x=0
  preterminal : ∀ R∈Ico 0 T,ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (Icc 0 R ×ˢ Ioc 0 b)
  bound : ∃ K,0≤K ∧ ∀ t∈Ico 0 T,∀ x∈Ioc 0 b,|u t x|≤K
  boundary : ∀ t∈Ico 0 T,u t b=0
  terminal : ∀ x∈Ioo 0 b,u T x=payoff x
  terminal_continuous : ∀ x∈Ioo 0 b,ContinuousWithinAt (fun z : ℝ × ℝ => u z.1 z.2)
    (Icc 0 T ×ˢ Ioc 0 b) (T,x)

/-- The same class after a strictly positive starting time has been moved
 to zero and the stock has been replaced by its logarithm. -/
structure AffineBarrierCandidate (a σ a0 T : ℝ) (payoff : ℝ → ℝ) (v : ℝ → ℝ → ℝ) : Prop where
  space : ∀ t∈Ioo a0 T,ContDiffOn ℝ 2 (v t) (Iio 0)
  time : ∀ t∈Ioo a0 T,∀ x<0,DifferentiableAt ℝ (fun s => v s x) t
  joint : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Ioo a0 T ×ˢ Iio 0)
  dt : ContinuousOn (fun z : ℝ × ℝ => deriv (fun s => v s z.2) z.1) (Ioo a0 T ×ˢ Iio 0)
  dx : ContinuousOn (fun z : ℝ × ℝ => deriv (v z.1) z.2) (Ioo a0 T ×ˢ Iio 0)
  dxx : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (v z.1)) z.2) (Ioo a0 T ×ˢ Iio 0)
  pde : ∀ t∈Ico 0 T,∀ x<0,
    deriv (fun s => v s x) t+deriv (v t) x*a+deriv (deriv (v t)) x*σ^2/2=0
  preterminal : ∀ R∈Ico 0 T,ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Icc 0 R ×ˢ Iic 0)
  bound : ∃ K,∀ t∈Ico 0 T,∀ x≤0,|v t x|≤K
  boundary : ∀ t∈Ico 0 T,v t 0=0
  terminal : ∀ x,x<0 → v T x=payoff x
  terminal_continuous : ∀ x,x<0 → ContinuousWithinAt (fun z : ℝ × ℝ => v z.1 z.2)
    (Icc 0 T ×ˢ Iic 0) (T,x)

/-- Uniqueness at the initial point, derived from the actual stopped Ito
 proof, not postulated as a probabilistic representation. -/
theorem affine_barrier_candidates_equal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (a σ a0 T y : ℝ) (ha0 : a0<0) (hT : 0<T) (hσ : 0<σ) (hy : y<0)
    (payoff : ℝ → ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : AffineBarrierCandidate a σ a0 T payoff u)
    (hv : AffineBarrierCandidate a σ a0 T payoff v) : u 0 y=v 0 y := by
  let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
  let Y := fun w => if realTimeClamp T<upperBarrierHit (fun t => X t w)
    then payoff (X (realTimeClamp T) w) else 0
  have hrep (f : ℝ → ℝ → ℝ) (hf : AffineBarrierCandidate a σ a0 T payoff f) :
      Integrable Y P ∧ (∫ w,Y w ∂P)=f 0 y := by
    obtain ⟨K,hK⟩ := hf.bound
    exact affine_barrier_candidate_expectation P B y a σ a0 T hy ha0 hσ hT
      f (fun z => deriv (fun s => f s z.2) z.1) hf.space
      (fun t ht x hx => (hf.time t ht x hx).hasDerivAt) hf.joint hf.dt hf.dx hf.dxx
      hf.pde hf.preterminal K hK payoff hf.boundary hf.terminal hf.terminal_continuous
  exact (hrep u hu).2.symm.trans (hrep v hv).2

end Asakura.Chapter11
