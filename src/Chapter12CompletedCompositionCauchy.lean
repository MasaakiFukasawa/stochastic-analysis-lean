import Chapter12CompositionJointApproximation
import Chapter12CauchyClosureRelation

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_smooth_composition_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hB : ∀j:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ j b x‖≤C*(1+‖x‖)^a)
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x,‖iteratedFDeriv ℝ j b x‖≤K*(1+‖x‖)^a)
    (p q t s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤t)] [Fact (1≤s)]
    [Fact (1≤t*(a+k+1:ℕ))] [HolderConjugate p q] [HolderConjugate (t*(a+k+1:ℕ)) s]
    [HolderTriple t t p]
    (hp : p≠⊤) (hq : q≠⊤) (hr : t*(a+k+1:ℕ)≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (x : ℕ → malliavinSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k)
    (y : ℕ → malliavinSobolevJetSpace H P W S hS hcore p hp k)
    (hy : ∀n, ( (y n).val 0 : Ω → ℝ)=ᵐ[P] (fun w => b ((x n).val 0 w)))
    (hx : CauchySeq (fun n => WithLp.toLp 1 (fun j => (x n).val j))) :
    CauchySeq (fun n => WithLp.toLp 1 (fun j => (y n).val j)) := by
  refine cauchy_closure_relation
    (fun c : SmoothCylinder H => scalarSobolevSumCoreJet H P W S hS hcore (t*(a+k+1:ℕ)) hr k c)
    (fun c : SmoothCylinder H => scalarSobolevSumCoreJet H P W S hS hcore p hp k (composeSmoothCylinder c b hb hB))
    ?_ _ _ hx ?_
  · intro c hc
    have hout := cylinder_composition_cauchy H P W S hS hcore b hb hB k K hK a hKB
      p q t s hp hq hr hs hdq hds c hc
    obtain ⟨z,hz⟩ := scalar_core_jet_cauchy_limit H P W S hS hcore p hp k
      (fun n => composeSmoothCylinder (c n) b hb hB) hout
    exact hz.cauchySeq
  · intro n
    obtain ⟨c,hc,hb'⟩ := sobolev_smooth_composition_joint_approximation H P W S hS hcore
      b hb hB k K hK a hKB p q t s hp hq hr hs hdq hds (x n) (y n) (hy n)
    apply isClosed_closure.mem_of_tendsto (hc.prodMk_nhds hb')
    exact Eventually.of_forall (fun m => subset_closure (mem_range_self (c m)))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_smooth_composition_cauchy
