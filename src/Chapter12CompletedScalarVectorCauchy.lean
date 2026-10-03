import Chapter12ScalarVectorJointApproximation
import Chapter12CauchyClosureRelation
open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
theorem sobolev_scalar_vector_product_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x:ℝ×H,‖iteratedFDeriv ℝ j (fun y:ℝ×H => y.1 • y.2) x‖≤K*(1+‖x‖)^a)
    (p q t s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤t)] [Fact (1≤s)]
    [Fact (1≤t*(a+k+1:ℕ))] [HolderConjugate p q] [HolderConjugate (t*(a+k+1:ℕ)) s]
    [HolderTriple t t p]
    (hp : p≠⊤) (hq : q≠⊤) (hr : t*(a+k+1:ℕ)≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (x : ℕ → malliavinSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k)
    (y : ℕ → vectorSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k)
    (z : ℕ → vectorSobolevJetSpace H P W S hS hcore p hp k)
    (hz : ∀n, ((z n).val 0 : Ω → H)=ᵐ[P] (fun w => @HSMul.hSMul ℝ H H inferInstance ((x n).val 0 w) ((y n).val 0 w)))
    (hx : CauchySeq (fun n => WithLp.toLp 1 (fun j => (x n).val j)))
    (hy : CauchySeq (fun n => (y n).val)) :
    CauchySeq (fun n => (z n).val) := by
  refine cauchy_closure_relation
    (fun v : SmoothCylinder H × VectorCylinderExpr H H =>
      (scalarSobolevSumCoreJet H P W S hS hcore (t*(a+k+1:ℕ)) hr k v.1,
       vectorSobolevCoreJet H P W S hS hcore (t*(a+k+1:ℕ)) hr k v.2))
    (fun v : SmoothCylinder H × VectorCylinderExpr H H =>
      vectorSobolevCoreJet H P W S hS hcore p hp k (v.2.scalarProduct v.1))
    ?_ _ _ (hx.prodMk hy) ?_
  · intro v hv
    have hf := uniformContinuous_fst.comp_cauchySeq hv
    have hc := uniformContinuous_snd.comp_cauchySeq hv
    obtain ⟨xf,hxf⟩ := cauchySeq_tendsto_of_complete hf
    obtain ⟨xc,hxc⟩ := cauchySeq_tendsto_of_complete hc
    have hout : ∀j:Fin (k+1),CauchySeq (fun n =>
        (iteratedVectorCylinderExpr H ((v n).2.scalarProduct (v n).1) j.val).valueLp P W S hS hcore p hp) := by
      intro j
      obtain ⟨C,hC,hest⟩ := scalar_vector_core_uniform_estimate H P W S hS hcore
        p q (t*(a+k+1:ℕ)) s hp hq hr hs hdq hds k K hK a hKB j.val (by omega)
      apply paired_jet_polynomial_cauchy (fun i:Fin (k+1) => malliavinTensorOrder H i.val)
        (fun i:Fin (k+1) => positiveMalliavinTensorPower H i.val)
        P p t (a+k+1) (by omega) _ _ _ _ _ hxf hxc C hC
      intro n m
      exact hest (v n).1 (v m).1 (v n).2 (v m).2
    obtain ⟨zz,hzz⟩ := vector_core_jet_cauchy_limit H P W S hS hcore p hp k
      (fun n => (v n).2.scalarProduct (v n).1) hout
    exact hzz.cauchySeq
  · intro n
    obtain ⟨f,c,hf,hc,hout⟩ := sobolev_scalar_vector_product_joint_approximation H P W S hS hcore
      k K hK a hKB p q t s hp hq hr hs hdq hds (x n) (y n) (z n) (hz n)
    apply isClosed_closure.mem_of_tendsto ((hf.prodMk_nhds hc).prodMk_nhds hout)
    exact Eventually.of_forall (fun m => subset_closure (mem_range_self (f m,c m)))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_scalar_vector_product_cauchy
