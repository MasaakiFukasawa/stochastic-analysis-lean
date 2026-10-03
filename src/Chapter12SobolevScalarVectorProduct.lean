import Chapter12ScalarVectorCoreUniformEstimate
import Chapter12PairedJetPolynomialCauchy
import Chapter12ScalarSingleCoreApproximation
import Chapter12VectorCauchyCompletion
import Chapter12LpBinaryIdentityLimit

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_scalar_vector_product {Ω : Type*} [MeasurableSpace Ω]
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
    (x : malliavinSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k)
    (y : vectorSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k) :
    ∃z : vectorSobolevJetSpace H P W S hS hcore p hp k,
      (z.val 0 : Ω → H)=ᵐ[P] (fun w => @HSMul.hSMul ℝ H H inferInstance (x.val 0 w) (y.val 0 w)) := by
  obtain ⟨f,hf⟩ := scalar_single_core_approximation H P W S hS hcore
    (t*(a+k+1:ℕ)) s hr hs hds k x
  obtain ⟨D,hD,hcoreD⟩ := higher_vector_core_operators H P W S hS hcore
    (t*(a+k+1:ℕ)) s hr hs hds
  obtain ⟨c,hc⟩ := vector_sobolev_core_approximation H P W S hS hcore
    (t*(a+k+1:ℕ)) hr k D hcoreD y
  let v := fun n => (c n).scalarProduct (f n)
  have hout : ∀j:Fin (k+1),CauchySeq (fun n =>
      (iteratedVectorCylinderExpr H (v n) j.val).valueLp P W S hS hcore p hp) := by
    intro j
    obtain ⟨C,hC,hest⟩ := scalar_vector_core_uniform_estimate H P W S hS hcore
      p q (t*(a+k+1:ℕ)) s hp hq hr hs hdq hds k K hK a hKB j.val (by omega)
    apply paired_jet_polynomial_cauchy (fun i:Fin (k+1) => malliavinTensorOrder H i.val)
      (fun i:Fin (k+1) => positiveMalliavinTensorPower H i.val)
      P p t (a+k+1) (by omega) _ _ _ _ _ hf hc C hC
    intro n m
    exact hest (f n) (f m) (c n) (c m)
  obtain ⟨Z,hZ⟩ := cauchySeq_tendsto_of_complete (hout 0)
  obtain ⟨z,hz⟩ := vector_cauchy_jet_limit H P W S hS hcore p hp k v hout Z hZ
  refine ⟨z,?_⟩
  rw [hz]
  let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) (t*(a+k+1:ℕ)) P
  let F : Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) (t*(a+k+1:ℕ)) P
  have hf0 : Tendsto (fun n => (f n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr) atTop (𝓝 (x.val 0)) :=
    (((continuous_apply (0:Fin (k+1))).comp (PiLp.continuous_ofLp 1 E)).tendsto _).comp hf
  have hc0 : Tendsto (fun n => (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr) atTop (𝓝 (y.val 0)) :=
    (((continuous_apply (0:Fin (k+1))).comp (PiLp.continuous_ofLp 1 F)).tendsto _).comp hc
  apply lp_binary_identity_limit P (t*(a+k+1:ℕ)) (t*(a+k+1:ℕ)) p (fun (a:ℝ) (u:H) => a • u) (by fun_prop)
    (fun n => (f n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr)
    (fun n => (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr)
    (fun n => (v n).valueLp P W S hS hcore p hp) (x.val 0) (y.val 0) Z hf0 hc0 hZ
  intro n
  filter_upwards [(c n).valueLp_coe H P W S hS hcore (t*(a+k+1:ℕ)) hr,
    (f n).value_memLp P W S hS hcore (t*(a+k+1:ℕ)) hr |>.coeFn_toLp,
    (v n).valueLp_coe H P W S hS hcore p hp] with w hcval hfval hvval
  change (f n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr w=(f n).value P W w at hfval
  rw [hvval,hfval,hcval]
  exact VectorCylinderExpr.scalarProduct_rawValue P W (f n) (c n) w
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_scalar_vector_product
