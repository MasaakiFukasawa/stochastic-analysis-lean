import Chapter12VectorSquareUniformEstimate
import Chapter12FiniteJetPolynomialCauchy
import Chapter12LpContinuousIdentityLimit
import Chapter12CylinderCauchyCompletion

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_vector_square {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x,‖iteratedFDeriv ℝ j (fun y:H => ‖y‖^2) x‖≤K*(1+‖x‖)^a)
    (p q t s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤t)] [Fact (1≤s)]
    [Fact (1≤t*(a+k+1:ℕ))] [HolderConjugate p q] [HolderConjugate (t*(a+k+1:ℕ)) s]
    [HolderTriple t t p]
    (hp : p≠⊤) (hq : q≠⊤) (hr : t*(a+k+1:ℕ)≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (x : vectorSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k) :
    ∃y : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      (y.val 0 : Ω → ℝ)=ᵐ[P] (fun w => ‖x.val 0 w‖^2) := by
  classical
  obtain ⟨D,hD,hcoreD⟩ := higher_vector_core_operators H P W S hS hcore
    (t*(a+k+1:ℕ)) s hr hs hds
  obtain ⟨c,hc⟩ := vector_sobolev_core_approximation H P W S hS hcore
    (t*(a+k+1:ℕ)) hr k D hcoreD x
  choose f hf using (fun n => vector_cylinder_square_exists H P W S hS hcore (c n))
  have hout : ∀j:Fin (k+1),CauchySeq (fun n => cylinderJetCoordinate H P W S hS hcore p hp (f n) j.val) := by
    intro j
    obtain ⟨C,hC,hest⟩ := vector_square_uniform_estimate H P W S hS hcore
      p q (t*(a+k+1:ℕ)) s hp hq hr hs hdq hds k K hK a hKB j.val (by omega)
    apply finite_jet_polynomial_cauchy (fun i:Fin (k+1) => positiveMalliavinTensorPower H i.val)
      P p t (a+k+1) (by omega) _ _ hc.cauchySeq C hC
    intro n m
    exact hest (c n) (c m) (f n) (f m) (hf n) (hf m)
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (hout 0)
  obtain ⟨y,hy⟩ := cylinder_cauchy_jet_limit H P W S hS hcore p hp k f hout z hz
  refine ⟨y,?_⟩
  rw [hy]
  let E : Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) (t*(a+k+1:ℕ)) P
  have hzero : Tendsto (fun n => (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr) atTop (𝓝 (x.val 0)) :=
    (((continuous_apply (0:Fin (k+1))).comp (PiLp.continuous_ofLp 1 E)).tendsto _).comp hc
  apply lp_continuous_identity_limit P (t*(a+k+1:ℕ)) p (fun u:H => ‖u‖^2) (by fun_prop)
    (fun n => (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr)
    (fun n => (f n).valueLp P W S hS hcore p hp) (x.val 0) z hzero hz
  intro n
  filter_upwards [(c n).valueLp_coe H P W S hS hcore (t*(a+k+1:ℕ)) hr,
    (f n).value_memLp P W S hS hcore p hp |>.coeFn_toLp,hf n] with w hw hfval hsq
  change (f n).valueLp P W S hS hcore p hp w=(f n).value P W w at hfval
  rw [hfval,hw,hsq]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_vector_square
