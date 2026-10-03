import Chapter12CylinderCompositionCauchy
import Chapter12ScalarSingleCoreApproximation
import Chapter12LpContinuousIdentityLimit
import Chapter12CylinderCauchyCompletion

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_smooth_composition {Ω : Type*} [MeasurableSpace Ω]
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
    (x : malliavinSobolevJetSpace H P W S hS hcore (t*(a+k+1:ℕ)) hr k) :
    ∃y : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      (y.val 0 : Ω → ℝ)=ᵐ[P] (fun w => b (x.val 0 w)) := by
  obtain ⟨c,hc⟩ := scalar_single_core_approximation H P W S hS hcore
    (t*(a+k+1:ℕ)) s hr hs hds k x
  have hout := cylinder_composition_cauchy H P W S hS hcore b hb hB k K hK a hKB
    p q t s hp hq hr hs hdq hds c hc.cauchySeq
  let cs := fun n => composeSmoothCylinder (c n) b hb hB
  obtain ⟨f,hf⟩ := cauchySeq_tendsto_of_complete (hout 0)
  obtain ⟨y,hy⟩ := cylinder_cauchy_jet_limit H P W S hS hcore p hp k cs hout f hf
  refine ⟨y,?_⟩
  rw [hy]
  let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) (t*(a+k+1:ℕ)) P
  have hzero : Tendsto (fun n => (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr) atTop (𝓝 (x.val 0)) :=
    (((continuous_apply (0:Fin (k+1))).comp (PiLp.continuous_ofLp 1 E)).tendsto _).comp hc
  apply lp_continuous_identity_limit P (t*(a+k+1:ℕ)) p b hb.continuous
    (fun n => (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr)
    (fun n => (cs n).valueLp P W S hS hcore p hp) (x.val 0) f hzero hf
  intro n
  filter_upwards [(c n).value_memLp P W S hS hcore (t*(a+k+1:ℕ)) hr |>.coeFn_toLp,
    (cs n).value_memLp P W S hS hcore p hp |>.coeFn_toLp] with w hw hz
  change (cs n).valueLp P W S hS hcore p hp w=(cs n).value P W w at hz
  change (c n).valueLp P W S hS hcore (t*(a+k+1:ℕ)) hr w=(c n).value P W w at hw
  rw [hz,hw]
  rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_smooth_composition
