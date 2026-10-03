import Chapter12GaussianPathTensorCore
import Chapter12CylinderPrescribedJetLimit
import Chapter12ScalarJetOperatorsFromCore

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem path_jet_limit_identification {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (N : ℕ → ℕ) (e : ∀n,Fin (N n) → H)
    (X : ∀n,(Fin (N n) → ℝ) → C(K,ℝ)) (hX : ∀n,ContDiff ℝ ∞ (X n))
    (hjX : ∀n t,∃a : GaussianJet (N n),a.f=fun z => X n z t)
    (V : ℕ → Lp C(K,ℝ) p P) (Z : Lp C(K,ℝ) p P) (hV : Tendsto V atTop (𝓝 Z))
    (hVX : ∀n,(V n : Ω → C(K,ℝ))=ᵐ[P] (fun w => X n (fun i => W (e n i) w)))
    (U : ∀k:ℕ,ℕ → Lp C(K,positiveMalliavinTensorPower H k) p P)
    (A : ∀k:ℕ,Lp C(K,positiveMalliavinTensorPower H k) p P)
    (hU : ∀k,Tendsto (U k) atTop (𝓝 (A k)))
    (hUX : ∀k n,(U k n : Ω → C(K,positiveMalliavinTensorPower H k))=ᵐ[P]
      (fun w => gaussianPathTensor H (e n) (X n) k (fun i => W (e n i) w)))
    (t : K) :
    let J : ∀j:ℕ,Lp (malliavinTensorOrder H j) p P
      | 0 => (ContinuousMap.evalCLM ℝ t).compLp Z
      | j+1 => (ContinuousMap.evalCLM ℝ t).compLp (A j)
    ∀k:ℕ,∃F : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      ∀j:Fin (k+1),F.val j=J j.val := by
  intro J
  choose f hf using fun n => hjX n t
  let c := fun n => (f n).toCylinder (e n)
  obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore p q hp hq hdense
  have h0 n : (c n).valueLp P W S hS hcore p hp=(ContinuousMap.evalCLM ℝ t).compLp (V n) := by
    apply Lp.ext
    filter_upwards [((c n).value_memLp P W S hS hcore p hp).coeFn_toLp,hVX n,
      (ContinuousMap.evalCLM ℝ t).coeFn_compLp (V n)] with w hc hw he
    change (c n).valueLp P W S hS hcore p hp w=(c n).value P W w at hc
    rw [hc,he,hw]
    change (f n).f (fun i => W (e n i) w)=X n (fun i => W (e n i) w) t
    rw [hf n]
  have hk j n : cylinderJetCoordinate H P W S hS hcore p hp (c n) (j+1)=
      (ContinuousMap.evalCLM ℝ t).compLp (U j n) := by
    apply Lp.ext
    have hg := gaussian_path_tensor_core H P W S hS hcore p hp (e n) (X n) (hX n) t (f n) (hf n) D hD j
    filter_upwards [hg,hUX j n,(ContinuousMap.evalCLM ℝ t).coeFn_compLp (U j n)] with w hw hu he
    change (iteratedCylinderExpr H (c n) j).valueLp P W S hS hcore p hp w=_
    rw [hw,he,hu]
    rfl
  have hj (j:ℕ) : Tendsto (fun n => cylinderJetCoordinate H P W S hS hcore p hp (c n) j)
      atTop (𝓝 (J j)) := by
    cases j with
    | zero =>
      change Tendsto (fun n => (c n).valueLp P W S hS hcore p hp) atTop _
      simp_rw [h0]
      exact (((ContinuousMap.evalCLM ℝ t).compLpL p P).continuous.tendsto Z).comp hV
    | succ j =>
      simp_rw [hk]
      exact (((ContinuousMap.evalCLM ℝ t).compLpL p P).continuous.tendsto (A j)).comp (hU j)
  intro k
  exact cylinder_prescribed_jet_limit H P W S hS hcore p hp k c (fun j => J j.val) (fun j => hj j.val)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.path_jet_limit_identification
