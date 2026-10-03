import Chapter12GaussianPathTensorRebasis
import Chapter12GaussianPathTensorLp
import Chapter12LpAffineNormBound
import Chapter12DerivativeCauchyCriterion

open MeasureTheory ProbabilityTheory Set ENNReal Filter TopologicalSpace
open scoped ContDiff Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_path_tensor_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore 2 (by simp)))
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeparableSpace K] [Nonempty K]
    (N : ℕ → ℕ) (e : ∀n,Fin (N n) → H)
    (X : ∀n,(Fin (N n) → ℝ) → C(K,ℝ))
    (hX : ∀n,ContDiff ℝ ∞ (X n))
    (hjX : ∀n t,∃a : GaussianJet (N n),a.f=fun z => X n z t)
    (M : ℕ × ℕ → ℕ) (f : ∀a,Fin (M a) → H)
    (F G : ∀a,(Fin (M a) → ℝ) → C(K,ℝ))
    (hF : ∀a,ContDiff ℝ ∞ (F a)) (hG : ∀a,ContDiff ℝ ∞ (G a))
    (hjF : ∀a t,∃b : GaussianJet (M a),b.f=fun z => F a z t)
    (hjG : ∀a t,∃b : GaussianJet (M a),b.f=fun z => G a z t)
    (hXF : ∀i j,(fun w => X i (fun z => W (e i z) w))=ᵐ[P]
      (fun w => F (i,j) (fun z => W (f (i,j) z) w)))
    (hXG : ∀i j,(fun w => X j (fun z => W (e j z) w))=ᵐ[P]
      (fun w => G (i,j) (fun z => W (f (i,j) z) w)))
    (p : ℝ≥0∞) [Fact (1≤p)] (k : ℕ)
    (hmem : ∀n,MemLp (fun w => gaussianPathTensor H (e n) (X n) k (fun z => W (e n z) w)) p P)
    {E : Type*} [NormedAddCommGroup E]
    (V : ℕ → Lp E p P) (hV : CauchySeq V) (r : ℕ → ℝ)
    (hr : ∀n,0≤r n) (hrlim : Tendsto r atTop (𝓝 0)) (C : ℝ) (hC : 0≤C)
    (hb : ∀i j,∀ᵐw ∂P,
      ‖gaussianPathTensor H (f (i,j)) (F (i,j)) k (fun z => W (f (i,j) z) w)-
        gaussianPathTensor H (f (i,j)) (G (i,j)) k (fun z => W (f (i,j) z) w)‖≤
        C*(‖V i w-V j w‖+r i+r j)) :
    ∃U : Lp C(K,positiveMalliavinTensorPower H k) p P,
      Tendsto (fun n => (hmem n).toLp (fun w => gaussianPathTensor H (e n) (X n) k
        (fun z => W (e n z) w))) atTop (𝓝 U) := by
  let A := fun n => (hmem n).toLp (fun w => gaussianPathTensor H (e n) (X n) k (fun z => W (e n z) w))
  apply cauchySeq_tendsto_of_complete
  apply derivative_cauchy_criterion A V hV r hrlim C hC
  intro i j
  have hi := gaussian_path_tensor_rebasis H P W S hS hcore hdense (e i) (f (i,j))
    (X i) (F (i,j)) (hX i) (hF (i,j)) (hjX i) (hjF (i,j)) (hXF i j) k
  have hj := gaussian_path_tensor_rebasis H P W S hS hcore hdense (e j) (f (i,j))
    (X j) (G (i,j)) (hX j) (hG (i,j)) (hjX j) (hjG (i,j)) (hXG i j) k
  have hbound : ∀ᵐw ∂P,‖(A i-A j) w‖≤C*(‖(V i-V j) w‖+(r i+r j)) := by
    filter_upwards [(hmem i).coeFn_toLp,(hmem j).coeFn_toLp,hi,hj,hb i j,
      Lp.coeFn_sub (A i) (A j),Lp.coeFn_sub (V i) (V j)] with w hai haj hiw hjw hbw haw hvw
    change A i w=_ at hai
    change A j w=_ at haj
    rw [haw,Pi.sub_apply,hai,haj,hiw,hjw,hvw,Pi.sub_apply]
    simpa only [add_assoc] using hbw
  simpa only [add_assoc] using lp_affine_norm_bound P p (A i-A j) (V i-V j) C (r i+r j) hC (add_nonneg (hr i) (hr j)) hbound
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_path_tensor_cauchy
