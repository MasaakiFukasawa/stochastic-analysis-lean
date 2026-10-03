import Chapter12GaussianPathTensorCauchy
import Chapter12BrownianGridPathTensorStability
import Chapter12BrownianGridScalarBounds
import Chapter12BrownianForcingFrames

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_path_tensor_limit {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀u,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (p : ℝ≥0∞) [Fact (1≤p)]
    (v : Fin (d+1) → E) (x : E) (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀a,‖iteratedFDeriv ℝ k S a‖≤C)
    (ell : E →L[ℝ] ℝ)
    (n : ℕ → ℕ) (h : ℕ → ℝ) (hn : ∀i,0<n i) (hh : ∀i,0<h i)
    (hnT : ∀i,(n i:ℝ)*h i=T) (hlim : Tendsto h atTop (𝓝 0)) :
    letI := finite_horizon_L2_nontrivial T hT
    let H := finiteWienerHilbertData d T
    let hc := fun u (_ : u∈(univ : Set H)) => hW u
    DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc 2 (by simp)) →
    ∀ (V : ℕ → Lp C(Icc (0:ℝ) T,E) p P), CauchySeq V →
      (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P] (fun w => S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v (h i) (n i) w))) →
      ∃N : ℕ → ℕ,∃e : ∀i,Fin (N i) → H,∃X : ∀i,(Fin (N i) → ℝ) → C(Icc (0:ℝ) T,ℝ),
      (∀i,Orthonormal ℝ (e i)) ∧ (∀i,ContDiff ℝ ∞ (X i)) ∧
      (∀i t,∃a : GaussianJet (N i),a.f=fun z => X i z t) ∧
      (∀i,(fun w => X i (fun j => W (e i j) w))=ᵐ[P]
        (fun w => ell.compLeftContinuous ℝ (Icc (0:ℝ) T) (V i w))) ∧
      ∀k:ℕ,∃U : ℕ → Lp C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k) p P,
        ∃Z : Lp C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k) p P,
        (∀i,(U i : Ω → C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k))=ᵐ[P]
          (fun w => gaussianPathTensor H (e i) (X i) k (fun j => W (e i j) w))) ∧ Tendsto U atTop (𝓝 Z) := by
  intro H hc hdense V hVc hV
  letI := finite_horizon_L2_nontrivial T hT
  letI : Nonempty (Icc (0:ℝ) T) := ⟨⟨0,le_rfl,hT.le⟩⟩
  have hf (a : ℕ × ℕ) := brownian_forcing_frames P d T hT W B hB v
    (h a.1) (h a.2) (hh a.1) (hh a.2) (n a.1) (n a.2) (hnT a.1) (hnT a.2)
  choose m f hf hrepF hrepG using hf
  let N := fun i => m (i,i)+1
  let e := fun i => f (i,i)
  let L := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h i) (n i)) v
  let A := fun a => kernelForcingPath (f a) (fun j => brownianKernelPolygonal d T j (h a.1) (n a.1)) v
  let A' := fun a => kernelForcingPath (f a) (fun j => brownianKernelPolygonal d T j (h a.2) (n a.2)) v
  let X := fun i => scalarForcingPath T S (ContinuousMap.const _ x) (L i) ell
  let F := fun a => scalarForcingPath T S (ContinuousMap.const _ x) (A a) ell
  let G := fun a => scalarForcingPath T S (ContinuousMap.const _ x) (A' a) ell
  have hX i := scalarForcingPath_smooth T S hS (ContinuousMap.const _ x) (L i) ell
  have hF a := scalarForcingPath_smooth T S hS (ContinuousMap.const _ x) (A a) ell
  have hG a := scalarForcingPath_smooth T S hS (ContinuousMap.const _ x) (A' a) ell
  have hjX i := scalarForcingPath_jets T S hS hSB (ContinuousMap.const _ x) (L i) ell
  have hjF a := scalarForcingPath_jets T S hS hSB (ContinuousMap.const _ x) (A a) ell
  have hjG a := scalarForcingPath_jets T S hS hSB (ContinuousMap.const _ x) (A' a) ell
  have hxV i : (fun w => X i (fun j => W (e i j) w))=ᵐ[P]
      (fun w => ell.compLeftContinuous ℝ (Icc (0:ℝ) T) (V i w)) := by
    filter_upwards [hrepF (i,i),hV i] with w hw hvw
    change ell.compLeftContinuous ℝ _ (S (ContinuousMap.const _ x+L i (fun j => W (e i j) w)))=_
    rw [hw,hvw]
  have hfv a : (fun w => F a (fun j => W (f a j) w))=ᵐ[P]
      (fun w => ell.compLeftContinuous ℝ (Icc (0:ℝ) T) (V a.1 w)) := by
    filter_upwards [hrepF a,hV a.1] with w hw hvw
    change ell.compLeftContinuous ℝ _ (S (ContinuousMap.const _ x+A a (fun j => W (f a j) w)))=_
    rw [hw,hvw]
  have hgv a : (fun w => G a (fun j => W (f a j) w))=ᵐ[P]
      (fun w => ell.compLeftContinuous ℝ (Icc (0:ℝ) T) (V a.2 w)) := by
    filter_upwards [hrepG a,hV a.2] with w hw hvw
    change ell.compLeftContinuous ℝ _ (S (ContinuousMap.const _ x+A' a (fun j => W (f a j) w)))=_
    rw [hw,hvw]
  refine ⟨N,e,X,(fun i => hf (i,i)),hX,hjX,hxV,?_⟩
  intro k
  obtain ⟨D,hD,hbD⟩ := brownian_grid_scalar_bounds b hb hbound d T hT.le v x S hS hSeq ell
    N n h hh hn hnT e (fun i => hf (i,i)) (k+1) (by omega)
  have hmem i := gaussian_path_tensor_memLp H P W (e i) (hf (i,i)) (X i) (hX i) k D hD (hbD i) p
  obtain ⟨C,hC,hbC⟩ := brownian_grid_path_tensor_stability b hb hbound d T hT.le v x S hS hSeq ell
    (fun a => m a+1) (fun a => n a.1) (fun a => n a.2) (fun a => h a.1) (fun a => h a.2)
    (fun a => hh a.1) (fun a => hh a.2) (fun a => hn a.1) (fun a => hn a.2)
    (fun a => hnT a.1) (fun a => hnT a.2) f hf k
  have hr : Tendsto (fun i => Real.sqrt (h i)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  have hdiff i j : ∀ᵐw ∂P,
      ‖gaussianPathTensor H (f (i,j)) (F (i,j)) k (fun z => W (f (i,j) z) w)-
        gaussianPathTensor H (f (i,j)) (G (i,j)) k (fun z => W (f (i,j) z) w)‖≤
        C*(‖V i w-V j w‖+Real.sqrt (h i)+Real.sqrt (h j)) := by
    filter_upwards [hrepF (i,j),hrepG (i,j),hV i,hV j] with w hfw hgw hvi hvj
    have hb := hbC (i,j) (fun z => W (f (i,j) z) w)
    dsimp only at hb
    rw [hfw,hgw,←hvi,←hvj] at hb
    simpa only [add_assoc] using hb
  obtain ⟨Z,hZ⟩ := gaussian_path_tensor_cauchy H P W univ dense_univ hc hdense N e X hX hjX
    (fun a => m a+1) f F G hF hG hjF hjG
    (fun i j => (hxV i).trans (hfv (i,j)).symm) (fun i j => (hxV j).trans (hgv (i,j)).symm)
    p k hmem V hVc (fun i => Real.sqrt (h i)) (fun i => Real.sqrt_nonneg _) hr C hC hdiff
  exact ⟨_,Z,(fun i => (hmem i).coeFn_toLp),hZ⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_path_tensor_limit
