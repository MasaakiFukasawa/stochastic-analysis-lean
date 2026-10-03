import Chapter12SmoothSolutionSobolev
import Chapter12BrownianPathTensorLimit
import Chapter12PathJetLimitIdentification

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem smooth_solution_full_approximation {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀u,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (Y : Ω → C(Icc (0:ℝ) T,Fin (d+1) → ℝ)) (hYm : Measurable Y)
    (hY : ∀w t i,Y w t i=B (i,t) w)
    (v : Fin (d+1) → E) (x : E) (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ)) :
    letI := finite_horizon_L2_nontrivial T hT
    let H := finiteWienerHilbertData d T
    let hc := fun u (_ : u∈(univ : Set H)) => hW u
    ∃S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ S ∧
      (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s))) ∧
      ∀ (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
        (hp : p≠⊤) (hq : q≠⊤),
        DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc 2 (by simp)) →
        DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq) →
        MemLp Y p P →
        ∃V : ℕ → Lp C(Icc (0:ℝ) T,E) p P,∃Z : Lp C(Icc (0:ℝ) T,E) p P,
        (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
          (fun w => S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v (T/(i+1:ℕ)) (i+1) w))) ∧
        (Z : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
          (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w))) ∧
        Tendsto V atTop (𝓝 Z) ∧
        ∀ell : E →L[ℝ] ℝ,
        ∃N : ℕ → ℕ,∃e : ∀i,Fin (N i) → H,∃X : ∀i,(Fin (N i) → ℝ) → C(Icc (0:ℝ) T,ℝ),
        (∀i,ContDiff ℝ ∞ (X i)) ∧ (∀i t,∃f : GaussianJet (N i),f.f=fun z => X i z t) ∧
        (∀i,(fun w => X i (fun j => W (e i j) w))=ᵐ[P]
          (fun w => ell.compLeftContinuous ℝ (Icc (0:ℝ) T) (V i w))) ∧
        ∃U : ∀k:ℕ,ℕ → Lp C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k) p P,
        ∃A : ∀k:ℕ,Lp C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k) p P,
        (∀k,Tendsto (U k) atTop (𝓝 (A k))) ∧
        (∀k i,(U k i : Ω → C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k))=ᵐ[P]
          (fun w => gaussianPathTensor H (e i) (X i) k (fun j => W (e i j) w))) ∧
        ∀t : Icc (0:ℝ) T,
          let J : ∀j:ℕ,Lp (malliavinTensorOrder H j) p P
            | 0 => (ell.comp (ContinuousMap.evalCLM ℝ t)).compLp Z
            | j+1 => (ContinuousMap.evalCLM ℝ t).compLp (A j)
          ∀k:ℕ,∃F : malliavinSobolevJetSpace H P W univ dense_univ hc p hp k,
            ∀j:Fin (k+1),F.val j=J j.val := by
  intro H hc
  letI := finite_horizon_L2_nontrivial T hT
  obtain ⟨S,hS,hSeq,hSB⟩ := smooth_forcing_all_bounds b hb hbound T hT.le
  refine ⟨S,hS,hSeq,?_⟩
  intro p q _ _ _ hp hq hdense2 hdense hYp
  obtain ⟨K,hK⟩ := hbound 1 le_rfl
  have hLip : LipschitzWith K b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hb.differentiable (by simp))
    intro z
    have hn : ‖fderiv ℝ b z‖≤(K:ℝ) := by simpa only [norm_iteratedFDeriv_one] using hK z
    exact_mod_cast hn
  let n := fun i : ℕ => i+1
  let h := fun i : ℕ => T/(i+1:ℕ)
  have hn i : 0<n i := Nat.succ_pos i
  have hh i : 0<h i := div_pos hT (by positivity)
  have hnT i : (n i:ℝ)*h i=T := by dsimp only [n,h]; field_simp
  have hl : Tendsto h atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat T)
  obtain ⟨V,Z,hV,hZ,hlim⟩ := brownian_forcing_solution_Lp P d T hT.le B Y hYm hY p hp hYp
    v x b K hLip S hSeq n h hn hh hnT hl
  refine ⟨V,Z,hV,hZ,hlim,?_⟩
  intro ell
  obtain ⟨N,e,X,he,hX,hjX,hXV,hder⟩ := brownian_path_tensor_limit P d T hT W hW B hB p
    v x b hb hbound S hS hSeq hSB ell n h hn hh hnT hl hdense2 V hlim.cauchySeq hV
  choose U A hUA hlimU using hder
  refine ⟨N,e,X,hX,hjX,hXV,U,A,hlimU,hUA,?_⟩
  let L := ell.compLeftContinuous ℝ (Icc (0:ℝ) T)
  have hlV : Tendsto (fun i => L.compLp (V i)) atTop (𝓝 (L.compLp Z)) :=
    ((L.compLpL p P).continuous.tendsto Z).comp hlim
  have hLX i : (L.compLp (V i) : Ω → C(Icc (0:ℝ) T,ℝ))=ᵐ[P]
      (fun w => X i (fun j => W (e i j) w)) := by
    filter_upwards [L.coeFn_compLp (V i),hXV i] with w hw hxw
    exact hw.trans hxw.symm
  intro t J k
  have hJ0 : (ContinuousMap.evalCLM ℝ t).compLp (L.compLp Z)=
      (ell.comp (ContinuousMap.evalCLM ℝ t)).compLp Z := by
    apply Lp.ext
    filter_upwards [(ContinuousMap.evalCLM ℝ t).coeFn_compLp (L.compLp Z),
      L.coeFn_compLp Z,(ell.comp (ContinuousMap.evalCLM ℝ t)).coeFn_compLp Z] with w hw hlw hzw
    rw [hw,hlw,hzw]
    rfl
  obtain ⟨F,hF⟩ := path_jet_limit_identification H P W univ dense_univ hc p q hp hq hdense
    N e X hX hjX (fun i => L.compLp (V i)) (L.compLp Z) hlV hLX U A hlimU hUA t k
  refine ⟨F,?_⟩
  intro j
  rw [hF]
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact hJ0
  | succ j => rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.smooth_solution_full_approximation
