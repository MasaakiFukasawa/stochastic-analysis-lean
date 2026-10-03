import Chapter12BrownianCylinderJetBounds
import Chapter12BrownianSolutionCylinder
import Chapter12CylinderDerivativeLimit

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_solution_sobolev_limit {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀u,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (v : Fin (d+1) → E) (x : E) (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀a,‖iteratedFDeriv ℝ k S a‖≤C)
    (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T)
    (n : ℕ → ℕ) (h : ℕ → ℝ) (hn : ∀i,0<n i) (hh : ∀i,0<h i)
    (hnT : ∀i,(n i:ℝ)*h i=T) (hlim : Tendsto h atTop (𝓝 0)) :
    letI := finite_horizon_L2_nontrivial T hT
    let H := finiteWienerHilbertData d T
    let hc := fun u (_ : u∈(univ : Set H)) => hW u
    ∀ (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq))
      (V : ℕ → Lp C(Icc (0:ℝ) T,E) p P) (Z : Lp C(Icc (0:ℝ) T,E) p P),
      (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P] (fun w => S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v (h i) (n i) w))) →
      Tendsto V atTop (𝓝 Z) →
      ∀k:ℕ,∃J : malliavinSobolevJetSpace H P W univ dense_univ hc p hp k,
        (J.val 0 : Ω → ℝ)=ᵐ[P] (fun w => ell (Z w t)) := by
  intro H hc hdense V Z hV hZ
  letI := finite_horizon_L2_nontrivial T hT
  have hex i := brownian_solution_cylinder P d T hT W B hB v x S hS hSB ell t (h i) (hh i) (n i) (hnT i)
  choose c hcv using hex
  let R : C(Icc (0:ℝ) T,E) →L[ℝ] ℝ := ell.comp (ContinuousMap.evalCLM ℝ t)
  have heq i : (c i).valueLp P W univ dense_univ hc p hp=R.compLp (V i) := by
    apply Lp.ext
    filter_upwards [((c i).value_memLp P W univ dense_univ hc p hp).coeFn_toLp,
      hcv i,hV i,R.coeFn_compLp (V i)] with w hw hcw hvw hrw
    change (c i).valueLp P W univ dense_univ hc p hp w=(c i).value P W w at hw
    rw [hw,hcw,hrw,hvw]
    rfl
  have h0 : Tendsto (fun i => (c i).valueLp P W univ dense_univ hc p hp) atTop (𝓝 (R.compLp Z)) := by
    simp_rw [heq]
    exact ((R.compLpL p P).continuous.tendsto Z).comp hZ
  have hr : Tendsto (fun i => Real.sqrt (h i)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  have hbC := brownian_cylinder_jet_bounds P d T hT W hW B hB p q hp hq v x b hb hbound
    S hS hSeq hSB ell t n h hn hh hnT hdense c V hcv hV
  intro k
  obtain ⟨J,hJ⟩ := cylinder_derivative_limit H P W univ dense_univ hc p hp c (R.compLp Z) h0
    V hZ.cauchySeq (fun i => Real.sqrt (h i)) hr hbC k
  refine ⟨J,?_⟩
  rw [hJ]
  exact R.coeFn_compLp Z
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_solution_sobolev_limit
