import Chapter12BrownianSolutionSobolevLimit
import Chapter12BrownianForcingSolutionLp
import Chapter12SmoothForcingAllBounds

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem smooth_solution_sobolev {Ω : Type*} {E : Type} [MeasurableSpace Ω]
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
        DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq) →
        MemLp Y p P → ∀(ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T) (k : ℕ),
        ∃J : malliavinSobolevJetSpace H P W univ dense_univ hc p hp k,
          (J.val 0 : Ω → ℝ)=ᵐ[P]
            (fun w => ell (S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w)) t)) := by
  intro H hc
  letI := finite_horizon_L2_nontrivial T hT
  obtain ⟨S,hS,hSeq,hSB⟩ := smooth_forcing_all_bounds b hb hbound T hT.le
  refine ⟨S,hS,hSeq,?_⟩
  intro p q _ _ _ hp hq hdense hYp ell t k
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
  obtain ⟨J,hJ⟩ := brownian_solution_sobolev_limit P d T hT W hW B hB p q hp hq v x b hb hbound
    S hS hSeq hSB ell t n h hn hh hnT hl hdense V Z hV hlim k
  refine ⟨J,?_⟩
  exact hJ.trans (hZ.mono (fun w hw => congrArg (fun z : C(Icc (0:ℝ) T,E) => ell (z t)) hw))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.smooth_solution_sobolev
