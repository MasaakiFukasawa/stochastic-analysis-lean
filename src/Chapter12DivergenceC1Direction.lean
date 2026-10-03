import Chapter12DivergenceRawPairing
import Chapter12MalliavinC1Chain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem divergence_C1_direction {Ω H:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P:Measure Ω) [IsProbabilityMeasure P] (W:H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (X:Lp ℝ 2 P) (V B:Lp H 2 P) (G Z:Lp ℝ 2 P)
    (hXV:(X,V)∈D.graph) (hBZ:IsDivergence D B Z)
    (c:ℝ) (hVB:∀ᵐw∂P,inner ℝ (V w) (B w)=c*G w)
    (f df:ℝ → ℝ) (hd:∀x,HasDerivAt f (df x) x) (hdc:Continuous df)
    (C:ℝ) (hC:0≤C) (hb:∀x,|df x|≤C) :
    (∫w,f (X w)*Z w ∂P)=c*(∫w,G w*df (X w) ∂P) := by
  obtain ⟨hi,hpair⟩ := closed_malliavin_C1_chain P W S hS hcore 2 (by simp) D hD hg X V hXV
    f df hd hdc C hC hb
  let Y := lipschitzCompositionLp P 2 (bounded_derivative_lipschitz f df hd C hC hb) X
  have hh := divergence_pairing_raw P D (Y:Ω → ℝ) (Z:Ω → ℝ)
    (hi.toLp _:Ω → H) (B:Ω → H) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _)
    (by simpa only [Lp.toLp_coeFn] using hpair)
    (by simpa only [Lp.toLp_coeFn] using hBZ)
  have hl:(∫w,inner ℝ (hi.toLp _ w) (B w) ∂P)=c*(∫w,G w*df (X w) ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hi.coeFn_toLp,hVB] with w hw hv
    rw [hw,inner_smul_left,hv]
    simp only [starRingEnd_apply,star_trivial]
    ring
  have hr:(∫w,Y w*Z w ∂P)=(∫w,f (X w)*Z w ∂P) := by
    apply integral_congr_ae
    filter_upwards [lipschitzCompositionLp_coe P 2 (bounded_derivative_lipschitz f df hd C hC hb) X] with w hw
    change Y w=f (X w) at hw
    rw [hw]
  exact hr.symm.trans (hh.symm.trans hl)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.divergence_C1_direction
