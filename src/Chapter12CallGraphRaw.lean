import Chapter12MalliavinCallChain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem closed_call_graph_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : Ω → ℝ) (U : Ω → H) (hF : MemLp F 2 P) (hU : MemLp U 2 P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ D.graph) (K : ℝ) (hno : P {w | F w=K}=0) :
    ∃ hi : MemLp (fun w => max (F w-K) 0) 2 P,
    ∃ hdi : MemLp (fun w => (if K<F w then (1:ℝ) else 0) • U w) 2 P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  have hn : P {w | hF.toLp F w=K}=0 := by
    have hs : {w | hF.toLp F w=K} =ᵐ[P] {w | F w=K} := by
      filter_upwards [hF.coeFn_toLp] with w hw
      simp only [mem_setOf_eq,hw]
    rwa [measure_congr hs]
  obtain ⟨hi,hdi,hchain⟩ := closed_malliavin_call_chain P W S hS hcore 2 (by simp) D hD hg
    (hF.toLp _) (hU.toLp _) hFU K hn
  have hv : (fun w => max (hF.toLp F w-K) 0) =ᵐ[P] (fun w => max (F w-K) 0) := by
    filter_upwards [hF.coeFn_toLp] with w hw
    rw [hw]
  have hdv : (fun w => (if K<hF.toLp F w then (1:ℝ) else 0) • hU.toLp U w) =ᵐ[P]
      (fun w => (if K<F w then (1:ℝ) else 0) • U w) := by
    filter_upwards [hF.coeFn_toLp,hU.coeFn_toLp] with w hw hu
    rw [hw,hu]
  have hj := MemLp.ae_eq hv hi
  have hdj := MemLp.ae_eq hdv hdi
  refine ⟨hj,hdj,?_⟩
  have he : hj.toLp _=hi.toLp _ := Lp.ext (hj.coeFn_toLp.trans (hi.coeFn_toLp.trans hv).symm)
  have hde : hdj.toLp _=hdi.toLp _ := Lp.ext (hdj.coeFn_toLp.trans (hdi.coeFn_toLp.trans hdv).symm)
  rw [he,hde]
  exact hchain

end Asakura.Chapter12
