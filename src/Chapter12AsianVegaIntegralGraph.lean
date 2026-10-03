import Chapter12StockVegaPathGraph
import Chapter12CompactSobolevIntegral

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- Closed Malliavin derivative of J0, with the stock graph and the
Bochner exchange proved in the same derivative operator. -/
theorem asian_vega_integral_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple q q p]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp2 : 2 ≤ p)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hDp : Dp.IsClosed) (hDq : Dq.IsClosed)
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (T : ℝ) (μ : Measure (Icc (0:ℝ) T)) [IsFiniteMeasure μ]
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (h : Icc (0:ℝ) T → H) (hh : Continuous h)
    (hXW : ∀ t, (fun w => X w t) =ᵐ[P] (W (h t) : Ω → ℝ))
    (x σ r : ℝ) (G K : Ω → ℝ) (hG : MemLp G p P) (hK : MemLp K p P)
    (hSb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖)
    (hVb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t*(X w t-σ*t.val)‖ ≤ ‖K w‖) :
    ∃ hi : MemLp (fun w => ∫ t,stockPathValue x σ r T (X w) t*(X w t-σ*t.val) ∂μ) p P,
    ∃ hdi : MemLp (fun w => ∫ t,(stockPathValue x σ r T (X w) t*(σ*(X w t-σ*t.val)+1)) • h t ∂μ) p P,
      (hi.toLp _,hdi.toLp _) ∈ Dp.graph := by
  let F := fun z : Icc (0:ℝ) T × Ω => stockPathValue x σ r T (X z.2) z.1*(X z.2 z.1-σ*z.1.val)
  let U := fun z : Icc (0:ℝ) T × Ω => stockPathValue x σ r T (X z.2) z.1*(σ*(X z.2 z.1-σ*z.1.val)+1)
  have hFm : Measurable F := by
    let f := fun z : Icc (0:ℝ) T × C(Icc (0:ℝ) T,ℝ) => stockPathValue x σ r T z.2 z.1*(z.2 z.1-σ*z.1.val)
    have hf : Continuous f := by unfold f stockPathValue; fun_prop
    exact hf.measurable.comp (measurable_fst.prodMk (hXm.comp measurable_snd))
  have hUm : Measurable U := by
    let f := fun z : Icc (0:ℝ) T × C(Icc (0:ℝ) T,ℝ) => stockPathValue x σ r T z.2 z.1*(σ*(z.2 z.1-σ*z.1.val)+1)
    have hf : Continuous f := by unfold f stockPathValue; fun_prop
    exact hf.measurable.comp (measurable_fst.prodMk (hXm.comp measurable_snd))
  let L := fun w => |σ| * ‖K w‖+‖G w‖
  have hL : MemLp L p P := (hK.norm.const_mul |σ|).add hG.norm
  have hub (t) : ∀ᵐ w ∂P, ‖U (t,w)‖ ≤ ‖L w‖ := by
    filter_upwards [hSb t,hVb t] with w h1 h2
    have he : U (t,w) = σ*F (t,w)+stockPathValue x σ r T (X w) t := by dsimp [U,F]; ring
    rw [he,show ‖L w‖ = |σ| * ‖K w‖+‖G w‖ from Real.norm_of_nonneg (by dsimp [L]; positivity)]
    exact (norm_add_le _ _).trans (by rw [norm_mul,Real.norm_eq_abs]; exact add_le_add (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h1)
  have hFL (t) : MemLp (fun w => F (t,w)) p P :=
    hK.of_le (hFm.comp measurable_prodMk_left).aestronglyMeasurable (hVb t)
  have hUL (t) : MemLp (fun w => U (t,w)) p P :=
    hL.of_le (hUm.comp measurable_prodMk_left).aestronglyMeasurable (hub t)
  have hgraph (t) : ((hFL t).toLp _,(ContinuousLinearMap.toSpanSingleton ℝ (h t)).compLp ((hUL t).toLp _)) ∈ Dp.graph := by
    obtain ⟨hi,hdi,hg⟩ := stock_vega_path_graph P W S hS hcore p q hp hq Dp Dq hDp hDq hgp hgq T X h hXW x σ r t
    have hv : (hFL t).toLp _ = hi.toLp _ := Lp.ext ((hFL t).coeFn_toLp.trans hi.coeFn_toLp.symm)
    have hu : (ContinuousLinearMap.toSpanSingleton ℝ (h t)).compLp ((hUL t).toLp _) = hdi.toLp _ := by
      apply Lp.ext
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ (h t)).coeFn_compLp ((hUL t).toLp _),
        (hUL t).coeFn_toLp,hdi.coeFn_toLp] with w h1 h2 h3
      rw [h1,h3]
      change ((hUL t).toLp _ w) • h t = _
      rw [h2]
    rwa [hv,hu]
  exact compact_sobolev_integral μ P p hp hp2 Dp hDp F U hFm hUm hFL hUL
    (fun w => by unfold F stockPathValue; fun_prop)
    (fun w => by unfold U stockPathValue; fun_prop) h hh K L hK hL hVb hub hgraph

end Asakura.Chapter12
