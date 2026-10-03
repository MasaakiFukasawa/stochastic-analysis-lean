import Chapter12StockTimeMomentGraph
import Chapter12ScalarDirectionIntegralPointwise

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem stock_time_moment_graph_explicit {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (T : ℝ) (hT : 0 ≤ T) (μ : Measure (Icc (0:ℝ) T)) [IsFiniteMeasure μ]
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (h : Icc (0:ℝ) T → H) (hh : Continuous h) (hb : ∀ t, ‖h t‖ ≤ Real.sqrt T)
    (hXW : ∀ t, (fun w => X w t) =ᵐ[P] (W (h t) : Ω → ℝ))
    (x σ r : ℝ) (j : ℕ) (G : Ω → ℝ) (hG : MemLp G p P)
    (hSb : ∀ t, ∀ᵐ w ∂P, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖) :
    ∃ hi : MemLp (fun w => ∫ t,t.val^j * stockPathValue x σ r T (X w) t ∂μ) p P,
    ∃ hdi : MemLp (fun w => ∫ t,(t.val^j * stockPathValue x σ r T (X w) t) • (σ • h t) ∂μ) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  obtain ⟨hL,hi,hg⟩ := stock_time_moment_graph P W S hS hcore p hp hp2 D hD hgraph T hT μ
    X hXm h hh hb hXW x σ r j G hG hSb
  let V := fun z : Icc (0:ℝ) T × Ω => z.1.val^j * stockPathValue x σ r T (X z.2) z.1
  have hVm : Measurable V := by
    exact ((measurable_subtype_coe.comp measurable_fst).pow_const j).mul
      (stock_path_joint_measurable x σ r T X hXm)
  have hVc (w) : Continuous (fun t => V (t,w)) := by unfold V stockPathValue; fun_prop
  have hbound (t : Icc (0:ℝ) T) : ∀ᵐ w ∂P, ‖V (t,w)‖ ≤ ‖T^j*G w‖ := by
    filter_upwards [hSb t] with w hw
    dsimp only [V]
    rw [norm_mul,norm_mul]
    rw [show ‖t.val^j‖ = t.val^j from Real.norm_of_nonneg (pow_nonneg t.property.1 j),
      show ‖T^j‖ = T^j from Real.norm_of_nonneg (pow_nonneg hT j)]
    exact mul_le_mul (pow_le_pow_left₀ t.property.1 t.property.2 j) hw (norm_nonneg _) (pow_nonneg hT j)
  have he := scalar_direction_integral_pointwise μ P p hp hp2 V hVm hL hVc
    (fun t => σ • h t) (hh.const_smul σ) (fun w => T^j*G w) (hG.const_mul (T^j)) hbound
  have hdi := (Lp.memLp (∫ t,(ContinuousLinearMap.toSpanSingleton ℝ (σ • h t)).compLp ((hL t).toLp _) ∂μ)).ae_eq he
  refine ⟨hi,hdi,?_⟩
  have hde : hdi.toLp _ = ∫ t,(ContinuousLinearMap.toSpanSingleton ℝ (σ • h t)).compLp ((hL t).toLp _) ∂μ :=
    Lp.ext (hdi.coeFn_toLp.trans he.symm)
  rwa [hde]

end Asakura.Chapter12
