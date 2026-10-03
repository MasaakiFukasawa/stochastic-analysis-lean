import Chapter12ExponentialFamilyIntegralLp
import Chapter12StockPathEnvelope

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The time moments of Black--Scholes stocks belong to the closed
Sobolev domain. The graph is obtained from the exponential Wiener formula,
with no hypothesis already asserting the derivative of the stock. -/
theorem stock_time_moment_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
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
    ∃ hL : ∀ t : Icc (0:ℝ) T, MemLp (fun w => t.val^j * stockPathValue x σ r T (X w) t) p P,
    ∃ hi : MemLp (fun w => ∫ t,t.val^j * stockPathValue x σ r T (X w) t ∂μ) p P,
      (hi.toLp _,∫ t,(ContinuousLinearMap.toSpanSingleton ℝ (σ • h t)).compLp ((hL t).toLp _) ∂μ) ∈ D.graph := by
  let A := fun t : Icc (0:ℝ) T => t.val^j *x*Real.exp ((r-σ^2/2)*t.val)
  let Y := fun z : Icc (0:ℝ) T × Ω => σ*X z.2 z.1
  have hA : Continuous A := by unfold A; fun_prop
  have hY : Measurable Y := by
    let f := fun z : Icc (0:ℝ) T × C(Icc (0:ℝ) T,ℝ) => σ*z.2 z.1
    have hf : Continuous f := by unfold f; fun_prop
    exact hf.measurable.comp (measurable_fst.prodMk (hXm.comp measurable_snd))
  have hYc (w) : Continuous (fun t => Y (t,w)) := by unfold Y; fun_prop
  have he (t : Icc (0:ℝ) T) (w : Ω) : A t*Real.exp (Y (t,w)) = t.val^j*stockPathValue x σ r T (X w) t := by
    dsimp [A,Y,stockPathValue]
    rw [Real.exp_add]
    ring
  have hYW (t) : (fun w => Y (t,w)) =ᵐ[P] (W (σ • h t) : Ω → ℝ) := by
    rw [map_smul]
    filter_upwards [hXW t,Lp.coeFn_smul σ (W (h t))] with w h1 h2
    rw [h2,Pi.smul_apply]
    change σ*X w t = σ*W (h t) w
    rw [h1]
  have hG' : MemLp (fun w => T^j*G w) p P := hG.const_mul (T^j)
  have hbound (t) : ∀ᵐ w ∂P, ‖A t*Real.exp (Y (t,w))‖ ≤ ‖T^j*G w‖ := by
    filter_upwards [hSb t] with w hw
    rw [he,norm_mul,norm_mul]
    rw [show ‖t.val^j‖ = t.val^j from Real.norm_of_nonneg (pow_nonneg t.property.1 j),
      show ‖T^j‖ = T^j from Real.norm_of_nonneg (pow_nonneg hT j)]
    exact mul_le_mul (pow_le_pow_left₀ t.property.1 t.property.2 j) hw (norm_nonneg _) (pow_nonneg hT j)
  have hfull := exponential_wiener_family_integral_Lp μ P W S hS hcore p hp hp2 D hD hgraph
    A hA Y hY hYc (fun t => σ • h t) (hh.const_smul σ) hYW
    (|σ| *Real.sqrt T) (by positivity)
    (fun t => by rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _))
    _ hG' hbound
  simpa only [he] using hfull

end Asakura.Chapter12
