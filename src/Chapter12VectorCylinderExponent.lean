import Chapter12VectorCylinderExpressions
import Chapter12LpInclusion

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem lp_inclusion_compLp {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q)
    (L : E →L[ℝ] F) (f : Lp E q P) :
    probabilityLpInclusion P p q hpq (L.compLp f)=L.compLp (probabilityLpInclusion P p q hpq f) := by
  apply Lp.ext
  filter_upwards [probabilityLpInclusion_coe P p q hpq (L.compLp f),
    L.coeFn_compLp f,L.coeFn_compLp (probabilityLpInclusion P p q hpq f),
    probabilityLpInclusion_coe P p q hpq f] with w h1 h2 h3 h4
  rw [h1,h2,h3,h4]

theorem vector_cylinder_exponent {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤)
    (c : VectorCylinderExpr H E) :
    probabilityLpInclusion P p q hpq (c.valueLp P W S hS hcore q hq)=c.valueLp P W S hS hcore p hp := by
  induction c with
  | term c e =>
    change probabilityLpInclusion P p q hpq
      (((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLp (c.valueLp P W S hS hcore q hq)) =
      ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLp (c.valueLp P W S hS hcore p hp)
    rw [lp_inclusion_compLp]
    congr 1
    apply Lp.ext
    exact (probabilityLpInclusion_coe P p q hpq (c.valueLp P W S hS hcore q hq)).trans
      ((c.value_memLp P W S hS hcore q hq).coeFn_toLp.trans
        (c.value_memLp P W S hS hcore p hp).coeFn_toLp.symm)
  | sum n c ih =>
    simp only [VectorCylinderExpr.valueLp,map_sum,ih]
  | smul a c ih =>
    simp only [VectorCylinderExpr.valueLp,map_smul,ih]

end Asakura.Chapter12
