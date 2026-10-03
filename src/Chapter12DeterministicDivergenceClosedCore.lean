import Chapter12DeterministicDivergence
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem deterministic_divergence_closed_core {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (h : H) :
    IsDivergence D ((memLp_const h (μ := P) (p := 2)).toLp (fun _ => h)) (W h) := by
  let v : Lp H 2 P := (memLp_const h).toLp (fun _ => h)
  have hh : closure (range (cylinderPair P W S hS hcore 2 (by simp))) ⊆
      {z : Lp ℝ 2 P × Lp H 2 P | inner ℝ z.2 v=inner ℝ z.1 (W h)} := by
    apply closure_minimal
    · rintro _ ⟨c,rfl⟩
      change inner ℝ (c.gradientLp P W S hS hcore 2 (by simp)) v=
        inner ℝ (c.valueLp P W S hS hcore 2 (by simp)) (W h)
      rw [L2.inner_def,L2.inner_def]
      have he := c.direction_ibp P W S hS hcore h
      convert he using 1
      · apply integral_congr_ae
        filter_upwards [(c.gradient_memLp P W S hS hcore 2 (by simp)).coeFn_toLp,
          (memLp_const h (μ := P) (p := 2)).coeFn_toLp] with w hw hv
        dsimp only [SmoothCylinder.gradientLp,v]
        rw [hw,hv]
      · apply integral_congr_ae
        filter_upwards [(c.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hw
        dsimp only [SmoothCylinder.valueLp]
        rw [hw]
        exact mul_comm _ _
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  intro f
  have hf := D.mem_graph f
  change ((f : Lp ℝ 2 P),D f)∈(D.graph : Set _) at hf
  rw [hg] at hf
  exact hh hf

end Asakura.Chapter12
