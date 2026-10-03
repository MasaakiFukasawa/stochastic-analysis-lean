import Chapter12CylinderPairLinear
import Chapter12CylinderUnbounded

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The closable cylinder operator has exactly the manuscript's cylinder
class as its domain; taking a span was only a construction device. -/
theorem concrete_cylinder_operator_exact_domain {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) :
    ∃ D : Lp ℝ p P →ₗ.[ℝ] Lp H p P, D.IsClosable ∧
      (D.graph : Set (Lp ℝ p P × Lp H p P)) = range (cylinderPair P W S hS hcore p hp) ∧
      ∀ F, F ∈ D.domain ↔ ∃ c : SmoothCylinder H, c.valueLp P W S hS hcore p hp = F := by
  obtain ⟨D,hg,hclose,hc⟩ := concrete_cylinder_operator P W S hS hcore p q hp hq hdense
  have hgraph : (D.graph : Set (Lp ℝ p P × Lp H p P)) = range (cylinderPair P W S hS hcore p hp) := by
    rw [hg]
    exact cylinderPair_span_eq_range P W S hS hcore p hp
  refine ⟨D,hclose,hgraph,fun F => ⟨?_,?_⟩⟩
  · intro hF
    have hm := D.mem_graph ⟨F,hF⟩
    change (F,D ⟨F,hF⟩) ∈ (D.graph : Set (Lp ℝ p P × Lp H p P)) at hm
    rw [hgraph] at hm
    obtain ⟨c,he⟩ := hm
    exact ⟨c,congrArg Prod.fst he⟩
  · rintro ⟨c,rfl⟩
    have hm := hc c
    obtain ⟨g,hg,_⟩ := D.mem_graph_iff.mp hm
    change (g : Lp ℝ p P) = c.valueLp P W S hS hcore p hp at hg
    rw [← hg]
    exact g.property

/-- The actual cylinder operator cannot satisfy an L2 boundedness estimate,
even though the previous theorem establishes its closability. -/
theorem cylinder_operator_L2_unbounded {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hD : ∀ c : SmoothCylinder H,
      (c.valueLp P W S hS hcore 2 (by simp),c.gradientLp P W S hS hcore 2 (by simp)) ∈ D.graph) :
    ¬∃ C : ℝ, ∀ f : D.domain, ‖D f‖ ≤ C*‖(f : Lp ℝ 2 P)‖ := by
  obtain ⟨h,hh⟩ := exists_norm_eq H (by norm_num : (0:ℝ) ≤ 1)
  rintro ⟨C,hC⟩
  apply concrete_cylinder_derivative_not_bounded P W S hS hcore h hh
  refine ⟨C,fun c => ?_⟩
  obtain ⟨g,hg,he⟩ := D.mem_graph_iff.mp (hD c)
  simpa only [hg,he] using hC g

end Asakura.Chapter12
