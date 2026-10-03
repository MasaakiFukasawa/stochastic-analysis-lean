import Chapter12ClosedCylinderGraphFromData
import Chapter12GreekDualExponents

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The four Sobolev closures used by the Asian Greek proof are built
from a single Wiener integral and its natural Gaussian information. -/
theorem greek_sobolev_operators {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [SecondCountableTopology H] [CompleteSpace H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (h : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (h t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (hgen : ∀ q : ℝ≥0∞, ∀ f : Lp ℝ q P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) :
    ∃ (D2 : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (D4 : Lp ℝ 4 P →ₗ.[ℝ] Lp H 4 P)
      (D8 : Lp ℝ 8 P →ₗ.[ℝ] Lp H 8 P) (D16 : Lp ℝ 16 P →ₗ.[ℝ] Lp H 16 P),
    D2.IsClosed ∧ D4.IsClosed ∧ D8.IsClosed ∧ D16.IsClosed ∧
    (D2.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))) ∧
    (D4.graph : Set _) = closure (range (cylinderPair P W S hS hcore 4 (by simp))) ∧
    (D8.graph : Set _) = closure (range (cylinderPair P W S hS hcore 8 (by simp))) ∧
    (D16.graph : Set _) = closure (range (cylinderPair P W S hS hcore 16 (by simp))) := by
  obtain ⟨D2,hd2,hg2⟩ := closed_cylinder_graph_from_data P W S hS hcore X hXm hXc h hXW times htimes
    2 2 (by simp) (by simp) (hgen 2)
  obtain ⟨D4,hd4,hg4⟩ := closed_cylinder_graph_from_data P W S hS hcore X hXm hXc h hXW times htimes
    4 (4/3) (by simp) (ENNReal.div_ne_top (by simp) (by norm_num)) (hgen (4/3))
  obtain ⟨D8,hd8,hg8⟩ := closed_cylinder_graph_from_data P W S hS hcore X hXm hXc h hXW times htimes
    8 (8/7) (by simp) (ENNReal.div_ne_top (by simp) (by norm_num)) (hgen (8/7))
  obtain ⟨D16,hd16,hg16⟩ := closed_cylinder_graph_from_data P W S hS hcore X hXm hXc h hXW times htimes
    16 (16/15) (by simp) (ENNReal.div_ne_top (by simp) (by norm_num)) (hgen (16/15))
  exact ⟨D2,D4,D8,D16,hd2,hd4,hd8,hd16,hg2,hg4,hg8,hg16⟩

end Asakura.Chapter12
