import Chapter12HilbertOutputCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

/-- The higher derivatives in the vector estimate are values of the same
closed derivative operators, rather than independently assigned arrays. -/
theorem gaussian_hilbert_output_core_graph {Ω : Type*} [MeasurableSpace Ω]
    (H K : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    {N k : ℕ} (u : Fin k → Fin N → GaussianJet N) (e : Fin N → H) (v : Fin k → K)
    (j : ℕ)
    (D : Lp (vectorMalliavinTensorPower H K j) p P →ₗ.[ℝ]
      Lp (vectorMalliavinTensorPower H K (j+1)) p P)
    (hD : ∀ c v,(vectorCylinderValue P W S hS hcore c v p hp,
      vectorCylinderDerivative P W S hS hcore c v p hp)∈D.graph) :
    (gaussianHilbertOutputCore H K P W S hS hcore p hp u e v j,
      gaussianHilbertOutputCore H K P W S hS hcore p hp u e v (j+1))∈D.graph := by
  classical
  have hh := D.graph.sum_mem (fun ab (_ : ab∈(Finset.univ : Finset (Fin k × (Fin (j+1) → Fin N)))) =>
    hD ((gaussianTensorJet (u ab.1) j ab.2).toCylinder e) (vectorTensorFrame H K e v j ab))
  rw [← prod_mk_sum] at hh
  change (gaussianHilbertOutputCore H K P W S hS hcore p hp u e v j,_)∈D.graph at hh
  convert hh using 1
  apply Prod.ext
  · rfl
  unfold gaussianHilbertOutputCore
  simp_rw [vector_cylinder_derivative_finite_sum,GaussianJet.toCylinder_partial]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (j+1+1) => Fin N))]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  simp only [gaussianTensorJet,vectorTensorFrame,Fin.consEquiv_apply,Fin.cons_zero,Fin.tail_cons]
  rfl

end Asakura.Chapter12
