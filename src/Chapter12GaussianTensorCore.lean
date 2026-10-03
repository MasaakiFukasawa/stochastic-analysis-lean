import Chapter12GaussianJetCylinder
import Chapter12TensorCoordinateNorm

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable def gaussianTensorJet {N : ℕ} (u : Fin N → GaussianJet N) :
    (k : ℕ) → (Fin (k+1) → Fin N) → GaussianJet N
  | 0,b => u (b 0)
  | k+1,b => (gaussianTensorJet u k (Fin.tail b)).partial (b 0)

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

noncomputable def gaussianTensorCore {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H)
    (k : ℕ) : Lp (positiveMalliavinTensorPower H k) p P :=
  ∑ b : Fin (k+1) → Fin N,vectorCylinderValue P W S hS hcore
    ((gaussianTensorJet u k b).toCylinder e) (tensorCoordinateFrame H e k b) p hp

/-- Every coordinate level is in the graph of the same closed tensor
Malliavin derivative. The next derivative is constructed, not postulated. -/
theorem gaussian_tensor_core_graph {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H)
    (k : ℕ)
    (D : Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀ c v,(vectorCylinderValue P W S hS hcore c v p hp,
      vectorCylinderDerivative P W S hS hcore c v p hp)∈D.graph) :
    (gaussianTensorCore H P W S hS hcore p hp u e k,
      gaussianTensorCore H P W S hS hcore p hp u e (k+1))∈D.graph := by
  classical
  have hh := D.graph.sum_mem (fun b (_ : b∈(Finset.univ : Finset (Fin (k+1) → Fin N))) =>
    hD ((gaussianTensorJet u k b).toCylinder e) (tensorCoordinateFrame H e k b))
  rw [← prod_mk_sum] at hh
  change (gaussianTensorCore H P W S hS hcore p hp u e k,_)∈D.graph at hh
  convert hh using 1
  apply Prod.ext
  · rfl
  unfold gaussianTensorCore
  simp_rw [vector_cylinder_derivative_finite_sum,GaussianJet.toCylinder_partial]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1+1) => Fin N))]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  simp only [gaussianTensorJet,tensorCoordinateFrame,Fin.consEquiv_apply,Fin.cons_zero,Fin.tail_cons]
  rfl

end Asakura.Chapter12
