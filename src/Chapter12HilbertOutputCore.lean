import Chapter12HilbertOutputFrame
import Chapter12GaussianTensorIndexOrder
import Chapter12GaussianVectorMoment

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

variable {Ω : Type*} [MeasurableSpace Ω] (H K : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

noncomputable def gaussianHilbertOutputCore {N k : ℕ}
    (u : Fin k → Fin N → GaussianJet N) (e : Fin N → H) (v : Fin k → K)
    (j : ℕ) : Lp (vectorMalliavinTensorPower H K j) p P :=
  ∑ ab : Fin k × (Fin (j+1) → Fin N),vectorCylinderValue P W S hS hcore
    ((gaussianTensorJet (u ab.1) j ab.2).toCylinder e) (vectorTensorFrame H K e v j ab) p hp

theorem gaussian_hilbert_output_core_coe {N k : ℕ}
    (u : Fin k → Fin N → GaussianJet N) (e : Fin N → H) (v : Fin k → K) (j : ℕ) :
    (gaussianHilbertOutputCore H K P W S hS hcore p hp u e v j : Ω → vectorMalliavinTensorPower H K j)=ᵐ[P]
      (fun w => ∑ ab,(gaussianTensorJet (u ab.1) j ab.2).f (fun i => W (e i) w) •
        vectorTensorFrame H K e v j ab) := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun ab : Fin k × (Fin (j+1) → Fin N) =>
    vectorCylinderValue P W S hS hcore ((gaussianTensorJet (u ab.1) j ab.2).toCylinder e)
      (vectorTensorFrame H K e v j ab) p hp)
  have ht := ae_all_iff.mpr (fun ab : Fin k × (Fin (j+1) → Fin N) =>
    vector_cylinder_value_coe H P W S hS hcore p hp ((gaussianTensorJet (u ab.1) j ab.2).toCylinder e)
      (vectorTensorFrame H K e v j ab))
  filter_upwards [hs,ht] with w hw ht
  change (∑ ab,vectorCylinderValue P W S hS hcore ((gaussianTensorJet (u ab.1) j ab.2).toCylinder e)
    (vectorTensorFrame H K e v j ab) p hp) w=_
  rw [hw]
  exact Finset.sum_congr rfl (fun ab _ => ht ab)

theorem gaussian_vector_recursive_norm {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (j : ℕ) (x : Fin (n+1) → ℝ) :
    gaussianArrayNorm (fun ab : Fin k × (Fin (j+1) → Fin (n+1)) => gaussianTensorJet (u ab.1) j ab.2) x=
      gaussianVectorDerivativeNorm u j x := by
  unfold gaussianArrayNorm gaussianVectorDerivativeNorm
  congr 1
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have hh := gaussian_tensor_array_norm (u a) j x
  have h1 : 0≤∑ b,(gaussianTensorJet (u a) j b).f x^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0≤∑ b,(gaussianDerivativeArray (u a) j b).f x^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact (Real.sqrt_inj h1 h2).mp hh

theorem gaussian_hilbert_output_core_norm {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (e : Fin (n+1) → H) (v : Fin k → K)
    (he : Orthonormal ℝ e) (hv : Orthonormal ℝ v) (j : ℕ) :
    (fun w => ‖gaussianHilbertOutputCore H K P W S hS hcore p hp u e v j w‖)=ᵐ[P]
      (fun w => gaussianVectorDerivativeNorm u j (fun i => W (e i) w)) := by
  filter_upwards [gaussian_hilbert_output_core_coe H K P W S hS hcore p hp u e v j] with w hw
  rw [hw,orthonormal_sum_norm _ (vectorTensorFrame_orthonormal H K e v he hv j)]
  exact gaussian_vector_recursive_norm u j _

end Asakura.Chapter12
