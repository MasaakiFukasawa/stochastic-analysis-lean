import FullAuditCylinderIBP
import Mathlib.Analysis.Calculus.Deriv.Pi

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem PolyGrowth.const {E : Type*} [Norm E] (c : ℝ) : PolyGrowth (fun _ : E => c) := by
  exact ⟨|c|,abs_nonneg _,0,fun x => by simp⟩

theorem PolyGrowth.finset_sum {E ι : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (f : ι → E → ℝ) (hf : ∀ i ∈ s, PolyGrowth (f i)) :
    PolyGrowth (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowth.const (E := E) 0
  | @insert i s hi ih =>
    simp only [Finset.mem_insert] at hf
    simpa only [Finset.sum_insert hi] using (hf i (Or.inl rfl)).add (ih (fun j hj => hf j (Or.inr hj)))

theorem PolyGrowth.comp_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ}
    (hf : PolyGrowth f) (A : E →L[ℝ] F) : PolyGrowth (fun x => f (A x)) := by
  obtain ⟨C,hC,k,hf⟩ := hf
  refine ⟨C*(1+‖A‖)^k,by positivity,k,fun x => ?_⟩
  calc
    |f (A x)| ≤ C*(1+‖A x‖)^k := hf _
    _ ≤ C*((1+‖A‖)*(1+‖x‖))^k := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by positivity)
      have h := A.le_opNorm x
      nlinarith [norm_nonneg A,norm_nonneg x]
    _ = _ := by rw [mul_pow]; ring

/-- A linear differential is the sum of its coordinate values. -/
theorem finite_differential_coordinates {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] ℝ) (v : Fin m → ℝ) :
    L v = ∑ j, v j*L (Pi.single j 1) := by
  have he : v = ∑ j, v j • Pi.single j (1:ℝ) := by
    ext k
    simp [Pi.smul_apply,Pi.single_apply]
  nth_rw 1 [he]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rfl

/-- The insertion line in the coordinate Gaussian integration-by-parts formula. -/
theorem insertion_line_derivative {n : ℕ} (i : Fin (n+1)) (z : Fin n → ℝ) (y : ℝ) :
    HasDerivAt (fun x : ℝ => (i.insertNth x z : Fin (n+1) → ℝ)) (Pi.single (M := fun _ : Fin (n+1) => ℝ) i 1) y := by
  have h := hasDerivAt_update (i.insertNth (0:ℝ) z) i y
  convert h using 1
  funext x
  exact (Fin.update_insertNth (α := fun _ => ℝ) i 0 x z).symm

noncomputable def transformedPartial {n m : ℕ} (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (D : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ) (i : Fin (n+1)) (z : Fin (n+1) → ℝ) : ℝ :=
  ∑ j, (A (Pi.single i 1)) j*D (A z) (Pi.single j 1)

theorem transformed_partial_derivative {n m : ℕ}
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ)
    (D : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (D x) x) (i : Fin (n+1)) (z : Fin n → ℝ) (y : ℝ) :
    HasDerivAt (fun x => f (A (i.insertNth x z))) (transformedPartial A D i (i.insertNth y z)) y := by
  have hline := (A.hasFDerivAt.comp_hasDerivAt y (insertion_line_derivative i z y))
  have h := (hf _).comp_hasDerivAt y hline
  convert h using 1
  · rfl
  · exact (finite_differential_coordinates (D (A (i.insertNth y z))) (A (Pi.single i 1))).symm

theorem transformed_partial_growth {n m : ℕ}
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (D : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (hD : ∀ j, PolyGrowth (fun x => D x (Pi.single j 1))) (i : Fin (n+1)) :
    PolyGrowth (transformedPartial A D i) := by
  apply PolyGrowth.finset_sum
  intro j _
  exact (PolyGrowth.const _).mul ((hD j).comp_linear A)

theorem transformed_partial_measurable {n m : ℕ}
    (A : (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (D : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (hD : ∀ j, Measurable (fun x => D x (Pi.single j 1))) (i : Fin (n+1)) :
    Measurable (transformedPartial A D i) := by
  exact Finset.measurable_sum _ (fun j _ => ((hD j).comp A.continuous.measurable).const_mul _)

end Asakura.FullAudit
