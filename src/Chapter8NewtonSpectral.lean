import Chapter8NewtonEnergy
import Mathlib.Analysis.InnerProductSpace.Spectrum

open Finset
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def newtonVectorEnergy (δ b : ℝ) (q v : E) : ℝ :=
  (b+δ^2/2)*‖q‖^2 + δ*⟪q,v⟫ + ‖v‖^2

def newtonVectorDissipation (δ b : ℝ) (H : E →ₗ[ℝ] E) (q v : E) : ℝ :=
  δ*⟪q,H q⟫ + 2*⟪v,H q - b • q⟫ + δ*‖v‖^2

/-- The scalar inequality lifts to any symmetric Hessian with spectrum in
[l,u], using the actual orthonormal eigenbasis. -/
theorem newton_spectral_form_bound [FiniteDimensional ℝ E]
    (l u δ b r : ℝ) (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hl : ∀ x, l*‖x‖^2 ≤ ⟪x,H x⟫)
    (hu : ∀ x, ⟪x,H x⟫ ≤ u*‖x‖^2)
    (hscalar : ∀ h, l ≤ h → h ≤ u → ∀ q v,
      2*r*newtonEnergy δ b q v ≤ newtonDissipation δ b h q v)
    (q v : E) :
    2*r*newtonVectorEnergy δ b q v ≤ newtonVectorDissipation δ b H q v := by
  let B := hH.eigenvectorBasis rfl
  let ev := hH.eigenvalues rfl
  have he (i : Fin (Module.finrank ℝ E)) : H (B i) = ev i • B i := hH.apply_eigenvectorBasis rfl i
  have hn (i : Fin (Module.finrank ℝ E)) : ‖B i‖ = 1 := B.orthonormal.norm_eq_one i
  have hi (i : Fin (Module.finrank ℝ E)) : ⟪B i,H (B i)⟫ = ev i := by
    rw [he,inner_smul_right,real_inner_self_eq_norm_sq,hn]; ring
  have hbnd (i : Fin (Module.finrank ℝ E)) : l ≤ ev i ∧ ev i ≤ u := by
    constructor
    · simpa [hi,hn] using hl (B i)
    · simpa [hi,hn] using hu (B i)
  have hcoord (i : Fin (Module.finrank ℝ E)) : ⟪B i,H q⟫ = ev i * ⟪B i,q⟫ := by
    rw [← hH (B i) q,he,real_inner_smul_left]
  have hcross (x y : E) : (∑ i, ⟪B i,x⟫*⟪B i,y⟫) = ⟪x,y⟫ := by
    simpa only [real_inner_comm x] using B.sum_inner_mul_inner x y
  have hsumP : (∑ i, newtonEnergy δ b ⟪B i,q⟫ ⟪B i,v⟫) = newtonVectorEnergy δ b q v := by
    simp only [newtonEnergy,newtonVectorEnergy,sum_add_distrib,mul_assoc,← mul_sum,
      B.sum_sq_inner_right,hcross]
  have hsumR : (∑ i, newtonDissipation δ b (ev i) ⟪B i,q⟫ ⟪B i,v⟫) =
      newtonVectorDissipation δ b H q v := by
    have hdiag : (∑ i, ev i*⟪B i,q⟫^2) = ⟪q,H q⟫ := by
      rw [← hcross q (H q)]
      apply sum_congr rfl
      intro i _
      rw [hcoord]; ring
    have hmixed : (∑ i, (ev i-b)*⟪B i,q⟫*⟪B i,v⟫) = ⟪v,H q-b • q⟫ := by
      rw [← hcross v (H q-b • q)]
      apply sum_congr rfl
      intro i _
      rw [inner_sub_right,inner_smul_right,hcoord]; ring
    calc
      _ = δ*(∑ i, ev i*⟪B i,q⟫^2) + 2*(∑ i, (ev i-b)*⟪B i,q⟫*⟪B i,v⟫) + δ*(∑ i,⟪B i,v⟫^2) := by
        simp only [newtonDissipation,sum_add_distrib,mul_sum]
        congr 2 <;> apply sum_congr rfl <;> intro i _ <;> ring
      _ = _ := by rw [hdiag,hmixed,B.sum_sq_inner_right]; rfl
  have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (Module.finrank ℝ E)))) =>
    hscalar (ev i) (hbnd i).1 (hbnd i).2 ⟪B i,q⟫ ⟪B i,v⟫)
  simpa only [← mul_sum,hsumP,hsumR] using hh

end
end Asakura.Chapter8
