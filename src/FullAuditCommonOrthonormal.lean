import FullAuditCylinderRebasis
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Choose a finite orthonormal system containing every direction used by
 either cylinder and the testing direction. One extra nonzero vector avoids
 a separate zero-dimensional coordinate index. -/
theorem finite_common_orthonormal {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [Nontrivial H] [Fintype ι] (v : ι → H) :
    ∃ (n : ℕ) (e : Fin (n+1) → H) (c : ι → Fin (n+1) → ℝ),
      Orthonormal ℝ e ∧ ∀ j, v j = ∑ i, c j i • e i := by
  classical
  obtain ⟨w,hw⟩ := exists_ne (0:H)
  let S := Submodule.span ℝ (insert w (range v))
  have hwS : w ∈ S := Submodule.subset_span (mem_insert _ _)
  have hvS (j : ι) : v j ∈ S := Submodule.subset_span (mem_insert_of_mem _ (mem_range_self j))
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ ((finite_range v).insert w)
  have hne : (⟨w,hwS⟩ : S) ≠ 0 := fun h => hw (congrArg Subtype.val h)
  letI : Nontrivial S := nontrivial_of_ne _ _ hne
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Module.finrank_pos (R := ℝ) (M := S)))
  let b : OrthonormalBasis (Fin (n+1)) ℝ S := (stdOrthonormalBasis ℝ S).reindex (finCongr hn)
  let e : Fin (n+1) → H := fun i => (b i : H)
  let c := fun j i => b.repr (⟨v j,hvS j⟩ : S) i
  refine ⟨n,e,c,?_,?_⟩
  · exact b.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  · intro j
    have h := congrArg (fun x : S => (x:H)) (b.sum_repr (⟨v j,hvS j⟩ : S))
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using h.symm

noncomputable def cylinderCoordinateMap {n m : ℕ} (c : Fin m → Fin (n+1) → ℝ) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun j => ∑ i, c j i • ContinuousLinearMap.proj i)

theorem cylinder_coordinate_map_apply {n m : ℕ} (c : Fin m → Fin (n+1) → ℝ)
    (z : Fin (n+1) → ℝ) (j : Fin m) : cylinderCoordinateMap c z j = ∑ i, c j i*z i := by
  simp [cylinderCoordinateMap]

theorem cylinder_coordinate_basis {n m : ℕ} (c : Fin m → Fin (n+1) → ℝ)
    (i : Fin (n+1)) (j : Fin m) : cylinderCoordinateMap c (Pi.single i 1) j = c j i := by
  rw [cylinder_coordinate_map_apply]
  simp [Pi.single_apply]

theorem cylindrical_directions_from_coordinates {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n m : ℕ} (e : Fin (n+1) → H) (c : Fin m → Fin (n+1) → ℝ) (j : Fin m) :
    cylindricalDirections e (cylinderCoordinateMap c) j = ∑ i, c j i • e i := by
  simp only [cylindricalDirections,cylinder_coordinate_basis]

end Asakura.FullAudit
