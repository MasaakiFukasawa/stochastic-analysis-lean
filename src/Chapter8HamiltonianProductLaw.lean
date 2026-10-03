import Chapter8DensityProductCoordinates
import Chapter8NewtonHamiltonian

open MeasureTheory
open scoped BigOperators ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem hamiltonian_density_factor {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (β m : ℝ) (z : Fin (d+d) → ℝ) :
    Real.exp (-β*newtonHamiltonian U m z)=
      Real.exp (-β*U (positionProjection d z))*
        Real.exp (-(β*m/2)*∑ i,(velocityProjection d z i)^2) := by
  rw [newton_hamiltonian_energy,← Real.exp_add]
  congr 1
  ring

theorem hamiltonian_partition_factor {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (β m : ℝ) :
    (∫ z : Fin (d+d) → ℝ,Real.exp (-β*newtonHamiltonian U m z))=
      (∫ q : Fin d → ℝ,Real.exp (-β*U q))*(∫ v : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,v i^2)) := by
  simp_rw [hamiltonian_density_factor]
  have hh := (phase_volume_preserving d).integral_comp'
    (fun p : (Fin d → ℝ) × (Fin d → ℝ) => Real.exp (-β*U p.1)*Real.exp (-(β*m/2)*∑ i,p.2 i^2))
  change (∫ z : Fin (d+d) → ℝ,Real.exp (-β*U (positionProjection d z))*
      Real.exp (-(β*m/2)*∑ i,(velocityProjection d z i)^2))=_ at hh
  rw [hh]
  exact integral_prod_mul (μ := (volume : Measure (Fin d → ℝ))) (ν := volume)
    (fun q : Fin d → ℝ => Real.exp (-β*U q)) (fun v : Fin d → ℝ => Real.exp (-(β*m/2)*∑ i,v i^2))

/-- The normalized phase density is exactly the product of the normalized
position density and normalized Gaussian velocity density. -/
theorem hamiltonian_product_law {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : Continuous U) (β m : ℝ) :
    ((volume : Measure (Fin (d+d) → ℝ)).withDensity (fun z => ENNReal.ofReal
      ((∫ y : Fin (d+d) → ℝ,Real.exp (-β*newtonHamiltonian U m y))⁻¹*
        Real.exp (-β*newtonHamiltonian U m z)))).map (phaseMeasurableEquiv d)=
      (volume.withDensity (fun q : Fin d → ℝ => ENNReal.ofReal
        ((∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U q)))).prod
      (volume.withDensity (fun v : Fin d → ℝ => ENNReal.ofReal
        ((∫ y : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,y i^2))⁻¹*Real.exp (-(β*m/2)*∑ i,v i^2)))) := by
  rw [hamiltonian_partition_factor]
  simp_rw [hamiltonian_density_factor,mul_inv]
  have he : (fun z : Fin (d+d) → ℝ => ENNReal.ofReal
      (((∫ q : Fin d → ℝ,Real.exp (-β*U q))⁻¹*(∫ v : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,v i^2))⁻¹)*
        (Real.exp (-β*U (positionProjection d z))*Real.exp (-(β*m/2)*∑ i,(velocityProjection d z i)^2))))=
      fun z => ENNReal.ofReal
        (((∫ q : Fin d → ℝ,Real.exp (-β*U q))⁻¹*Real.exp (-β*U (positionProjection d z)))*
        ((∫ v : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,v i^2))⁻¹*Real.exp (-(β*m/2)*∑ i,(velocityProjection d z i)^2))) := by
    funext z
    congr 1
    ring
  rw [he]
  apply phase_product_density
    (fun q : Fin d → ℝ => (∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U q))
    (fun v : Fin d → ℝ => (∫ y : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,y i^2))⁻¹*Real.exp (-(β*m/2)*∑ i,v i^2))
  · fun_prop
  · fun_prop
  · intro q
    apply mul_nonneg _ (Real.exp_pos _).le
    exact inv_nonneg.mpr (integral_nonneg (fun y => (Real.exp_pos _).le))
  · intro v
    apply mul_nonneg _ (Real.exp_pos _).le
    exact inv_nonneg.mpr (integral_nonneg (fun y => (Real.exp_pos _).le))

end Asakura.Chapter8
