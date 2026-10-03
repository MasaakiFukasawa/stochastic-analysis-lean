import Chapter5GaussianTrace
import Chapter5VectorHeatEndpoint

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The heat equation for the actual Gaussian average, with its Hessian
identified by differentiation under the integral. Bounded second
 derivatives apply in particular to the smooth compact approximants. -/
theorem gaussian_average_heat_equation_lipschitz
    (n : ℕ) (f : (Fin (n+1) → ℝ) → ℝ)
    (D : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (DD : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0)
    (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (x : Fin (n+1) → ℝ) (t : ℝ) (ht : 0 < t) :
    let A := fun s y => ∫ z,f (y+Real.sqrt s • z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
    HasDerivAt (fun s => A s x)
      ((1/2:ℝ) * ∑ i, fderiv ℝ (fderiv ℝ (A t)) x (Pi.single i 1) (Pi.single i 1)) t := by
  let : ContinuousENorm ((Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) →L[ℝ] ℝ) :=
    SeminormedAddGroup.toContinuousENorm (E := ((Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) →L[ℝ] ℝ))
  let : ContinuousENorm ((Fin (n+1) → ℝ) →L[ℝ] ℝ) :=
    SeminormedAddGroup.toContinuousENorm (E := ((Fin (n+1) → ℝ) →L[ℝ] ℝ))
  dsimp only
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hi := gaussian_product_first_moment (n+1)
  obtain ⟨h0,_,_,_⟩ := averaged_bounded_fderiv ν hi f D hd hDc C hD
  obtain ⟨h1,_,_,_⟩ := averaged_bounded_fderiv ν hi D DD hdd hDDc K hDD
  have he : fderiv ℝ (fun y => ∫ z,f (y+Real.sqrt t • z) ∂ν) =
      (fun y => ∫ z,D (y+Real.sqrt t • z) ∂ν) := funext (fun y => (h0 y t).fderiv)
  have hDDi : Integrable (fun z => DD (x+Real.sqrt t • z)) ν :=
    Integrable.of_bound (f := fun z => DD (x+Real.sqrt t • z)) (μ := ν) (hDDc.comp (by fun_prop)).aestronglyMeasurable K (ae_of_all _ fun z => hDD _)
  have hess (i : Fin (n+1)) :
      fderiv ℝ (fderiv ℝ (fun y => ∫ z,f (y+Real.sqrt t • z) ∂ν)) x (Pi.single i 1) (Pi.single i 1) =
      ∫ z,DD (x+Real.sqrt t • z) (Pi.single i 1) (Pi.single i 1) ∂ν := by
    rw [he,(h1 x t).fderiv,ContinuousLinearMap.integral_apply hDDi]
    apply ContinuousLinearMap.integral_apply
    exact Integrable.of_bound (f := fun z => DD (x+Real.sqrt t • z) (Pi.single i 1)) (μ := ν) ((hDDc.comp (by fun_prop)).clm_apply continuous_const).aestronglyMeasurable K
      (ae_of_all _ fun z => by
        calc
          _ ≤ ‖DD (x+Real.sqrt t • z)‖ * ‖(Pi.single i 1 : Fin (n+1) → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ K := by simpa [Pi.norm_single] using hDD (x+Real.sqrt t • z))
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hd y).differentiableAt) (fun y => by
      rw [(hd y).fderiv]
      exact_mod_cast hD y)
  have hfi := vector_lipschitz_average_integrable ν hi f C hl x t
  have htD := vector_average_time_derivative_of_integrable ν hi f D hd hDc C hD x t ht hfi
  have htrace := gaussian_gradient_trace n D DD hdd hDc hDDc C K hD hDD x t
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  convert htD using 1
  dsimp only [ν] at hess
  simp_rw [hess]
  rw [integral_div, htrace]
  field_simp

end Asakura.Chapter5
