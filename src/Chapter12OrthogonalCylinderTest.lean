import Chapter12WienerCylinder

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- A cylinder depending on past directions has zero derivative pairing
with a future direction. This is the vanishing term in Clark--Ocone. -/
theorem cylinder_derivative_orthogonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {m : ℕ} (v : Fin m → H) (h : H)
    (hv : ∀ j, ⟪v j,h⟫ = 0) (a : Fin m → ℝ) : ⟪∑ j,a j • v j,h⟫ = 0 := by
  simp only [sum_inner,real_inner_smul_left,hv,mul_zero,Finset.sum_const_zero]

/-- Gaussian integration by parts reduces to the Brownian increment test
when the testing cylinder uses only directions orthogonal to that increment. -/
theorem wiener_orthogonal_cylinder_ibp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {m k : ℕ} (u : Fin m → H) (v : Fin k → H) (h : H)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (hmdf : ∀ j, Measurable (fun x => Df x (Pi.single j 1)))
    (hmdg : ∀ j, Measurable (fun x => Dg x (Pi.single j 1)))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ j, PolyGrowth (fun x => Df x (Pi.single j 1)))
    (hpdg : ∀ j, PolyGrowth (fun x => Dg x (Pi.single j 1)))
    (horth : ∀ j, ⟪v j,h⟫ = 0) :
    (∫ w, g (fun j => W (v j) w)*
      ⟪∑ j,Df (fun j => W (u j) w) (Pi.single j 1) • u j,h⟫ ∂P) =
    ∫ w, f (fun j => W (u j) w)*g (fun j => W (v j) w)*W h w ∂P := by
  rw [wiener_cylindrical_gaussian_ibp P W S hS hcore u v h f g Df Dg
    hf hg hmdf hmdg hpf hpg hpdf hpdg]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only
  rw [cylinder_derivative_orthogonal v h horth,sub_zero,mul_assoc]

end Asakura.Chapter12
