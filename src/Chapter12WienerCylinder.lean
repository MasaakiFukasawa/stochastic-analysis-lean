import Chapter12WienerCoordinates
import Chapter12WienerGaussianClosure

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem wiener_cylindrical_derivative_independent {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {m k : ℕ} (u : Fin m → H) (v : Fin k → H)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (heq : (fun ω => f (fun j => W (u j) ω)) =ᵐ[P]
      fun ω => g (fun j => W (v j) ω)) :
    (fun ω => ∑ j, Df (fun j => W (u j) ω) (Pi.single j 1) • u j) =ᵐ[P]
      fun ω => ∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j := by
  have hlaw := wiener_gaussian_law_from_dense_core P W S hS hcore
  exact cylindrical_derivative_representation_independent P (fun h ω => W h ω)
    (fun _ v c => wiener_finite_linearity P W.toLinearMap v c)
    (fun _ e he => wiener_orthonormal_law P W hlaw e he)
    u v f g Df Dg hf hg heq

theorem wiener_cylindrical_gaussian_ibp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {m k : ℕ} (u : Fin m → H) (v : Fin k → H) (h : H)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (hmdf : ∀ j, Measurable (fun x => Df x (Pi.single j 1)))
    (hmdg : ∀ j, Measurable (fun x => Dg x (Pi.single j 1)))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ j, PolyGrowth (fun x => Df x (Pi.single j 1)))
    (hpdg : ∀ j, PolyGrowth (fun x => Dg x (Pi.single j 1))) :
    (∫ ω, g (fun j => W (v j) ω) *
      ⟪∑ j, Df (fun j => W (u j) ω) (Pi.single j 1) • u j, h⟫ ∂P) =
    ∫ ω, f (fun j => W (u j) ω) * (g (fun j => W (v j) ω) * W h ω -
      ⟪∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j, h⟫) ∂P := by
  have hlaw := wiener_gaussian_law_from_dense_core P W S hS hcore
  exact cylindrical_gaussian_ibp_original P (fun h ω => W h ω)
    (fun _ v c => wiener_finite_linearity P W.toLinearMap v c)
    (fun _ e he => wiener_orthonormal_law P W hlaw e he)
    u v h f g Df Dg hf hg hmdf hmdg hpf hpg hpdf hpdg

end Asakura.Chapter12
