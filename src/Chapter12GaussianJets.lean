import Chapter12CylinderPartialDerivative
import Chapter12GaussianProductIBP

open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Smooth finite Gaussian coordinate functions with polynomial bounds
on all derivatives, the class in which the repeated IBP is performed. -/
structure GaussianJet (n : ℕ) where
  f : (Fin n → ℝ) → ℝ
  smooth : ContDiff ℝ ∞ f
  growth : ∀ k : ℕ,∃ C : ℝ,0≤C ∧ ∃ a : ℕ,∀ x,
    ‖iteratedFDeriv ℝ k f x‖≤C*(1+‖x‖)^a

instance {n : ℕ} : CoeFun (GaussianJet n) (fun _ => (Fin n → ℝ) → ℝ) := ⟨GaussianJet.f⟩

noncomputable def GaussianJet.partial {n : ℕ} (f : GaussianJet n) (i : Fin n) : GaussianJet n :=
  ⟨fun x => fderiv ℝ f.f x (Pi.single i 1),
    (f.smooth.fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply contDiff_const,
    iterated_polynomial_growth_directional_derivative f.f f.smooth (Pi.single i 1) f.growth⟩

noncomputable def GaussianJet.iteratedPartial {n : ℕ} (f : GaussianJet n) : List (Fin n) → GaussianJet n
  | [] => f
  | i::is => (f.iteratedPartial is).partial i

theorem GaussianJet.polynomial_growth {n : ℕ} (f : GaussianJet n) : PolyGrowth f.f := by
  obtain ⟨C,hC,a,hb⟩ := f.growth 0
  exact ⟨C,hC,a,fun x => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb x⟩

theorem GaussianJet.all_moments {n : ℕ} (f : GaussianJet n) (p : ENNReal) (hp : p≠⊤) :
    MemLp f.f p (Measure.pi fun _ => gaussianReal 0 1) := by
  exact polynomial_growth_gaussian_memLp f.smooth.continuous.measurable f.polynomial_growth p hp

/-- Coordinate derivatives here are actual one-variable derivatives,
not independent formal symbols supplied to the integration-by-parts lemma. -/
theorem GaussianJet.coordinate_derivative {n : ℕ} (f : GaussianJet (n+1))
    (i : Fin (n+1)) (z : Fin n → ℝ) (y : ℝ) :
    HasDerivAt (fun x => f.f (i.insertNth x z)) ((f.partial i).f (i.insertNth y z)) y := by
  have hh := ((f.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt y
    (insertion_line_derivative i z y)
  simpa only [Function.comp_def,GaussianJet.partial] using hh

end Asakura.Chapter12
