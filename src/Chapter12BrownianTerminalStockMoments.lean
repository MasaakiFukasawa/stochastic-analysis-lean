import Chapter12GaussianExponentialLp
import Chapter12WienerCoordinates
import Chapter12BrownianCylinderDensity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem brownian_terminal_stock_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0≤T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (Z : Fin (d+1) → Ω → ℝ)
    (hZ : ∀ j,Z j =ᵐ[P] (W (brownianTimeDirection (j,⟨T,hT,le_rfl⟩)) : Ω → ℝ))
    (a : Fin (d+1) → ℝ) (s : ℝ) (p : ℝ≥0∞) (hp : p≠⊤) :
    MemLp (fun w => s*Real.exp (∑ j,a j*Z j w)) p P := by
  let e := fun j : Fin (d+1) => brownianTimeDirection (j,⟨T,hT,le_rfl⟩)
  let h := ∑ j,a j • e j
  have hi := (gaussian_exponential_memLp P (W h : Ω → ℝ) 0 _ (hlaw h) 1 p hp).const_mul s
  have he : (fun w => s*Real.exp (1*W h w)) =ᵐ[P] (fun w => s*Real.exp (∑ j,a j*Z j w)) := by
    filter_upwards [wiener_finite_linearity P W.toLinearMap e a,ae_all_iff.mpr hZ] with w hw hz
    have hh : W h w=∑ j,a j*W (e j) w := hw
    rw [one_mul,hh]
    congr 2
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun z => a j*z) (hz j).symm)
  exact MemLp.ae_eq he hi

theorem brownian_terminal_stock_indicator_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0≤T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (Z : Fin (d+1) → Ω → ℝ)
    (hZ : ∀ j,Z j =ᵐ[P] (W (brownianTimeDirection (j,⟨T,hT,le_rfl⟩)) : Ω → ℝ))
    (a : Fin (d+1) → ℝ) (s : ℝ) (E : Set Ω) [DecidablePred (fun w => w∈E)] (hE : MeasurableSet E) :
    Integrable (fun w => (if w∈E then (1:ℝ) else 0)*(s*Real.exp (∑ j,a j*Z j w))) P := by
  have hi := (brownian_terminal_stock_memLp P d T hT W hlaw Z hZ a s 2 (by simp)).integrable (by norm_num)
  convert hi.indicator hE using 1
  funext w
  by_cases hw : w∈E <;> simp [hw]

end Asakura.Chapter12
