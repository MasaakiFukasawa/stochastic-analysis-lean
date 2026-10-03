import Chapter12CharacteristicDecay
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem weighted_exponential_coordinate_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H f : Ω → ℝ) (ξ : ℝ) (φ : ℂ) (k : ℕ)
    (he : (Complex.I*(ξ:ℂ))^k*φ=
      ∫ w,(H w:ℂ)*Complex.exp (Complex.I*(f w:ℂ)) ∂P) :
    |ξ|^k*‖φ‖≤∫ w,|H w| ∂P := by
  have hn (w) : ‖(H w:ℂ)*Complex.exp (Complex.I*(f w:ℂ))‖=|H w| := by
    simp [norm_mul,Complex.norm_exp]
  have hi := norm_integral_le_integral_norm (μ := P) (fun w => (H w:ℂ)*Complex.exp (Complex.I*(f w:ℂ)))
  rw [←he] at hi
  simpa only [hn,norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] using hi

/-- Repeated weighted IBP gives a uniform polynomial decay bound. The
weights depend on the selected coordinate, never on the Fourier variable. -/
theorem weighted_characteristic_decay {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d k : ℕ} (φ : (Fin (d+1) → ℝ) → ℂ)
    (F : Ω → (Fin (d+1) → ℝ)) (H : Fin (d+1) → Ω → ℝ)
    (hφ : ∀ ξ,‖φ ξ‖≤1)
    (he : ∀ ξ i,(Complex.I*(ξ i:ℂ))^k*φ ξ=
      ∫ w,(H i w:ℂ)*Complex.exp (Complex.I*((∑ j,ξ j*F w j):ℂ)) ∂P) :
    ∃ A : ℝ,0≤A ∧ ∀ ξ,‖φ ξ‖≤A/(1+‖ξ‖)^k := by
  classical
  apply coordinate_power_decay φ (∑ i,∫ w,|H i w| ∂P) hφ
  intro ξ i
  have hi := weighted_exponential_coordinate_bound P (H i) (fun w => ∑ j,ξ j*F w j)
    (ξ i) (φ ξ) k (by simpa using he ξ i)
  exact hi.trans (Finset.single_le_sum (f := fun i => ∫ w,|H i w| ∂P) (fun j _ => integral_nonneg (μ := P) (fun w => abs_nonneg (H j w)))
    (Finset.mem_univ i))

end Asakura.Chapter12
