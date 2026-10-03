import Chapter10MatrixDriftIntegral
import Chapter10StoppedDriftDensity

open MeasureTheory Set Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000

/-- On a prefix ending no later than T, the stopped prediction drift gives
exactly the ordinary matrix drift. The value at time zero is immaterial. -/
theorem stopped_matrix_drift_integral {d r : ℕ} (T t : ℝ) (ht : 0≤t) (htT : t≤T)
    (H : ℝ → Matrix (Fin d) (Fin r) ℝ) (g : ℝ → Fin r → ℝ) (i : Fin d) :
    (∫ s in 0..t,∑ k,H s i k*((Ioc (0:ℝ) T).indicator (fun s => g s k) s))=
      ∫ s in 0..t,(H s*ᵥg s) i := by
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s hs
  rw [uIoc_of_le ht] at hs
  have hsT : s∈Ioc (0:ℝ) T := ⟨hs.1,hs.2.trans htT⟩
  simp only [Set.indicator_of_mem hsT]
  rfl

/-- Substitute the actual prediction g=Cm; the product is HCm. -/
theorem stopped_prediction_drift_integral {d r n : ℕ} (T t : ℝ) (ht : 0≤t) (htT : t≤T)
    (H : ℝ → Matrix (Fin d) (Fin r) ℝ) (C : ℝ → Matrix (Fin r) (Fin n) ℝ)
    (m : ℝ → Fin n → ℝ) (i : Fin d) :
    (∫ s in 0..t,∑ k,H s i k*((Ioc (0:ℝ) T).indicator (fun s => (C s*ᵥm s) k) s))=
      ∫ s in 0..t,((H s*C s)*ᵥm s) i := by
  rw [stopped_matrix_drift_integral T t ht htT H (fun s => C s*ᵥm s) i]
  simp only [Matrix.mulVec_mulVec]

end Asakura.Chapter10
