import Chapter13CheyetteState
import Chapter13NoiseAlgebra

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1400000

/-- Disjoint maturity supports leave exactly one coordinate of Gamma. -/
theorem single_period_integral {n:ℕ} (g:Fin n → ℝ → ℝ) (j:Fin n) (a b:ℝ)
    (hab:a≤b) (hzero:∀i,i≠j → ∀s∈Ioc a b,g i s=0) :
    (fun i => ∫s in a..b,g i s)=Pi.single j (∫s in a..b,g j s) := by
  classical
  funext i
  by_cases hij:i=j
  · subst i;simp
  · rw [Pi.single_eq_of_ne hij]
    calc
      (∫s in a..b,g i s)=∫s in a..b,(0:ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with s hs
        exact hzero i hij s (by simpa only [uIoc_of_le hab] using hs)
      _=0 := intervalIntegral.integral_zero

theorem maturity_coefficient_zero (g:ℝ → ℝ) (a b t:ℝ) (hab:a≤b) (hbt:b≤t) :
    (∫s in max a t..max b t,g s)=0 := by rw [max_eq_right (hab.trans hbt),max_eq_right hbt,intervalIntegral.integral_same]

theorem single_row_matrix_contraction {m d:ℕ} (S:Fin m → Fin d → ℝ)
    (j:Fin m) (γ:ℝ) :
    (fun k => ∑i,((Pi.single j γ : Fin m → ℝ) i)*S i k)=(fun k => γ*S j k) := by
  classical
  funext k
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem market_drift_normalization {n d:ℕ} (σ:Fin n → EuclideanSpace ℝ (Fin d))
    (hσ:∀i,σ i≠0) (a γ:Fin n → ℝ) (j:Fin n) :
    γ j * inner ℝ (σ j) (∑i∈Finset.Iic j,(a i*γ i) • σ i)=
      γ j*‖σ j‖*(∑i∈Finset.Iic j,a i*γ i*‖σ i‖*(inner ℝ (σ i) (σ j)/(‖σ i‖*‖σ j‖))) := by
  simp only [inner_sum,real_inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (σ j) (σ i)]
  field_simp [norm_ne_zero_iff.mpr (hσ i),norm_ne_zero_iff.mpr (hσ j)]
  <;> ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.single_period_integral
#print axioms Asakura.Chapter13.maturity_coefficient_zero
#print axioms Asakura.Chapter13.single_row_matrix_contraction
#print axioms Asakura.Chapter13.market_drift_normalization
