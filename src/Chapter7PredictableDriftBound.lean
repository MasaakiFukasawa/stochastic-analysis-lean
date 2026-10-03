import Chapter7PredictableProjectedEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The exact drift--Brownian leading-cross-term estimate written in the
estimator proof. Its adaptedness is used through the preceding grid theorem. -/
theorem predictable_drift_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (hh : 0 ≤ h) (b : Fin n → Ω → ℝ)
    (ha : ∀ k : Fin n,Measurable[B.F (realTimeClamp ((k:ℝ)*h))] (b k))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ k w,|b k w| ≤ K) :
    let Z := fun k : Fin n => fun w => ∑ j,u j*
      (B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w)
    (∫ w,(∑ k,h*b k w*Z k w)^2 ∂P) ≤ K^2*(∑ j,u j^2)*(n:ℝ)*h^3 := by
  classical
  dsimp only
  have hi k : MemLp (b k) 2 P := MemLp.of_bound
    ((ha k).mono (B.le _) le_rfl).aestronglyMeasurable K (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hb k w)
  have hg k : MemLp (fun w => h*b k w) 2 P := (hi k).const_mul h
  have he := predictable_projected_grid_energy P B u h hh (fun k w => h*b k w)
    (fun k => measurable_const.mul (ha k)) hg
  rw [he]
  have hbi k : (∫ w,(h*b k w)^2 ∂P) ≤ h^2*K^2 := by
    have hisq : Integrable (fun w => (h*b k w)^2) P := (memLp_two_iff_integrable_sq (hg k).aestronglyMeasurable).mp (hg k)
    calc
      _ ≤ ∫ _ : Ω,h^2*K^2 ∂P := integral_mono hisq (integrable_const _) (fun w => by
        rw [mul_pow]
        have hx : (b k w)^2 ≤ K^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hb k w)
        exact mul_le_mul_of_nonneg_left hx (sq_nonneg h))
      _ = _ := by simp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hbi k)
  have hnon : 0 ≤ h*(∑ j,u j^2) := mul_nonneg hh (Finset.sum_nonneg (fun j _ => sq_nonneg (u j)))
  have hm := mul_le_mul_of_nonneg_left hsum hnon
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
  convert hm using 1 <;> ring

end Asakura.Chapter7
