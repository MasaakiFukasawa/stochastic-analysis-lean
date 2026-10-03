import Chapter12VectorWienerGaussian

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- No Wiener integral is assumed: a Brownian system supplies its actual
linear isometry and all the Gaussian laws used in the cylinder proofs. -/
theorem vector_actual_wiener_isometry_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1)) :
    ∃ W : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ f, HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P) ∧
      (∀ f : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))),
        ∃ N : Fin (d+1) → HalfClosedTime → Ω → ℝ,
        ∃ hN : ∀ i, ContinuousM2Witness P B.F (N i),
          (∀ i, ItoCovarianceFormula P B.F (B.W i) (fun z => f i z.2) (N i)) ∧
          W f = ∑ i, ((hN i).moment ⊤).toLp (N i ⊤)) := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (by simp : (0:EReal)<⊤)
  have hco (r : ℝ) : ∃ n, r ≤ c n := by
    have ht : realTimeClamp (T := ⊤) (max r 0) < ⊤ := by
      change (realTimeClamp (T := ⊤) (max r 0)).val < (⊤ : EReal)
      rw [real_time_clamp_eq _ (le_max_right _ _) le_top]
      exact EReal.coe_lt_top _
    obtain ⟨n,hn⟩ := hcc _ ht
    have hh : ((max r 0 : ℝ) : EReal) < (c n : EReal) := by
      have hh := hn
      change (realTimeClamp (T := ⊤) (max r 0)).val < (realTimeClamp (T := ⊤) (c n)).val at hh
      simpa only [real_time_clamp_eq _ (le_max_right r 0) le_top,
        real_time_clamp_eq _ (hc n).le le_top] using hh
    exact ⟨n,(le_max_left r 0).trans (EReal.coe_lt_coe_iff.mp hh).le⟩
  obtain ⟨W,hW⟩ := vector_wiener_isometry_from_actual_ito P B c hc hcm hct hcut hcc hco
  exact ⟨W,vector_actual_wiener_gaussian_law P B W hW,hW⟩

end Asakura.Chapter12
