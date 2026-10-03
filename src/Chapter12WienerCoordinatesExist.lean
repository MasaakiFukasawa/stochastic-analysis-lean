import Chapter12VectorWienerGaussian
import Chapter12VectorWienerCoordinatesConstructed

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- No Wiener integral is assumed: a Brownian system supplies its actual
linear isometry and all the Gaussian laws used in the cylinder proofs. -/
theorem actual_wiener_coordinate_isometries_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1)) :
    ∃ J : Fin (d+1) → Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P,
    ∃ W : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ f, W f = ∑ i,J i (f i)) ∧
      (∀ i (f : ℝ → ℝ) (hm : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))),
        ∃ N : HalfClosedTime → Ω → ℝ, ∃ hN : ContinuousM2Witness P B.F N,
          ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
          J i (hi.toLp f) = (hN.moment ⊤).toLp (N ⊤)) ∧
      (∀ f, HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P) := by
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
  obtain ⟨J,W,hW,hJ⟩ := vector_wiener_coordinate_isometries P B c hc hcm hct hcut hcc hco
  refine ⟨J,W,hW,hJ,?_⟩
  apply vector_actual_wiener_gaussian_law P B W
  intro f
  choose N hN hNI he using fun i => hJ i (f i) (Lp.stronglyMeasurable (f i)).measurable (Lp.memLp (f i))
  refine ⟨N,hN,hNI,?_⟩
  rw [hW]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Lp.toLp_coeFn] using he i

end Asakura.Chapter12
