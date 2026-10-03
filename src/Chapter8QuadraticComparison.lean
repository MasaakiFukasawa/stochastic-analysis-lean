import Chapter8NewtonThreshold
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Metric
namespace Asakura.Chapter8

/-- Compactness supplies one positive comparison constant for two positive
continuous homogeneous quadratic forms. -/
theorem positive_quadratic_comparison {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    (P R : E → ℝ) (hP : Continuous P) (hR : Continuous R)
    (hp : ∀ x ≠ 0, 0 < P x) (hr : ∀ x ≠ 0, 0 < R x)
    (hPs : ∀ (a : ℝ) x, P (a • x) = a^2 * P x)
    (hRs : ∀ (a : ℝ) x, R (a • x) = a^2 * R x) :
    ∃ c > 0, ∀ x, c * P x ≤ R x := by
  have hn (x : E) (hx : x ∈ sphere (0:E) 1) : x ≠ 0 := by
    intro he
    simpa [he] using hx
  have hc : ContinuousOn (fun x => R x / P x) (sphere (0:E) 1) :=
    hR.continuousOn.div hP.continuousOn (fun x hx => (hp x (hn x hx)).ne')
  obtain ⟨z,hz,hmin⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)) hc
  refine ⟨R z / P z, div_pos (hr z (hn z hz)) (hp z (hn z hz)), ?_⟩
  intro x
  by_cases hx : x = 0
  · have hp0 : P 0 = 0 := by simpa using hPs 0 (0:E)
    have hr0 : R 0 = 0 := by simpa using hRs 0 (0:E)
    simp [hx,hp0,hr0]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := ‖x‖⁻¹ • x
    have hy : y ∈ sphere (0:E) 1 := by
      simp [y,mem_sphere_zero_iff_norm,norm_smul,abs_of_pos hxnorm, hxnorm.ne']
    have hh := (le_div_iff₀ (hp y (hn y hy))).mp (hmin hy)
    dsimp only [y] at hh
    rw [hPs,hRs] at hh
    have hi : 0 < (‖x‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr hxnorm)
    exact (mul_le_mul_iff_of_pos_left hi).mp (by nlinarith only [hh])

end Asakura.Chapter8
