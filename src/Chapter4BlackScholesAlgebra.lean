import FullAuditChapter4Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Asakura.Chapter4

/-- The Gaussian exponential tilt behind the density identity in the
Black-Scholes exercise. This is a density calculation, not a verification
of the entire PDE or payoff integral. -/
theorem gaussian_tilt_identity (a z : ℝ) (hz : z ≠ 0) :
    Real.exp a * Real.exp (-((a/z+z/2)^2)/2) =
      Real.exp (-((a/z-z/2)^2)/2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  <;> ring

theorem black_scholes_density_identity (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    let dp := (Real.log (s/K)+(r-q+σ^2/2)*t)/(σ*Real.sqrt t)
    let dm := (Real.log (s/K)+(r-q-σ^2/2)*t)/(σ*Real.sqrt t)
    s*Real.exp ((r-q)*t)*Real.exp (-dp^2/2) = K*Real.exp (-dm^2/2) := by
  dsimp only
  have hz : σ*Real.sqrt t ≠ 0 := by positivity
  have hsq := Real.sq_sqrt ht.le
  have hdp : (Real.log (s/K)+(r-q+σ^2/2)*t)/(σ*Real.sqrt t) =
      (Real.log (s/K)+(r-q)*t)/(σ*Real.sqrt t)+(σ*Real.sqrt t)/2 := by
    field_simp
    nlinarith [hsq]
  have hdm : (Real.log (s/K)+(r-q-σ^2/2)*t)/(σ*Real.sqrt t) =
      (Real.log (s/K)+(r-q)*t)/(σ*Real.sqrt t)-(σ*Real.sqrt t)/2 := by
    field_simp
    nlinarith [hsq]
  rw [hdp,hdm]
  have he : s*Real.exp ((r-q)*t) = K*Real.exp (Real.log (s/K)+(r-q)*t) := by
    rw [Real.exp_add,Real.exp_log (div_pos hs hK)]
    field_simp
  rw [he,mul_assoc,gaussian_tilt_identity _ _ hz]

/-- Substitution of the call's computed time/delta/gamma derivatives in the
printed PDE; the derivative identities must be proved separately. -/
theorem black_scholes_pde_cancellation (s K r q σ t Φp Φm φp : ℝ)
    (hσ : σ ≠ 0) (hs : s ≠ 0) (ht : 0 < t) :
    let C := Real.exp (-q*t)*s*Φp-Real.exp (-r*t)*K*Φm
    let delta := Real.exp (-q*t)*Φp
    let gamma := Real.exp (-q*t)*φp/(s*σ*Real.sqrt t)
    let theta := -q*s*Real.exp (-q*t)*Φp+r*K*Real.exp (-r*t)*Φm+
      s*σ*Real.exp (-q*t)*φp/(2*Real.sqrt t)
    theta+r*C = (r-q)*s*delta+σ^2*s^2*gamma/2 := by
  dsimp only
  field_simp
  <;> ring

end Asakura.Chapter4
