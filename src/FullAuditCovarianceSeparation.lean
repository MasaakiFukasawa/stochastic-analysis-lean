import FullAuditCovarianceBilinear

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Test with the difference, use the covariance expectation identity, then
 the checked terminal injectivity of continuous M2 martingales. -/
theorem bounded_cov_separates_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F)
    (hXY : ∀ Z : boundedMProcess P F, ∀ᵐ ω ∂P, ∀ t,
      boundedCov P F hF hle hnull X Z t ω = boundedCov P F hF hle hnull Y Z t ω) :
    ∀ᵐ ω ∂P, ∀ t, X.val t ω = Y.val t ω := by
  let D := X-Y
  have hb := bounded_cov_bilinear P F hF hle hnull Y X D (-1)
  have he : (-1:ℝ) • Y+X = D := by dsimp [D]; module
  rw [he] at hb
  have hz : ∀ᵐ ω ∂P, ∀ t, boundedCov P F hF hle hnull D D t ω = 0 := by
    filter_upwards [hb,hXY D] with ω hb hω
    intro t
    rw [hb t,hω t]
    ring
  have hmean := bounded_cov_mean P F hF hle hnull D D
  have hint : (∫ ω, boundedCov P F hF hle hnull D D ⊤ ω ∂P) = 0 := by
    calc
      _ = ∫ _ : Ω, (0:ℝ) ∂P := integral_congr_ae (hz.mono fun ω h => h ⊤)
      _ = 0 := integral_zero _ _
  have hs : (∫ ω, D.val ⊤ ω^2 ∂P) = 0 := by
    simpa only [pow_two] using hmean.trans hint
  have hi := (memLp_two_iff_integrable_sq (D.property.1.moment ⊤).aestronglyMeasurable).mp (D.property.1.moment ⊤)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg (D.val ⊤ ω)) hi).mp hs
  have hterm : X.val ⊤ =ᵐ[P] Y.val ⊤ := by
    filter_upwards [hae] with ω hω
    have h := sq_eq_zero_iff.mp hω
    exact sub_eq_zero.mp h
  exact continuous_m2_terminal_injective P F hF hle X.val Y.val X.property.1 Y.property.1 hterm

end Asakura.FullAudit
