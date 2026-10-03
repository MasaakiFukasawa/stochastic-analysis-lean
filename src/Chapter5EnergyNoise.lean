import Chapter2SquareRootCS
import Chapter3StoppedMartingaleFromLp

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The Cauchy-Schwarz step establishing integrability of the square root
of the energy martingale's bracket. U is sup |delta Y|² and V is int |delta Z|². -/
theorem energy_bracket_sqrt_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A U V : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hA : AEStronglyMeasurable A P) (hU : Integrable U P) (hV : Integrable V P)
    (hU0 : ∀ᵐ ω ∂P, 0 ≤ U ω) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hb : ∀ᵐ ω ∂P, A ω ≤ K^2*U ω*V ω) :
    Integrable (fun ω => Real.sqrt (A ω)) P := by
  have hi := (integrable_sqrt_product_bound P U V hU hV hU0 hV0).1.const_mul K
  apply hi.mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hA)
  filter_upwards [hb,hU0,hV0] with ω hbω hu hv
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (A ω) ≤ Real.sqrt (K^2*U ω*V ω) := Real.sqrt_le_sqrt hbω
    _ = K*(Real.sqrt (U ω)*Real.sqrt (V ω)) := by
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg K) hu),Real.sqrt_mul (sq_nonneg K),Real.sqrt_sq hK]
      ring

/-- The stochastic integral in the energy identity really has zero-mean
increments. This applies Chapter 3's p=1 theorem to an actual local
martingale and its covariance, instead of assuming zero expectation. -/
theorem energy_noise_increment_mean_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (N A : ClosedTime T → Ω → ℝ)
    (hN : LocalMProcessWitness P F N) (hNA : LocalCovarianceWitness P F N N A)
    (u : ClosedTime T) (hu : u < ⊤)
    (U V : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hU : Integrable U P) (hV : Integrable V P)
    (hU0 : ∀ᵐ ω ∂P, 0 ≤ U ω) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hb : ∀ᵐ ω ∂P, A u ω ≤ K^2*U ω*V ω)
    (s : ClosedTime T) (hs : s ≤ u) :
    Integrable (fun ω => N u ω-N s ω) P ∧
    (∫ ω, N u ω-N s ω ∂P) = 0 := by
  have hAm : Measurable (A u) := by
    have h1 := (hN.adapted P F u hu).mono (hle u) le_rfl
    have h2 := (hNA.defect.adapted P F u hu).mono (hle u) le_rfl
    have he : A u = fun ω => N u ω*N u ω-(N u ω*N u ω-A u ω) := by funext ω;ring
    rw [he]
    exact (h1.mul h1).sub h2
  have hi := energy_bracket_sqrt_integrable P (A u) U V K hK hAm.aestronglyMeasurable hU hV hU0 hV0 hb
  have hir : Integrable (fun ω => A u ω^((1:ℝ)/2)) P := by simpa only [← Real.sqrt_eq_rpow] using hi
  have hm := stopped_Mp_of_variation_moment P hT F hF hle hnull N A hN hNA
    (fun _ => u) (fun t => by by_cases h : u ≤ t <;> simp [h]) (fun _ => hu) 1 le_rfl hir
  have hmui t : Integrable (fun ω => N (min u t) ω) P :=
    (hm.moment t).integrable (by norm_num)
  have hiu : Integrable (N u) P := by simpa using hmui u
  have his : Integrable (N s) P := by simpa [min_eq_right hs] using hmui s
  refine ⟨hiu.sub his,?_⟩
  have hce : P[N u|F s] =ᵐ[P] N s := by simpa [min_eq_right hs] using hm.martingale s u hs
  have he : (∫ ω, N s ω ∂P) = ∫ ω, N u ω ∂P := by
    rw [← integral_congr_ae hce]
    exact integral_condExp (hle s)
  rw [integral_sub hiu his,he,sub_self]

end Asakura.Chapter5
