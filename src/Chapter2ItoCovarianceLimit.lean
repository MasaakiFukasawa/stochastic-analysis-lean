import FullAuditBoundedKW
import Chapter2CovarianceLimit
import Chapter2SignedElementaryIntegral
import Chapter2ElementaryFiniteSum
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The general covariance formula at a fixed finite time, proved from
actual elementary integrals. Signed measures are tied to the original
covariance increments, and both probability error terms are derived.
The concrete Stieltjes construction supplies the interval hypotheses. -/
theorem ito_covariance_from_elementary_limits
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X Y C B Z D : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F X Y C) (hB : LocalCovarianceWitness P F Y Y B)
    (hD : LocalCovarianceWitness P F Z Y D)
    (t : ClosedTime T) (ht : t < ⊤)
    (α β : Ω → Measure ℝ) (ν : Ω → SignedMeasure ℝ)
    [∀ ω, IsFiniteMeasure (α ω)] [∀ ω, IsFiniteMeasure (β ω)] [∀ ω, NullSingletonClass (α ω)]
    (hcs : ∀ᵐ ω ∂P, ∀ a b, a ≤ b → |ν ω (Ioc a b)| ≤
      Real.sqrt ((α ω).real (Ioc a b))*Real.sqrt ((β ω).real (Ioc a b)))
    (hβ : Measurable (fun ω => (β ω).real univ))
    (N : ℕ → ℕ) (a b : (n : ℕ) → Fin (N n) → ℝ) (G : (n : ℕ) → Fin (N n) → Ω → ℝ)
    (hab : ∀ n i, a n i ≤ b n i)
    (hGm : ∀ n i, Measurable[F (realTimeClamp (a n i))] (G n i))
    (hGi : ∀ n i, MemLp (G n i) ∞ P)
    (hν : ∀ n, ∀ᵐ ω ∂P, ∀ i, ν ω (Ioc (a n i) (b n i)) =
      C (min (realTimeClamp (b n i)) t) ω-C (min (realTimeClamp (a n i)) t) ω)
    (H : Ω → ℝ → ℝ) (hHm : ∀ ω, Measurable (H ω))
    (hH : ∀ᵐ ω ∂P, MemLp (H ω) 2 (α ω))
    (he : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ ∫ r,
      ((∑ i, (Ico (a n i) (b n i)).indicator (fun _ => G n i ω) r)-H ω r)^2 ∂α ω}) atTop (𝓝 0))
    (hprob : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ⨆ s,
      |(∑ i, G n i ω*(X (min (realTimeClamp (b n i)) (min t s)) ω-
        X (min (realTimeClamp (a n i)) (min t s)) ω))-Z (min t s) ω|}) atTop (𝓝 0)) :
    D t =ᵐ[P] fun ω => signedIntegralRaw (ν ω) (H ω) := by
  classical
  let W := fun n s ω => ∑ i, G n i ω*(X (min (realTimeClamp (b n i)) s) ω-X (min (realTimeClamp (a n i)) s) ω)
  let J := fun n ω r => ∑ i, (Ico (a n i) (b n i)).indicator (fun _ => G n i ω) r
  have hall n := finite_elementary_integral_covariance P F hF hle hnull X Y C hX hY hC
    Finset.univ (fun i => realTimeClamp (a n i)) (fun i => realTimeClamp (b n i)) (G n)
    (fun i => real_time_clamp_mono (hab n i)) (hGm n) (hGi n)
  choose Q hQ hQi using fun n => (hall n).2
  have hqp := covariance_probability_continuity P F hF hle hnull W Q Z Y B D
    (fun n => (hall n).1) hZ hY hQ hB hD t ht hprob
  have hJm n ω : Measurable (J n ω) := by
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.indicator measurableSet_Ico
  have hJ n : ∀ᵐ ω ∂P, MemLp (J n ω) 2 (α ω) := by
    apply ae_of_all
    intro ω
    apply memLp_finsetSum
    intro i hi
    exact (memLp_const (G n i ω)).indicator measurableSet_Ico
  have hsp := signed_stieltjes_probability_continuity P α β ν hcs J H hJm hHm hJ hH hβ he
  have heq n : Q n t =ᵐ[P] (fun ω => signedIntegralRaw (ν ω) (J n ω)) := by
    filter_upwards [hQi n,hν n,hcs] with ω hq hνw hcsw
    letI : NullSingletonClass (ν ω).totalVariation := signed_cs_null_singletons (α ω) (β ω) (ν ω) hcsw
    rw [hq t ht,signed_integral_finite_steps]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x : ℝ => G n i ω*x) (hνw i).symm)
  have hq : TendstoInMeasure P (fun n => Q n t) atTop (D t) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using hqp
  have hs : TendstoInMeasure P (fun n ω => signedIntegralRaw (ν ω) (J n ω)) atTop
      (fun ω => signedIntegralRaw (ν ω) (H ω)) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using hsp
  exact tendstoInMeasure_ae_unique hq (hs.congr_left (fun n => (heq n).symm))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_covariance_from_elementary_limits
