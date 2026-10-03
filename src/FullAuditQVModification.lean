import FullAuditQVExistAE
import FullAuditBVMartingaleWritten

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Modification on the common ambient null set preserves adaptedness by
 augmentation, and makes every path of the constructed variation increasing. -/
theorem qv_monotone_modification {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (hY : ContinuousM2Witness P F Y)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t => X t ω^2-Y t ω)) :
    ∃ A : ClosedTime T → Ω → ℝ, (∀ t, Measurable[F t] (A t)) ∧ (∀ ω, Continuous (fun t => A t ω)) ∧
      (∀ ω, Monotone (fun t => A t ω)) ∧
      ContinuousM2Witness P F (fun t ω => X t ω^2-A t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, X t ω^2-A t ω = Y t ω) := by
  classical
  let N := toMeasurable P {ω | ¬ Monotone (fun t => X t ω^2-Y t ω)}
  have hNm : MeasurableSet[m] N := measurableSet_toMeasurable _ _
  have hNz : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.mp hmono
  have hNF (t) := hnull t N hNm hNz
  let A := fun t ω => if ω ∈ N then 0 else X t ω^2-Y t ω
  have hAm (t) : Measurable[F t] (A t) :=
    Measurable.ite (hNF t) measurable_const (((hm t).pow_const 2).sub (hY.adapted t))
  have hAc (ω) : Continuous (fun t => A t ω) := by
    by_cases hω : ω ∈ N
    · simpa only [A,if_pos hω] using (continuous_const : Continuous (fun _ : ClosedTime T => (0:ℝ)))
    · simp only [A,if_neg hω]
      exact ((hc ω).pow 2).sub (hY.path ω)
  have hAo (ω) : Monotone (fun t => A t ω) := by
    by_cases hω : ω ∈ N
    · simp only [A,if_pos hω]; exact monotone_const
    · have h : Monotone (fun t => X t ω^2-Y t ω) := by
        by_contra hn
        exact hω (subset_toMeasurable P _ hn)
      simpa only [A,if_neg hω] using h
  have hAE : ∀ᵐ ω ∂P, ∀ t, X t ω^2-A t ω = Y t ω := by
    have hnon : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]
      simpa only [not_not,Set.setOf_mem_eq] using hNz
    filter_upwards [hnon] with ω hω
    intro t
    simp [A,hω]
  have he (t) : (fun ω => X t ω^2-A t ω) =ᵐ[P] Y t := hAE.mono fun ω h => h t
  refine ⟨A,hAm,hAc,hAo,?_,hAE⟩
  refine ⟨fun t => ((hm t).pow_const 2).sub (hAm t),
    fun t => (memLp_congr_ae (he t)).mpr (hY.moment t),
    fun ω => ((hc ω).pow 2).sub (hAc ω),?_,(he ⊥).trans hY.initial⟩
  intro s t hst
  exact (condExp_congr_ae (he t)).trans ((hY.martingale s t hst).trans (he s).symm)

/-- Uniqueness uses the checked A intersect M2 argument, rather than being
 supplied as a premise of quadratic variation. A and B need only be increasing;
 their continuity follows from the two continuous martingale defects. -/
theorem qv_uniqueness_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X A B : ClosedTime T → Ω → ℝ)
    (hA : ∀ ω, Monotone (fun t => A t ω)) (hB : ∀ ω, Monotone (fun t => B t ω))
    (hYA : ContinuousM2Witness P F (fun t ω => X t ω^2-A t ω))
    (hYB : ContinuousM2Witness P F (fun t ω => X t ω^2-B t ω)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = B t ω := by
  have hZ := hYB.add P F (hYA.smul P F (-1))
  have he : (fun t => (fun ω => X t ω^2-B t ω)+(-1:ℝ) • (fun ω => X t ω^2-A t ω)) =
      (fun t ω => A t ω-B t ω) := by
    funext t ω
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he] at hZ
  have hz := continuous_bv_martingale_zero_written P F hF hle _ hZ.adapted hZ.moment hZ.path
    (fun ω => increasing_difference_boundedVariation _ _ (hA ω) (hB ω)) hZ.martingale hZ.initial
  filter_upwards [hz] with ω hω
  intro t
  exact sub_eq_zero.mp (hω t)

end Asakura.FullAudit
