import FullAuditCovarianceBasics
import FullAuditCovarianceSymmetry

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem monotone_difference_add {ι : Type*} [Preorder ι] (f g : ι → ℝ)
    (hf : ∃ A B, Monotone A ∧ Monotone B ∧ ∀ t, f t = A t-B t)
    (hg : ∃ A B, Monotone A ∧ Monotone B ∧ ∀ t, g t = A t-B t) :
    ∃ A B, Monotone A ∧ Monotone B ∧ ∀ t, f t+g t = A t-B t := by
  obtain ⟨A,B,hA,hB,he⟩ := hf
  obtain ⟨C,D,hC,hD,he2⟩ := hg
  refine ⟨A+C,B+D,hA.add hC,hB.add hD,?_⟩
  intro t
  rw [he t,he2 t]
  change A t-B t+(C t-D t) = (A t+C t)-(B t+D t)
  ring

theorem monotone_difference_smul {ι : Type*} [Preorder ι] (f : ι → ℝ)
    (hf : ∃ A B, Monotone A ∧ Monotone B ∧ ∀ t, f t = A t-B t) (c : ℝ) :
    ∃ A B, Monotone A ∧ Monotone B ∧ ∀ t, c*f t = A t-B t := by
  obtain ⟨A,B,hA,hB,he⟩ := hf
  by_cases hc : 0 ≤ c
  · refine ⟨fun t => c*A t,fun t => c*B t,?_,?_,?_⟩
    · exact fun s t hst => mul_le_mul_of_nonneg_left (hA hst) hc
    · exact fun s t hst => mul_le_mul_of_nonneg_left (hB hst) hc
    · intro t; rw [he t]; ring
  · refine ⟨fun t => (-c)*B t,fun t => (-c)*A t,?_,?_,?_⟩
    · exact fun s t hst => mul_le_mul_of_nonneg_left (hB hst) (neg_nonneg.mpr (le_of_not_ge hc))
    · exact fun s t hst => mul_le_mul_of_nonneg_left (hA hst) (neg_nonneg.mpr (le_of_not_ge hc))
    · intro t; rw [he t]; ring

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)

theorem bounded_cov_bilinear (X Y Z : boundedMProcess P F) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, boundedCov P F hF hle hnull (c • X+Y) Z t ω =
      c*boundedCov P F hF hle hnull X Z t ω+boundedCov P F hF hle hnull Y Z t ω := by
  let C := boundedCov P F hF hle hnull
  have hXZ := bounded_cov_product_witness P F hF hle hnull X Z
  have hYZ := bounded_cov_product_witness P F hF hle hnull Y Z
  have hM := (hXZ.smul P F c).add P F hYZ
  have he : (fun t => c • (fun ω => X.val t ω*Z.val t ω-C X Z t ω)+
      (fun ω => Y.val t ω*Z.val t ω-C Y Z t ω)) =
      (fun t ω => (c • X+Y).val t ω*Z.val t ω-(c*C X Z t ω+C Y Z t ω)) := by
    funext t ω
    simp only [Submodule.coe_add,Submodule.coe_smul,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [he] at hM
  have hA (ω) := monotone_difference_add (fun t => c*C X Z t ω) (fun t => C Y Z t ω)
    (monotone_difference_smul _ (bounded_cov_in_A P F hF hle hnull X Z ω) c)
    (bounded_cov_in_A P F hF hle hnull Y Z ω)
  have h := bounded_cov_unique P F hF hle hnull (c • X+Y) Z _ hA hM
  exact h.mono fun ω hω t => (hω t).symm

theorem bounded_cov_mean (X Y : boundedMProcess P F) :
    (∫ ω, X.val ⊤ ω*Y.val ⊤ ω ∂P) = ∫ ω, boundedCov P F hF hle hnull X Y ⊤ ω ∂P := by
  let C := boundedCov P F hF hle hnull X Y
  have h := bounded_cov_product_witness P F hF hle hnull X Y
  have hiXY : Integrable (fun ω => X.val ⊤ ω*Y.val ⊤ ω) P :=
    (X.property.1.moment ⊤).integrable_mul (Y.property.1.moment ⊤)
  have hiD := (h.moment ⊤).integrable (by norm_num)
  have hiC : Integrable (C ⊤) P := by
    convert hiXY.sub hiD using 1
    funext ω
    simp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have he := integral_congr_ae ((h.martingale ⊥ ⊤ le_top).trans h.initial)
  rw [integral_condExp (hle ⊥)] at he
  simp only [Pi.zero_apply,integral_zero] at he
  change (∫ ω, X.val ⊤ ω*Y.val ⊤ ω-C ⊤ ω ∂P) = 0 at he
  rw [integral_sub hiXY hiC] at he
  exact sub_eq_zero.mp he

end Asakura.FullAudit
