import FullAuditBoundedProcess

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)

/-- Polarization of the constructed square compensators gives the printed
 product martingale, by the actual polynomial identity. -/
theorem bounded_cov_product_witness (X Y : boundedMProcess P F) :
    ContinuousM2Witness P F (fun t ω => X.val t ω*Y.val t ω-boundedCov P F hF hle hnull X Y t ω) := by
  let Q := boundedQV P F hF hle hnull
  have hp := (boundedQV_properties P F hF hle hnull (X+Y)).2.2.2
  have hn := (boundedQV_properties P F hF hle hnull (X-Y)).2.2.2
  have h := (hp.add P F (hn.smul P F (-1))).smul P F (1/4)
  have he : (fun t => (1/4:ℝ) • ((fun ω => (X+Y).val t ω^2-Q (X+Y) t ω) +
      (-1:ℝ) • (fun ω => (X-Y).val t ω^2-Q (X-Y) t ω))) =
      (fun t ω => X.val t ω*Y.val t ω-boundedCov P F hF hle hnull X Y t ω) := by
    funext t ω
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,Submodule.coe_add,Submodule.coe_sub,Pi.sub_apply,boundedCov,Q]
    ring
  rwa [he] at h

/-- Membership in A is checked from the two increasing terms of polarization. -/
theorem bounded_cov_in_A (X Y : boundedMProcess P F) (ω : Ω) :
    ∃ A B : ClosedTime T → ℝ, Monotone A ∧ Monotone B ∧
      ∀ t, boundedCov P F hF hle hnull X Y t ω = A t-B t := by
  let Q := boundedQV P F hF hle hnull
  refine ⟨fun t => Q (X+Y) t ω/4,fun t => Q (X-Y) t ω/4,?_,?_,?_⟩
  · intro s t hst
    exact div_le_div_of_nonneg_right ((boundedQV_properties P F hF hle hnull (X+Y)).2.2.1 ω hst) (by norm_num)
  · intro s t hst
    exact div_le_div_of_nonneg_right ((boundedQV_properties P F hF hle hnull (X-Y)).2.2.1 ω hst) (by norm_num)
  · intro t
    dsimp [boundedCov,Q]
    ring

/-- The uniqueness clause for product compensators is proved from A intersect
 M2={0}, and does not assume a covariance uniqueness rule. -/
theorem bounded_cov_unique (X Y : boundedMProcess P F)
    (A : ClosedTime T → Ω → ℝ)
    (hA : ∀ ω, ∃ B C : ClosedTime T → ℝ, Monotone B ∧ Monotone C ∧ ∀ t, A t ω = B t-C t)
    (hM : ContinuousM2Witness P F (fun t ω => X.val t ω*Y.val t ω-A t ω)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = boundedCov P F hF hle hnull X Y t ω := by
  let C := boundedCov P F hF hle hnull X Y
  have hC := bounded_cov_product_witness P F hF hle hnull X Y
  have h := hC.add P F (hM.smul P F (-1))
  have he : (fun t => (fun ω => X.val t ω*Y.val t ω-C t ω)+
      (-1:ℝ) • (fun ω => X.val t ω*Y.val t ω-A t ω)) = (fun t ω => A t ω-C t ω) := by
    funext t ω
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [he] at h
  have hdecomp (ω) : ∃ B D : ClosedTime T → ℝ, Monotone B ∧ Monotone D ∧
      ∀ t, A t ω-C t ω = B t-D t := by
    obtain ⟨Ap,An,hAp,hAn,heA⟩ := hA ω
    obtain ⟨Cp,Cn,hCp,hCn,heC⟩ := bounded_cov_in_A P F hF hle hnull X Y ω
    refine ⟨Ap+Cn,An+Cp,hAp.add hCn,hAn.add hCp,?_⟩
    intro t
    dsimp [C]
    rw [heA t,heC t]
    ring
  have hz := A_inter_M2_zero_written P F hF hle _ h.adapted h.moment h.path hdecomp h.martingale h.initial
  filter_upwards [hz] with ω hω
  intro t
  exact sub_eq_zero.mp (hω t)

end Asakura.FullAudit
