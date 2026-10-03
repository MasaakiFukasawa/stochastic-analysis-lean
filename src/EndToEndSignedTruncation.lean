import Chapter2SignedDifferenceIntegral
import Chapter2TruncationLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false

/-- The appendix's truncation formula remains valid when the untruncated
 function is integrable only for total variation, not for a chosen positive
 decomposition. Thus no undefined difference of infinite integrals is used. -/
theorem signed_decomposition_truncation {Ω : Type*} [MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (f : Ω → ℝ) (hf : Measurable f)
    (hi : Integrable f (α.toSignedMeasure-β.toSignedMeasure).totalVariation) :
    Tendsto (fun n : ℕ =>
      (∫ x, max (-(n:ℝ)) (min (f x) n) ∂α)-
      (∫ x, max (-(n:ℝ)) (min (f x) n) ∂β))
      atTop (𝓝 (signedIntegralRaw (α.toSignedMeasure-β.toSignedMeasure) f)) := by
  let ν := α.toSignedMeasure-β.toSignedMeasure
  let g := fun n : ℕ => fun x => max (-(n:ℝ)) (min (f x) n)
  have hm n : Measurable (g n) := measurable_const.max (hf.min measurable_const)
  have hg n x : |g n x| ≤ (n:ℝ) := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α:=ℝ) n]) (min_le_right _ _)⟩
  have hgf n x : |g n x| ≤ |f x| := by
    apply abs_le.mpr
    constructor
    · apply le_trans _ (le_max_right _ _)
      exact le_min (neg_abs_le _) (by linarith [Nat.cast_nonneg (α:=ℝ) n,abs_nonneg (f x)])
    · exact max_le (by linarith [Nat.cast_nonneg (α:=ℝ) n,abs_nonneg (f x)]) ((min_le_left _ _).trans (le_abs_self _))
  have hlim x : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    obtain ⟨N,hN⟩ := exists_nat_ge |f x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb := abs_le.mp (hN.trans (show (N:ℝ) ≤ n by exact_mod_cast hn))
    simp only [g,min_eq_left hb.2,max_eq_right hb.1]
  have hconv (μ : Measure Ω) (hμ : μ ≤ ν.totalVariation) :
      Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 (∫ x,f x ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hm n).aestronglyMeasurable) (hi.mono_measure hμ).abs
      (fun n => .of_forall (fun x => by simpa only [Real.norm_eq_abs] using hgf n x))
      (.of_forall hlim)
  have he n : (∫ x,g n x ∂α)-(∫ x,g n x ∂β) = signedIntegralRaw ν (g n) := by
    exact (signed_difference_integral α β (g n)
      (Integrable.of_bound (hm n).aestronglyMeasurable n
        (.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hg n x)))).symm
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := fun _ => le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := fun _ => le_add_left le_rfl
  change Tendsto (fun n => (∫ x,g n x ∂α)-(∫ x,g n x ∂β)) atTop (𝓝 (signedIntegralRaw ν f))
  simp_rw [he]
  exact (hconv _ hp).sub (hconv _ hn)

#print axioms signed_decomposition_truncation
end Asakura.EndToEnd
