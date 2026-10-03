import Chapter4FeynmanKacLimits

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Bounded convergence supplies the terminal-time conditional identity
from identities strictly before the endpoint. -/
theorem bounded_conditional_terminal_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G≤m)
    (Z : ℝ → Ω → ℝ) (V : Ω → ℝ) (s R K : ℝ) (hsR : s<R)
    (hZm : ∀ r∈Icc s R,AEStronglyMeasurable[m] (Z r) P)
    (hZc : ∀ w,ContinuousOn (fun r => Z r w) (Icc s R))
    (hZb : ∀ r∈Icc s R,∀ w,|Z r w|≤K)
    (hV : StronglyMeasurable[G] V) (hVi : Integrable V P)
    (he : ∀ r∈Ico s R,P[Z r | G]=ᵐ[P] V) : P[Z R | G]=ᵐ[P] V := by
  let b := fun n : ℕ => R-(R-s)/((n:ℝ)+1)
  have hb n : b n∈Ico s R := by
    have hd0 : 0<(n:ℝ)+1 := by positivity
    have hd1 : 1≤(n:ℝ)+1 := by have h := Nat.cast_nonneg (α := ℝ) n;linarith
    have hf := div_le_self (sub_nonneg.mpr hsR.le) hd1
    exact ⟨by dsimp only [b];linarith,sub_lt_self R (div_pos (sub_pos.mpr hsR) hd0)⟩
  have hbc n : b n∈Icc s R := ⟨(hb n).1,(hb n).2.le⟩
  have hbR : Tendsto b atTop (𝓝 R) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R-s)
    convert (tendsto_const_nhds (x := R)).sub hh using 1 <;> simp [b,div_eq_mul_inv]
  apply conditional_limit_from_stopped_tests P G hG (fun n => Z (b n)) (Z R) V (fun _ => K)
    (fun n => hZm _ (hbc n)) (hZm R ⟨hsR.le,le_rfl⟩) hV hVi (integrable_const K)
    (fun n => ae_of_all _ fun w => hZb _ (hbc n) w)
  · apply ae_of_all
    intro w
    exact (hZc w R ⟨hsR.le,le_rfl⟩).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hbR,Eventually.of_forall hbc⟩)
  · intro n A hA
    have hi : Integrable (Z (b n)) P := Integrable.of_bound (hZm _ (hbc n)) K
      (ae_of_all _ fun w => hZb _ (hbc n) w)
    exact (setIntegral_condExp hG hi hA).symm.trans
      (setIntegral_congr_ae (hG A hA) ((he _ (hb n)).mono fun w hw _ => hw))

end Asakura.Chapter4
