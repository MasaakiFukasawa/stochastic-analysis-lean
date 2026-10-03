import Chapter10ConditionalCharacteristicLimit
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Brownian conditional increments up to every preterminal time extend to
maturity along the continuous order-flow path. -/
theorem brownian_terminal_characteristic {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : MeasurableSpace Ω) (hle : H≤m)
    (X : ℝ → Ω → ℝ) (s T u : ℝ) (hsT : s<T)
    (hX : ∀ t,Measurable[m] (X t))
    (hc : ∀ᵐ w ∂P,ContinuousOn (fun t => X t w) (Icc s T))
    (hchar : ∀ t∈Ico s T,
      P[(fun w => Complex.exp (((u*(X t w-X s w):ℝ):ℂ)*Complex.I))|H]=ᵐ[P]
        fun _ => Complex.exp ((-(t-s)*u^2/2:ℝ):ℂ)) :
    P[(fun w => Complex.exp (((u*(X T w-X s w):ℝ):ℂ)*Complex.I))|H]=ᵐ[P]
      fun _ => Complex.exp ((-(T-s)*u^2/2:ℝ):ℂ) := by
  letI : MeasurableSpace Ω := m
  let b := fun n : ℕ => T-(T-s)/((n:ℝ)+1)
  have hb n : b n∈Ico s T := by
    have hd0 : 0<(n:ℝ)+1 := by positivity
    have hd1 : 1≤(n:ℝ)+1 := by have h := Nat.cast_nonneg (α := ℝ) n;linarith
    have hf := div_le_self (sub_nonneg.mpr hsT.le) hd1
    exact ⟨by dsimp only [b];linarith,sub_lt_self T (div_pos (sub_pos.mpr hsT) hd0)⟩
  have hbT : Tendsto b atTop (𝓝 T) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T-s)
    convert (tendsto_const_nhds (x := T)).sub hh using 1 <;> simp [b,div_eq_mul_inv]
  have hbw : Tendsto b atTop (𝓝[Icc s T] T) := tendsto_nhdsWithin_iff.mpr
    ⟨hbT,Eventually.of_forall fun n => ⟨(hb n).1,(hb n).2.le⟩⟩
  apply conditional_gaussian_characteristic_limit P H hle
    (fun n w => X (b n) w-X s w) (fun w => X T w-X s w)
    (fun n => (hX _).sub (hX _)) ?_ (fun n => b n-s) (T-s) u
    (fun n => sub_nonneg.mpr (hb n).1) (hbT.sub_const s) (fun n => hchar _ (hb n))
  filter_upwards [hc] with w hw
  exact (((hw T ⟨hsT.le,le_rfl⟩).tendsto.comp hbw).sub_const (X s w))

end Asakura.Chapter10
