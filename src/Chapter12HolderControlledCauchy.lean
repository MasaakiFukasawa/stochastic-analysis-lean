import Chapter12DerivativeCauchyCriterion
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem holder_controlled_cauchy {Ω E G : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup G]
    (P : Measure Ω) (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [ENNReal.HolderTriple q q p]
    (u : ℕ → Lp E p P) (v : ℕ → G) (hv : CauchySeq v)
    (R D : ℕ → ℕ → Lp ℝ q P) (M : ℝ) (hM : 0≤M)
    (hR : ∀n m,‖R n m‖≤M) (hD : ∀n m,‖D n m‖≤‖v n-v m‖)
    (hb : ∀n m,∀ᵐw ∂P,‖(u n-u m) w‖≤‖R n m w‖*‖D n m w‖) : CauchySeq u := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  apply derivative_cauchy_criterion u v hv (fun _ => 0) tendsto_const_nhds
    (‖B‖*M) (mul_nonneg (norm_nonneg B) hM)
  intro n m
  simp only [add_zero]
  have hcmp : ‖u n-u m‖≤‖B.holder p (R n m) (D n m)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hb n m,B.coeFn_holder (r:=p) (R n m) (D n m)] with w hw hc
    rw [hc]
    change ‖(u n-u m) w‖≤‖R n m w*D n m w‖
    simpa only [norm_mul] using hw
  apply hcmp.trans
  apply (B.norm_holder_apply_apply_le (R n m) (D n m)).trans
  calc
    _ ≤ (‖B‖*M)*‖v n-v m‖ := mul_le_mul
      (mul_le_mul_of_nonneg_left (hR n m) (norm_nonneg B)) (hD n m)
      (norm_nonneg (D n m)) (mul_nonneg (norm_nonneg B) hM)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.holder_controlled_cauchy
