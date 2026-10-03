import Chapter12HolderControlledCauchy
import Chapter12LpNormPowerMember
import Chapter12LpInclusion

open MeasureTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem probabilityLpInclusion_norm_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (f : Lp E q P) :
    ‖probabilityLpInclusion P p q hpq f‖≤‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae (probabilityLpInclusion_coe P p q hpq f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_le_eLpNorm_of_exponent_le hpq)

theorem polynomial_controlled_cauchy {Ω E G : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup G]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [ENNReal.HolderTriple q q p]
    (d : ℕ) (hd : 0<d) [Fact (1≤q*d)]
    (u : ℕ → Lp E p P) (v : ℕ → G) (hv : CauchySeq v)
    (A D : ℕ → ℕ → Lp ℝ (q*d) P) (C B : ℝ) (hC : 0≤C) (hB : 0≤B)
    (hA : ∀n m,‖A n m‖≤B) (hD : ∀n m,‖D n m‖≤‖v n-v m‖)
    (hb : ∀n m,∀ᵐw ∂P,‖(u n-u m) w‖≤C*‖A n m w‖^d*‖D n m w‖) :
    CauchySeq u := by
  have hqd : q≤q*d := by
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hd)
  let R := fun n m => C • lpNormPower d hd (A n m)
  let L := fun n m => probabilityLpInclusion P q (q*d) hqd (D n m)
  apply holder_controlled_cauchy P p q u v hv R L (C*B^d) (mul_nonneg hC (pow_nonneg hB d))
  · intro n m
    dsimp only [R]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,lpNormPower_norm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hA n m) d) hC
  · intro n m
    exact (probabilityLpInclusion_norm_le P q (q*d) hqd (D n m)).trans (hD n m)
  · intro n m
    filter_upwards [hb n m,Lp.coeFn_smul C (lpNormPower d hd (A n m)),
      lpNormPower_coe d hd (A n m),probabilityLpInclusion_coe P q (q*d) hqd (D n m)] with w hw hs hp hl
    dsimp only [R,L]
    rw [hs,Pi.smul_apply,smul_eq_mul,hp,hl,norm_mul,Real.norm_eq_abs,abs_of_nonneg hC,
      norm_pow,norm_norm]
    exact hw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.polynomial_controlled_cauchy
