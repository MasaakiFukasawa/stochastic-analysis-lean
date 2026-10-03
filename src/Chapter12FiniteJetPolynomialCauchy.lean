import Chapter12PolynomialControlledCauchy
import Chapter12LpSumNorm
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000

theorem finite_jet_polynomial_cauchy {Ω I E : Type*} [MeasurableSpace Ω] [Fintype I]
    [NormedAddCommGroup E]
    (V : I → Type*) [∀i,NormedAddCommGroup (V i)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [ENNReal.HolderTriple q q p]
    (d : ℕ) (hd : 0<d) [Fact (1≤q*d)]
    (u : ℕ → Lp E p P) (v : ℕ → PiLp 1 (fun i => Lp (V i) (q*d) P))
    (hv : CauchySeq v) (C : ℝ) (hC : 0≤C)
    (hb : ∀n m,∀ᵐw ∂P,‖(u n-u m) w‖≤
      C*(1+∑i,‖v n i w‖+∑i,‖v m i w‖)^d*∑i,‖(v n i-v m i) w‖) : CauchySeq u := by
  classical
  obtain ⟨B,hB⟩ := hv.isBounded_range.exists_norm_le
  have hB0 : 0≤B := (norm_nonneg (v 0)).trans (hB _ (mem_range_self 0))
  let one : Lp ℝ (q*d) P := (memLp_const (1:ℝ)).toLp (fun _ : Ω => (1:ℝ))
  have hone : (one : Ω → ℝ)=ᵐ[P] (fun _ => 1) := (memLp_const (1:ℝ)).coeFn_toLp
  have honen : ‖one‖≤1 := by
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (f:=one) zero_le_one
      (hone.mono (fun w hw => by rw [hw,norm_one]))
  let A := fun n m => one+lpSumNorm (fun i => v n i)+lpSumNorm (fun i => v m i)
  let D := fun n m => lpSumNorm (fun i => v n i-v m i)
  have hAn n m : ‖A n m‖≤1+B+B := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_add_le _ _).trans (add_le_add honen
        ((lpSumNorm_norm_le _).trans (hB _ (mem_range_self n))))
    · exact (lpSumNorm_norm_le _).trans (hB _ (mem_range_self m))
  have hDn n m : ‖D n m‖≤‖v n-v m‖ := lpSumNorm_norm_le _
  apply polynomial_controlled_cauchy P p q d hd u v hv A D C (1+B+B) hC (by linarith) hAn hDn
  intro n m
  filter_upwards [hb n m,hone,lpSumNorm_coe (fun i => v n i),lpSumNorm_coe (fun i => v m i),
    lpSumNorm_coe (fun i => v n i-v m i),
    Lp.coeFn_add one (lpSumNorm (fun i => v n i)),
    Lp.coeFn_add (one+lpSumNorm (fun i => v n i)) (lpSumNorm (fun i => v m i))] with w hw ho hn hm hD ha hb
  dsimp only [A,D]
  rw [hb,Pi.add_apply,ha,Pi.add_apply,ho,hn,hm,hD,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  exact hw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_jet_polynomial_cauchy
