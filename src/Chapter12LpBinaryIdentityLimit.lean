import Chapter12LpContinuousIdentityLimit

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem lp_binary_identity_limit {Ω E F G:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (P:Measure Ω) (p q r:ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)]
    (b:E → F → G) (hb:Continuous (fun x:E×F => b x.1 x.2))
    (u:ℕ → Lp E p P) (v:ℕ → Lp F q P) (z:ℕ → Lp G r P)
    (U:Lp E p P) (V:Lp F q P) (Z:Lp G r P)
    (hu:Tendsto u atTop (𝓝 U)) (hv:Tendsto v atTop (𝓝 V)) (hz:Tendsto z atTop (𝓝 Z))
    (he:∀n,∀ᵐw ∂P,z n w=b (u n w) (v n w)) : ∀ᵐw ∂P,Z w=b (U w) (V w) := by
  obtain ⟨ns,hns,hun⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  obtain ⟨ms,hms,hvn⟩ := (tendstoInMeasure_of_tendsto_Lp (hv.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨ls,hls,hzn⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((hz.comp hns.tendsto_atTop).comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hun,hvn,hzn,ae_all_iff.mpr he] with w huw hvw hzw hew
  have ht := hb.continuousAt.tendsto.comp
    (((huw.comp hms.tendsto_atTop).comp hls.tendsto_atTop).prodMk_nhds (hvw.comp hls.tendsto_atTop))
  have heq : (fun k => z (ns (ms (ls k))) w)=fun k => b (u (ns (ms (ls k))) w) (v (ns (ms (ls k))) w) :=
    funext (fun k => hew _)
  simp only [Function.comp_apply] at hzw ht
  rw [heq] at hzw
  exact tendsto_nhds_unique hzw ht
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lp_binary_identity_limit
