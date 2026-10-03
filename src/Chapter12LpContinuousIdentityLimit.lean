import Chapter12FiberwiseClosedGraph

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12

theorem lp_continuous_identity_limit {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)]
    (b : E → F) (hb : Continuous b)
    (u : ℕ → Lp E p P) (v : ℕ → Lp F q P) (U : Lp E p P) (V : Lp F q P)
    (hu : Tendsto u atTop (𝓝 U)) (hv : Tendsto v atTop (𝓝 V))
    (he : ∀n,∀ᵐw ∂P,v n w=b (u n w)) : ∀ᵐw ∂P,V w=b (U w) := by
  obtain ⟨ns,hns,hun⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  obtain ⟨ms,hms,hvn⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hv.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hun,hvn,ae_all_iff.mpr he] with w hw hvw hew
  have ht := hb.continuousAt.tendsto.comp (hw.comp hms.tendsto_atTop)
  have heq : (fun k => v (ns (ms k)) w)=fun k => b (u (ns (ms k)) w) := funext (fun k => hew _)
  simp only [Function.comp_apply] at hvw
  rw [heq] at hvw
  exact tendsto_nhds_unique hvw ht
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lp_continuous_identity_limit
