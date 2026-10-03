import Chapter12FiniteJetPolynomialCauchy

open MeasureTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem paired_jet_polynomial_cauchy {Ω I J E:Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    [NormedAddCommGroup E]
    (V:I → Type u) (W:J → Type u) [∀i,NormedAddCommGroup (V i)] [∀j,NormedAddCommGroup (W j)]
    (P:Measure Ω) [IsProbabilityMeasure P]
    (p q:ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [ENNReal.HolderTriple q q p]
    (d:ℕ) (hd:0<d) [Fact (1≤q*d)]
    (u:ℕ → Lp E p P)
    (v:ℕ → PiLp 1 (fun i => Lp (V i) (q*d) P)) (vlim:PiLp 1 (fun i => Lp (V i) (q*d) P))
    (w:ℕ → PiLp 1 (fun j => Lp (W j) (q*d) P)) (wlim:PiLp 1 (fun j => Lp (W j) (q*d) P))
    (hv:Tendsto v atTop (𝓝 vlim)) (hw:Tendsto w atTop (𝓝 wlim)) (C:ℝ) (hC:0≤C)
    (hb:∀n m,∀ᵐω ∂P,‖(u n-u m) ω‖≤
      C*(1+∑i,‖v n i ω‖+∑i,‖v m i ω‖+∑j,‖w n j ω‖+∑j,‖w m j ω‖)^d*
        ((∑i,‖(v n i-v m i) ω‖)+∑j,‖(w n j-w m j) ω‖)) : CauchySeq u := by
  let A:Sum I J → Type _ := Sum.elim V W
  letI : ∀i,NormedAddCommGroup (A i) := fun i => by cases i <;> dsimp [A] <;> infer_instance
  let z:ℕ → PiLp 1 (fun i => Lp (A i) (q*d) P) := fun n =>
    WithLp.toLp 1 (fun i => match i with | .inl i => v n i | .inr j => w n j)
  let zlim:PiLp 1 (fun i => Lp (A i) (q*d) P) :=
    WithLp.toLp 1 (fun i => match i with | .inl i => vlim i | .inr j => wlim j)
  have hz:Tendsto z atTop (𝓝 zlim) := by
    apply (PiLp.continuous_toLp 1 (fun i => Lp (A i) (q*d) P)).continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro i
    cases i with
    | inl i => exact (((continuous_apply i).comp (PiLp.continuous_ofLp 1 _)).tendsto _).comp hv
    | inr j => exact (((continuous_apply j).comp (PiLp.continuous_ofLp 1 _)).tendsto _).comp hw
  apply finite_jet_polynomial_cauchy A P p q d hd u z hz.cauchySeq C hC
  intro n m
  filter_upwards [hb n m] with ω hω
  change ‖(u n-u m) ω‖≤C*(1+(∑i:Sum I J,‖z n i ω‖)+(∑i:Sum I J,‖z m i ω‖))^d*
    (∑i:Sum I J,‖(z n i-z m i) ω‖)
  simp only [Fintype.sum_sum_type,z]
  convert hω using 1 <;> ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.paired_jet_polynomial_cauchy
