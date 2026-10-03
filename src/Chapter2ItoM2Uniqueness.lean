import Chapter2ItoTerminalCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Covariance uniqueness includes the terminal value once that value has
been constructed by continuous extension. -/
theorem ito_m2_covariance_unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : ContinuousM2Witness P F Y)
    (hZ : ContinuousM2Witness P F Z)
    (hy : ItoCovarianceFormula P F X H Y) (hz : ItoCovarianceFormula P F X H Z) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω = Z t ω := by
  obtain ⟨u,hu,hm,ht⟩ := exists_seq_strictMono_tendsto' (show (⊥ : ClosedTime T) < ⊤ from hT)
  have hc : ∀ t, t < ⊤ → ∃ n, t < u n :=
    fun t ht' => (ht.eventually (lt_mem_nhds ht')).exists
  have hYL := continuous_m2_is_local P F hF hle u hu.monotone (fun n => (hm n).2) hc Y hY
  have hZL := continuous_m2_is_local P F hF hle u hu.monotone (fun n => (hm n).2) hc Z hZ
  have he := hy.unique P hT F hF hle hnull X Y Z H hX hYL hZL hz
  filter_upwards [he] with ω hω
  intro t
  by_cases ht' : t < ⊤
  · exact hω t ht'
  · have htop : t = ⊤ := eq_top_iff.mpr (le_of_not_gt ht')
    rw [htop]
    have hyT := ((hY.path ω).continuousAt.tendsto (x := ⊤)).comp ht
    have hzT := ((hZ.path ω).continuousAt.tendsto (x := ⊤)).comp ht
    exact tendsto_nhds_unique (hyT.congr (fun n => hω (u n) (hm n).2)) hzT

/-- Linearity is an equality of the actual closed-interval M2 processes,
including the terminal value obtained by the L2 limit. -/
theorem ito_m2_covariance_linearity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y Z W : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ) (a : ℝ)
    (hX : LocalMProcessWitness P F X) (hY : ContinuousM2Witness P F Y)
    (hZ : ContinuousM2Witness P F Z) (hW : ContinuousM2Witness P F W)
    (hy : ItoCovarianceFormula P F X H Y) (hz : ItoCovarianceFormula P F X G Z)
    (hw : ItoCovarianceFormula P F X (fun z => a*H z+G z) W) :
    ∀ᵐ ω ∂P, ∀ t, W t ω = a*Y t ω+Z t ω := by
  have hcomb := (hY.smul P F a).add P F hZ
  exact ito_m2_covariance_unique P hT F hF hle hnull X W (fun t ω => a*Y t ω+Z t ω)
    (fun z => a*H z+G z) hX hW hcomb hw (hy.add_smul P F hF hle X Y Z H G hz a)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_m2_covariance_unique
#print axioms Asakura.Chapter2Complete.ito_m2_covariance_linearity
