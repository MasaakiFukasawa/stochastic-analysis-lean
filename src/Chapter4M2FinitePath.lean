import Chapter4FinitePathNorm
import FullAuditMartingaleHilbert

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma continuous_m2_finset_sum
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    {ι : Type*} (s : Finset ι) (X : ι → ClosedTime T → Ω → ℝ)
    (hX : ∀ i∈s,ContinuousM2Witness P F (X i)) :
    ContinuousM2Witness P F (fun t w => ∑ i∈s,X i t w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert ContinuousM2Witness.zero P F using 1
    funext t w
    simp only [Finset.sum_empty,Pi.zero_apply]
  | @insert i s hi ih =>
    convert (hX i (Finset.mem_insert_self _ _)).add P F
      (ih (fun j hj => hX j (Finset.mem_insert_of_mem hj))) using 1
    funext t w
    simp only [Finset.sum_insert hi,Pi.add_apply]

lemma m2_finite_path_memLp
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (Z : ClosedTime T → Ω → ℝ) (hZ : ContinuousM2Witness P F Z)
    (R : ℝ) (hRT : (R:EReal)<T)
    (hc : ∀ w,Continuous (fun t => Z (min (realTimeClamp R) t) w)) :
    MemLp (finiteRealPath Z R hc) 2 P := by
  have hp := continuous_martingale_path_memLp P F hF hle Z hZ.adapted hZ.moment hZ.path hZ.martingale
  apply hp.of_le_mul (c:=1)
    (finite_real_path_measurable F hle Z R hRT hc (fun t _ => hZ.adapted t)).aestronglyMeasurable
  exact ae_of_all _ fun w => by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro r
    exact (continuousPath Z hZ.path w).norm_coe_le_norm (realTimeClamp r.val)

lemma scalar_random_path_memLp {Ω D : Type*} [MeasurableSpace Ω]
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) (G : Ω → ℝ) (hG : MemLp G 2 P) (f : C(D,ℝ)) :
    MemLp (fun w => G w • f) 2 P := by
  apply hG.of_le_mul (c:=‖f‖) (hG.aestronglyMeasurable.smul aestronglyMeasurable_const)
  exact ae_of_all _ fun w => by
    change ‖G w • f‖≤‖f‖*‖G w‖
    rw [norm_smul,mul_comm]

end Asakura.Chapter4
