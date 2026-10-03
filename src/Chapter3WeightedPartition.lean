import Chapter3WeightedStoppedM2
import Chapter3OrthogonalSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- If a continuous adapted process has finished evolving by σ, its terminal
value is Fσ measurable. This is the earlier-term measurability in prop:qcv. -/
theorem finished_process_terminal_measurable
    {Ω : Type*} {m : MeasurableSpace Ω}
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Z : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (Z t))
    (hc : ∀ ω, Continuous (fun t => Z t ω))
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (he : ∀ ω, Z (σ ω) ω = Z ⊤ ω) :
    Measurable[writtenStoppedSpace m F σ hσ] (Z ⊤) := by
  have h := stopped_value_measurable_right_continuous m (Fact.out : 0 ≤ T) F hF hle
    σ hσ Z hm (fun ω t => (hc ω).continuousAt.continuousWithinAt)
  simpa only [he] using h

/-- A finished earlier M2 term and a weighted later M2 term are orthogonal.
Their ordering and the later coefficient's measurability discharge the inputs
of the zero-conditional-mean lemma. -/
theorem successive_weighted_terms_orthogonal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Z Y : ClosedTime T → Ω → ℝ)
    (hZ : ContinuousM2Witness P F Z) (hY : ContinuousM2Witness P F Y)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hend : ∀ ω, Z (σ ω) ω = Z ⊤ ω)
    (hz : ∀ ω, Y (σ ω) ω = 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A)
    (hAb : MemLp A ∞ P) :
    (∫ ω, Z ⊤ ω*(A ω*Y ⊤ ω) ∂P) = 0 := by
  have hZm := finished_process_terminal_measurable F hF hle Z hZ.adapted hZ.path σ hσ hend
  have h := stopped_zero_martingale_orthogonal P F hF hle Y hY σ hσ
    (.of_forall hz) (fun ω => A ω*Z ⊤ ω) (hA.mul hZm) (hAb.mul (hZ.moment ⊤))
  convert h using 1
  congr 1
  funext ω
  ring

/-- The finite weighted partition energy equality, with orthogonality proved
from the time ordering, not assumed as an input. -/
theorem weighted_partition_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ℕ → ClosedTime T → Ω → ℝ) (hY : ∀ j, ContinuousM2Witness P F (Y j))
    (σ : ℕ → Ω → ClosedTime T)
    (hσ : ∀ j t, MeasurableSet[F t] {ω | σ j ω ≤ t})
    (hz : ∀ j ω t, t ≤ σ j ω → Y j t ω = 0)
    (hend : ∀ i j, i < j → ∀ ω, Y i (σ j ω) ω = Y i ⊤ ω)
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (σ j) (hσ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P) (N : ℕ) :
    (∫ ω, (∑ j ∈ Finset.range N, A j ω*Y j ⊤ ω)^2 ∂P) =
      ∑ j ∈ Finset.range N, ∫ ω, (A j ω*Y j ⊤ ω)^2 ∂P := by
  have hW (j) := bounded_stopped_weight_m2 P F hF hle (Y j) (hY j) (σ j) (hσ j)
    (hz j) (A j) (hA j) (hAb j)
  have ho (i j) (hij : i < j) :
      (∫ ω, (A i ω*Y i ⊤ ω)*(A j ω*Y j ⊤ ω) ∂P) = 0 :=
    successive_weighted_terms_orthogonal P F hF hle _ _ (hW i) (hY j) (σ j) (hσ j)
      (fun ω => by rw [hend i j hij ω])
      (fun ω => hz j ω _ le_rfl) (A j) (hA j) (hAb j)
  apply orthogonal_sum_energy P (Finset.range N) _ (fun j _ => (hW j).moment ⊤)
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ho i j h
  · simpa only [mul_comm] using ho j i h

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.finished_process_terminal_measurable
#print axioms Asakura.Chapter3Complete.successive_weighted_terms_orthogonal
#print axioms Asakura.Chapter3Complete.weighted_partition_energy
