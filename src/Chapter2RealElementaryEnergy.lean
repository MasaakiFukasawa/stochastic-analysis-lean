import Chapter2ElementaryGridEnergy
import Chapter2ActualStieltjesEnergy
import FullAuditBoundedKW

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

theorem local_covariance_path_continuous
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C) (ω : Ω) (t : ClosedTime T) (ht : t < ⊤) :
    ContinuousAt (fun s => C s ω) t := by
  have h := ((hX.path P F ω t ht).mul (hY.path P F ω t ht)).sub (hC.defect.path P F ω t ht)
  convert h using 1
  funext s
  change C s ω = X s ω*Y s ω-(X s ω*Y s ω-C s ω)
  ring

/-- A real-time elementary strategy has the actual Stieltjes integral
of its square as quadratic variation, on every finite subinterval. -/
theorem real_elementary_grid_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T)
    (hAm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 b))
    (N : ℕ) (u : ℕ → ℝ) (hu : StrictMonoOn u (Iic N))
    (huab : ∀ i ≤ N, u i ∈ Icc 0 b)
    (G : ℕ → Ω → ℝ)
    (hGm : ∀ i < N, Measurable[F (realTimeClamp (u i))] (G i))
    (hG : ∀ i < N, MemLp (G i) ∞ P) :
    let Z := fun t ω => ∑ i ∈ Finset.range N, G i ω*
      stepIncrement (realTimeClamp (u i)) (realTimeClamp (u (i+1))) (fun t => X t ω) t
    LocalMProcessWitness P F Z ∧ ∃ Q, LocalCovarianceWitness P F Z Z Q ∧
      ∀ᵐ ω ∂P, ∀ t, t ∈ Icc 0 b →
        ∃ hr : ∀ r ∈ Icc 0 b, ContinuousWithinAt (fun s => A (realTimeClamp s) ω) (Icc 0 b ∩ Ici r) r,
        Q (realTimeClamp t) ω =
          ∫ r in Iic t, (∑ i ∈ Finset.range N, (Ico (u i) (u (i+1))).indicator (fun _ => G i ω) r)^2
            ∂(intervalStieltjes 0 b hb (fun s => A (realTimeClamp s) ω) (hAm ω) hr).measure := by
  intro Z
  have hrt (t : ℝ) (ht : t ∈ Icc 0 b) : realTimeClamp (T := T) t < ⊤ := by
    change (realTimeClamp t : EReal) < T
    rw [real_time_clamp_eq t ht.1 ((EReal.coe_le_coe ht.2).trans hbT.le)]
    exact (EReal.coe_le_coe ht.2).trans_lt hbT
  have hu' : StrictMonoOn (fun i => realTimeClamp (T := T) (u i)) (Iic N) := by
    intro i hi j hj hij
    change (realTimeClamp (u i) : EReal) < (realTimeClamp (u j) : EReal)
    rw [real_time_clamp_eq _ (huab i hi).1 ((EReal.coe_le_coe (huab i hi).2).trans hbT.le),
      real_time_clamp_eq _ (huab j hj).1 ((EReal.coe_le_coe (huab j hj).2).trans hbT.le)]
    exact_mod_cast hu hi hj hij
  obtain ⟨hZ,Q,hQ,hQi⟩ := elementary_grid_quadratic_variation P F hF hle hnull X A hX hA
    N (fun i => realTimeClamp (u i)) hu' G hGm hG
  refine ⟨hZ,Q,hQ,?_⟩
  filter_upwards [hQi] with ω hqi
  intro t ht
  have hc : ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 b) := by
    intro r hr
    exact ((local_covariance_path_continuous P F X X A hX hX hA ω _ (hrt r hr)).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  let hr := fun r (hr : r ∈ Icc 0 b) => (hc r hr).mono (inter_subset_left (t := Ici r))
  refine ⟨hr,?_⟩
  rw [hqi _ (hrt t ht),actual_stieltjes_grid_energy 0 b hb _ (hAm ω) hc N u hu huab (fun i => G i ω) t ht]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [stepIncrement]
  rw [← real_time_clamp_mono.map_min,← real_time_clamp_mono.map_min]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_path_continuous
#print axioms Asakura.Chapter2Complete.real_elementary_grid_energy
