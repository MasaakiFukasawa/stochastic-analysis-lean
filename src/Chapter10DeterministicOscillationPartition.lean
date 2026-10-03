import Chapter4BrownianSystem
import Chapter3OscillationPartition
import Chapter3StoppedMartingaleFromLp

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Continuous deterministic coefficients admit deterministic partitions
satisfying the already-proved semimartingale integral approximation theorem. -/
theorem deterministic_oscillation_partitions
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t) :
    ∃ τ : ℕ → ℕ → HalfClosedTime,
      (∀ n,τ n 0=⊥) ∧ (∀ n,Monotone (τ n)) ∧ (∀ n j,τ n j<⊤) ∧
      (∀ n t,t<⊤ → ∃ j,t<τ n j) ∧
      ∀ n j t,‖H (min (τ n (j+1)) t)-H (min (τ n j) t)‖≤(1/2:ℝ)^n := by
  letI : MeasurableSpace Unit := ⊤
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion (T := (⊤:EReal)) (by simp)
  let F := fun _ : HalfClosedTime => (⊤ : MeasurableSpace Unit)
  let X := fun t (_ : Unit) => H t
  let u := fun j => realTimeClamp (T := (⊤:EReal)) (c j)
  have hum : Monotone u := fun i j hij => real_time_clamp_mono (hcm.monotone hij)
  have hut j : u j<⊤ := real_time_below (c j) (hc j).le (hcT j)
  have huc t (ht : t<⊤) : ∃ j,t<u j := hcc t ht
  let τ := fun n j => oscillationPartition X u ((1/2:ℝ)^n) j ()
  have hp n := constructed_oscillation_partition F (fun _ _ _ => le_rfl) X
    (fun _ _ => measurable_const) (fun _ t ht => hH t ht) u hum hut huc
    ((1/2:ℝ)^n) (pow_pos (by norm_num) n)
  refine ⟨τ,fun n => (hp n).1 (),fun n => (hp n).2.2.1 (),
    fun n j => (hp n).2.2.2.1 j (),fun n t ht => (hp n).2.2.2.2.1 () t ht,?_⟩
  intro n j t
  exact (hp n).2.2.2.2.2 j () t

end Asakura.Chapter10
