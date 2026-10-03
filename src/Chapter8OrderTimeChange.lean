import Chapter8MartingaleCLTVaryingWritten

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)

theorem order_time_change_M2 (a : ClosedTime T ≃o ClosedTime T) (ha : Continuous a)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) :
    ContinuousM2Witness P (fun t => F (a t)) (fun t => X (a t)) := by
  refine ⟨fun t => hX.adapted _,fun t => hX.moment _,fun ω => (hX.path ω).comp ha,?_,?_⟩
  · intro s t hst
    exact hX.martingale _ _ (a.monotone hst)
  · simpa only [a.map_bot] using hX.initial

theorem order_time_change_local (a : ClosedTime T ≃o ClosedTime T) (ha : Continuous a)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    LocalMProcessWitness P (fun t => F (a t)) (fun t => X (a t)) := by
  obtain ⟨ρ,hρ,hmono,hfinite,hco,hbound⟩ := hX.localizers
  refine ⟨fun n ω => a.symm (ρ n ω),?_,?_,?_,?_,?_⟩
  · intro n t
    have he : {ω | a.symm (ρ n ω) ≤ t} = {ω | ρ n ω ≤ a t} := by
      ext ω; exact a.symm_apply_le
    rw [he]; exact hρ n (a t)
  · intro ω n k hnk
    exact a.symm.monotone (hmono ω hnk)
  · intro n ω
    simpa only [a.symm.map_top] using a.symm.strictMono (hfinite n ω)
  · intro ω t ht
    have hat : a t < ⊤ := by simpa only [a.map_top] using a.strictMono ht
    obtain ⟨n,hn⟩ := hco ω (a t) hat
    refine ⟨n,?_⟩
    simpa only [a.symm_apply_apply] using a.symm.strictMono hn
  · intro n
    have he (t) (ω) : a (min (a.symm (ρ n ω)) t) = min (ρ n ω) (a t) := by
      rw [a.monotone.map_min,a.apply_symm_apply]
    have hh := order_time_change_M2 P F a ha (fun t ω => X (min (ρ n ω) t) ω) (hbound n).1
    refine ⟨?_,?_⟩
    · simpa only [he] using hh
    · intro t
      simpa only [he] using (hbound n).2 (a t)

theorem order_time_change_variation (a : ClosedTime T ≃o ClosedTime T)
    (C : ClosedTime T → Ω → ℝ) (hC : LocalVariationWitness F C) :
    LocalVariationWitness (fun t => F (a t)) (fun t => C (a t)) := by
  obtain ⟨ρ,hρ,hmono,hfinite,hco,hvar⟩ := hC.localizers
  refine ⟨fun n ω => a.symm (ρ n ω),?_,?_,?_,?_,?_⟩
  · intro n t
    have he : {ω | a.symm (ρ n ω) ≤ t} = {ω | ρ n ω ≤ a t} := by
      ext ω; exact a.symm_apply_le
    rw [he]; exact hρ n (a t)
  · intro ω n k hnk
    exact a.symm.monotone (hmono ω hnk)
  · intro n ω
    simpa only [a.symm.map_top] using a.symm.strictMono (hfinite n ω)
  · intro ω t ht
    have hat : a t < ⊤ := by simpa only [a.map_top] using a.strictMono ht
    obtain ⟨n,hn⟩ := hco ω (a t) hat
    refine ⟨n,?_⟩
    simpa only [a.symm_apply_apply] using a.symm.strictMono hn
  · intro n ω
    obtain ⟨U,V,hU,hV,he⟩ := hvar n ω
    refine ⟨U ∘ a,V ∘ a,hU.comp a.monotone,hV.comp a.monotone,?_⟩
    intro t
    rw [a.monotone.map_min,a.apply_symm_apply]
    exact he (a t)

theorem order_time_change_covariance (a : ClosedTime T ≃o ClosedTime T) (ha : Continuous a)
    (X Y C : ClosedTime T → Ω → ℝ) (hC : LocalCovarianceWitness P F X Y C) :
    LocalCovarianceWitness P (fun t => F (a t)) (fun t => X (a t)) (fun t => Y (a t))
      (fun t => C (a t)) :=
  ⟨order_time_change_local P F a ha _ hC.defect,order_time_change_variation F a C hC.variation⟩

end Asakura.Chapter8
