import EndToEndLocalItoCoordinates
import EndToEndPathReconstruction

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter13
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The local Ito family admits a jointly measurable continuous-path
realization. Only the original coefficient measurability is assumed. -/
theorem local_ito_joint_paths {Ω E : Type} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (i : Fin d)
    (μ : Measure E) [IsFiniteMeasure μ]
    (H : E × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ w b,0≤b → ∃ K : ℝ,0≤K ∧ ∀ x r,r∈Icc 0 b → |H (x,(w,r))|≤K)
    (N : E → HalfClosedTime → Ω → ℝ) (hN : ∀ x,LocalMProcessWitness P B.F (N x))
    (hNI : ∀ x,ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (N x)) :
    ∃ R : E × Ω → C(ℝ,ℝ), Measurable R ∧
      ∀ᵐ x ∂μ, ∀ᵐ w ∂P, ∀ r, R (x,w) r=N x (realTimeClamp r) w := by
  classical
  letI := real_continuous_path_polish
  let q := denseSeq ℝ
  have hex n := local_ito_joint_coordinate P B i μ H hm hp hb N hN hNI
    (max (q n) 0) (le_max_right _ _)
  choose G hGm hGe using hex
  have hclamp r : realTimeClamp (T:=(⊤:EReal)) (max r 0)=realTimeClamp r := by
    by_cases hr : 0≤r
    · rw [max_eq_left hr]
    · have hre : (r:EReal)≤0 := by exact_mod_cast le_of_not_ge hr
      rw [max_eq_right (le_of_not_ge hr)]
      apply Subtype.ext
      simp [realTimeClamp,Set.coe_projIcc,max_eq_left hre]
  simp only [hclamp] at hGe
  let Bad := {x | ¬ ∀ n, ∀ᵐ w ∂P, G n (x,w)=N x (realTimeClamp (q n)) w}
  have hBad : μ Bad=0 := ae_iff.mp (ae_all_iff.mpr hGe)
  let S := (toMeasurable μ Bad)ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable μ Bad).compl
  have hS : ∀ᵐ x ∂μ, x∈S := by
    rw [ae_iff]
    simpa only [S,mem_compl_iff,not_not,Set.ofPred_mem_eq] using (measure_toMeasurable (μ:=μ) Bad).trans hBad
  have hgood x (hx : x∈S) : ∀ n, ∀ᵐ w ∂P, G n (x,w)=N x (realTimeClamp (q n)) w := by
    by_contra hn
    exact hx (subset_toMeasurable μ Bad hn)
  let X := fun x r w => if x∈S then N x (realTimeClamp r) w else 0
  have hc x w : Continuous (fun r => X x r w) := by
    by_cases hx : x∈S
    · simp only [X,if_pos hx]
      apply continuous_iff_continuousAt.mpr
      intro r
      have ht : realTimeClamp (T:=(⊤:EReal)) r<⊤ :=
        (real_time_clamp_mono (le_max_left r 0)).trans_lt
          (real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _))
      exact ((hN x).path P B.F w _ ht).comp real_time_clamp_continuous.continuousAt
    · simp only [X,if_neg hx]
      exact continuous_const
  let G' := fun n (z : E × Ω) => if z.1∈S then G n z else 0
  have hm' n : Measurable (G' n) := Measurable.ite (hSm.preimage measurable_fst) (hGm n) measurable_const
  have he x : ∀ᵐ w ∂P, ∀ n, G' n (x,w)=X x (q n) w := by
    by_cases hx : x∈S
    · simpa only [G',X,if_pos hx] using ae_all_iff.mpr (hgood x hx)
    · exact Filter.Eventually.of_forall (fun w n => by simp only [G',X,if_neg hx])
  obtain ⟨R,hRm,hRe⟩ := path_from_countable_coordinates q (denseRange_denseSeq ℝ) P X hc G' hm' he
  refine ⟨R,hRm,?_⟩
  filter_upwards [hS] with x hx
  simpa only [X,if_pos hx] using hRe x

#print axioms local_ito_joint_paths
end Asakura.EndToEnd
