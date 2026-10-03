import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- An actual infinite sequence of independent unit noises: discarding its
first coordinate preserves the law, and the first noise is independent of
the entire remaining past. -/
theorem iid_past_shift {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    let R := Measure.infinitePi (fun _ : ℕ => P)
    let S := fun w : ℕ → Ω => fun n => w (n+1)
    MeasurePreserving S R R ∧
      R.map (fun w => (w 0,S w))=P.prod R := by
  dsimp only
  let R := Measure.infinitePi (fun _ : ℕ => P)
  let S := fun w : ℕ → Ω => fun n => w (n+1)
  have hSm : Measurable S := by fun_prop
  have hS : R.map S=R :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => P) Nat.succ_injective
  refine ⟨⟨hSm,hS⟩,?_⟩
  let A := fun n : ℕ => MeasurableSpace.comap (fun w : ℕ → Ω => w n) m
  have hInd : iIndep A R := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => P) (X := fun _ w => w) (fun _ => measurable_id)
  have hA n : A n≤ (inferInstance : MeasurableSpace (ℕ → Ω)) := (measurable_pi_apply n).comap_le
  have hd : Disjoint ({0} : Set ℕ) (Set.range Nat.succ) := by
    simp
  have hh := indep_iSup_of_disjoint hA hInd hd
  have he : MeasurableSpace.comap S (inferInstance : MeasurableSpace (ℕ → Ω))=
      ⨆ n : ℕ,A (n+1) := by
    simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,MeasurableSpace.comap_comp]
    rfl
  have hi : IndepFun (fun w : ℕ → Ω => w 0) S R := by
    change Indep (A 0) (MeasurableSpace.comap S inferInstance) R
    rw [he]
    simpa only [iSup_singleton,iSup_range] using hh
  rw [hi.map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable hSm.aemeasurable,hS]
  rw [Measure.infinitePi_map_eval]

end Asakura.Chapter8
