import Chapter8IIDPastShift
import Chapter8RandomL2FixedPoint

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Independent unit noises construct an invariant finite-second-moment
law of a contractive random map. The pullback random variable, its past
shift, and independence of the next noise are all constructed explicitly. -/
theorem contractive_random_map_invariant {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F))
    (hF0 : MemLp (F 0) 2 P) (ρ : ℝ≥0) (hρ : ρ<1)
    (hLip : ∀ w x y,‖F x w-F y w‖≤(ρ:ℝ)*‖x-y‖) :
    ∃ π : Measure E,IsProbabilityMeasure π ∧ MemLp (fun x : E => x) 2 π ∧
      (π.prod P).map (Function.uncurry F)=π := by
  let R := Measure.infinitePi (fun _ : ℕ => P)
  let S := fun w : ℕ → Ω => fun n => w (n+1)
  obtain ⟨hS,hST⟩ := iid_past_shift P
  change MeasurePreserving S R R at hS
  change R.map (fun w => (w 0,S w))=P.prod R at hST
  let F' := fun x (w : ℕ → Ω) => F x (w 0)
  have hF' : Measurable (Function.uncurry F') :=
    hF.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hF'0 : MemLp (F' 0) 2 R :=
    hF0.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ : ℕ => P) 0)
  obtain ⟨T,Y,hTe,hTL,hy,hlim,hbound,hfix⟩ := random_L2_fixed_point R S hS F' hF' hF'0 ρ hρ
    (fun w x y => hLip (w 0) x y)
  let y := (Lp.aestronglyMeasurable Y).mk (Y : (ℕ → Ω) → E)
  have hym : Measurable y := (Lp.aestronglyMeasurable Y).stronglyMeasurable_mk.measurable
  have hye : (Y : (ℕ → Ω) → E)=ᵐ[R] y := (Lp.aestronglyMeasurable Y).ae_eq_mk
  have hyi : MemLp y 2 R := (Lp.memLp Y).ae_eq hye
  have heq : y=ᵐ[R] fun w => F (y (S w)) (w 0) := by
    filter_upwards [hye,hfix,hS.quasiMeasurePreserving.ae hye] with w h1 h2 h3
    rw [←h1,h2]
    change F (Y (S w)) (w 0)=F (y (S w)) (w 0)
    rw [h3]
  let π := R.map y
  have hp : IsProbabilityMeasure π :=
    (Measure.isProbabilityMeasure_map_iff hym.aemeasurable).mpr inferInstance
  have hpi : MemLp (fun x : E => x) 2 π :=
    (memLp_map_measure_iff (by fun_prop) hym.aemeasurable).mpr hyi
  have hj : R.map (fun w => (y (S w),w 0))=π.prod P := by
    let K := fun z : Ω × (ℕ → Ω) => (y z.2,z.1)
    have hKm : Measurable K := (hym.comp measurable_snd).prodMk measurable_fst
    have he : (fun w => (y (S w),w 0))=K ∘ (fun w : ℕ → Ω => (w 0,S w)) := rfl
    rw [he,←Measure.map_map hKm ((measurable_pi_apply 0).prodMk hS.measurable),hST]
    change (P.prod R).map ((Prod.map y id) ∘ Prod.swap)=π.prod P
    rw [←Measure.map_map (hym.prodMap measurable_id) measurable_swap,Measure.prod_swap,
      ←Measure.map_prod_map _ _ hym measurable_id,Measure.map_id]
  refine ⟨π,hp,hpi,?_⟩
  have hJm : Measurable (fun w : ℕ → Ω => (y (S w),w 0)) :=
    (hym.comp hS.measurable).prodMk (measurable_pi_apply 0)
  rw [←hj,Measure.map_map hF hJm]
  exact (Measure.map_congr heq).symm

end Asakura.Chapter8
