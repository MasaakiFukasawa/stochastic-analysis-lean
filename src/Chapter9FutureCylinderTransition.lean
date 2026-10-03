import Chapter9BoundedTests

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Forward Markov transitions reduce every bounded test of finitely many
future observations to a bounded Borel function of the present state.
This is the finite-cylinder step needed for reversal of the filtration. -/
theorem future_cylinder_conditional_transition {Ω E ι : Type*}
    [m : MeasurableSpace Ω] [MeasurableSpace E] [LinearOrder ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ι → MeasurableSpace Ω)
    (hmono : Monotone F) (hle : ∀ t,F t≤m) (X : ι → Ω → E) (hX : ∀ t,Measurable[F t] (X t))
    (htrans : ∀ s t,s≤t → ∀ f : E → ℝ,IsBoundedBorel f →
      ∃ g : E → ℝ,IsBoundedBorel g ∧ P[(fun w => f (X t w))|F s]=ᵐ[P] (fun w => g (X s w)))
    (f : ι → E → ℝ) (hf : ∀ t,IsBoundedBorel (f t))
    (L : List ι) (s : ι) (hsorted : L.Pairwise (· ≤ ·)) (hs : ∀ t∈L,s≤t) :
    ∃ g : E → ℝ,IsBoundedBorel g ∧
      P[finiteTestProduct X f L|F s]=ᵐ[P] (fun w => g (X s w)) := by
  letI : MeasurableSpace Ω := m
  induction L generalizing s with
  | nil =>
    refine ⟨fun _ => 1,IsBoundedBorel.const 1,?_⟩
    simpa only [finiteTestProduct] using!
      (Filter.Eventually.of_forall (fun w => congrFun
        (condExp_of_stronglyMeasurable (hle s) stronglyMeasurable_const (integrable_const (1:ℝ))) w))
  | cons t L ih =>
    obtain ⟨hfirst,hrest⟩ := List.pairwise_cons.mp hsorted
    have hst : s≤t := hs t (by simp)
    obtain ⟨g,hg,hce⟩ := ih t hrest hfirst
    have hti : Integrable (finiteTestProduct X f L) P :=
      (finiteTestProduct_bounded X (fun u => (hX u).mono (hle u) le_rfl) f hf L).integrable P
    obtain ⟨C,_,hC⟩ := (hf t).2
    have hpull := condExp_stronglyMeasurable_mul_of_bound (hle t)
      ((hf t).1.comp (hX t)).stronglyMeasurable hti C (ae_of_all _ (fun w => hC (X t w)))
    have hstep : P[finiteTestProduct X f (t::L)|F t]=ᵐ[P]
        (fun w => (f t (X t w))*g (X t w)) := by
      apply hpull.trans
      filter_upwards [hce] with w hw
      change f t (X t w)*P[finiteTestProduct X f L|F t] w=f t (X t w)*g (X t w)
      rw [hw]
    obtain ⟨q,hq,hqce⟩ := htrans s t hst (fun y => f t y*g y) ((hf t).mul hg)
    refine ⟨q,hq,?_⟩
    exact (condExp_condExp_of_le (μ := P) (f := finiteTestProduct X f (t::L)) (hmono hst) (hle t)).symm.trans
      ((condExp_congr_ae (m := F s) hstep).trans hqce)
end Asakura.Chapter9
