import Chapter8BilinearPostcomposition
import Chapter8LinearPathContinuity
import Chapter8ContinuousPathFamily

open MeasureTheory Set
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Continuous dependence of the second variation, even when the second
drift derivative is merely continuous rather than Lipschitz. -/
theorem second_variation_parameter_continuous {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace P]
    (T : ℝ) (hT : 0 ≤ T) (L : ℝ) (hL : 0<L)
    (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hcD : Continuous D) (hcD₂ : Continuous D₂) (hDb : ∀ z,‖D z‖ ≤ L)
    (X : P → C(Icc (0:ℝ) T,E)) (J : P → C(Icc (0:ℝ) T,E →L[ℝ] E))
    (K : P → C(Icc (0:ℝ) T,E →L[ℝ] E →L[ℝ] E))
    (hcX : Continuous X) (hcJ : Continuous J)
    (hK : ∀ p t h k,K p t h k=∫ s in 0..t.val,
      D (X p (projIcc 0 T hT s)) (K p (projIcc 0 T hT s) h k)+
      D₂ (X p (projIcc 0 T hT s)) (J p (projIcc 0 T hT s) h) (J p (projIcc 0 T hT s) k)) :
    Continuous K := by
  let A : P → C(Icc (0:ℝ) T,(E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E)) :=
    fun p => ⟨fun t => bilinearPostcomposition (D (X p t)),
      bilinear_postcomposition_continuous.comp (hcD.comp (X p).continuous)⟩
  let R : P → C(Icc (0:ℝ) T,E →L[ℝ] E →L[ℝ] E) := fun p =>
    ⟨fun t => ((ContinuousLinearMap.compL ℝ E E E).flip (J p t)).comp ((D₂ (X p t)).comp (J p t)),
      (continuous_const.clm_apply (J p).continuous).clm_comp
        ((hcD₂.comp (X p).continuous).clm_comp (J p).continuous)⟩
  have hXev : Continuous (fun q : P × Icc (0:ℝ) T => X q.1 q.2) :=
    continuous_eval.comp ((hcX.comp continuous_fst).prodMk continuous_snd)
  have hJev : Continuous (fun q : P × Icc (0:ℝ) T => J q.1 q.2) :=
    continuous_eval.comp ((hcJ.comp continuous_fst).prodMk continuous_snd)
  have hAc : Continuous A := ContinuousMap.continuous_of_continuous_uncurry A
    (bilinear_postcomposition_continuous.comp (hcD.comp hXev))
  have hRc : Continuous R := ContinuousMap.continuous_of_continuous_uncurry R
    ((continuous_const.clm_apply hJev).clm_comp ((hcD₂.comp hXev).clm_comp hJev))
  apply linear_solution_parameter_continuous T hT L hL A R K hAc hRc
  · intro p
    apply (ContinuousMap.norm_le _ hL.le).mpr
    intro t
    exact (bilinear_postcomposition_norm _).trans (hDb _)
  · intro p t
    have hc : Continuous (fun s => A p (projIcc 0 T hT s) (K p (projIcc 0 T hT s))+R p (projIcc 0 T hT s)) :=
      (((A p).continuous.comp continuous_projIcc).clm_apply
        ((K p).continuous.comp continuous_projIcc)).add ((R p).continuous.comp continuous_projIcc)
    apply ContinuousLinearMap.ext
    intro h
    apply ContinuousLinearMap.ext
    intro k
    rw [hK p t h k,ContinuousLinearMap.intervalIntegral_apply
      (φ := fun s => A p (projIcc 0 T hT s) (K p (projIcc 0 T hT s))+R p (projIcc 0 T hT s))
      (hc.intervalIntegrable 0 t.val),ContinuousLinearMap.intervalIntegral_apply
      (φ := fun s => (A p (projIcc 0 T hT s) (K p (projIcc 0 T hT s))+R p (projIcc 0 T hT s)) h)
      ((hc.clm_apply continuous_const).intervalIntegrable 0 t.val)]
    rfl

end Asakura.Chapter8
