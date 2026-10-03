import Chapter12AsianPathAverage

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianBridgePath (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) : C(Icc (0:ℝ) T,ℝ) :=
  ⟨fun s => f s-s.val/T*f ⟨T,hT,le_rfl⟩,by fun_prop⟩

theorem brownianBridgePath_measurable (T : ℝ) (hT : 0 ≤ T) :
    Measurable (brownianBridgePath T hT) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact (ContinuousMap.measurable_eval s).sub
    ((ContinuousMap.measurable_eval (⟨T,hT,le_rfl⟩ : Icc (0:ℝ) T)).const_mul (s.val/T))

/-- Recombining the bridge and its independent terminal coordinate recovers
exactly the original Black--Scholes arithmetic average. -/
theorem asian_bridge_average_identity (x σ r T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    asianBridgeAverage x σ r T hT (brownianBridgePath T hT f,f ⟨T,hT,le_rfl⟩) =
      (∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s)))/T := by
  unfold asianBridgeAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT] at hs
  have he : (projIcc 0 T hT s).val = s := by simp [projIcc,hs.1,hs.2]
  change x*Real.exp ((r-σ^2/2)*s+σ*(f (projIcc 0 T hT s)-
    (projIcc 0 T hT s).val/T*f ⟨T,hT,le_rfl⟩)+σ*s/T*f ⟨T,hT,le_rfl⟩) = _
  rw [he]
  congr 1
  congr 1
  ring

/-- Atomlessness now applies to the actual average, with the bridge
constructed from the original path rather than supplied as an extra input. -/
theorem black_scholes_average_no_atom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x σ r T : ℝ)
    (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X) (hXg : HasGaussianLaw X P)
    (hcov : ∀ s : Icc (0:ℝ) T,
      cov[(fun w => X w ⟨T,hT.le,le_rfl⟩),(fun w => X w s); P] = s.val)
    (hterminal : HasLaw (fun w => X w ⟨T,hT.le,le_rfl⟩) (gaussianReal 0 ⟨T,hT.le⟩) P)
    (K : ℝ) :
    P {w | (∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*X w (projIcc 0 T hT.le s)))/T = K} = 0 := by
  have h := asian_average_no_atom P x σ r T hx hσ hT X (fun w => brownianBridgePath T hT.le (X w))
    hXm ((brownianBridgePath_measurable T hT.le).comp hXm) hXg hcov
    (fun _ _ => rfl) hterminal K
  simpa only [asian_bridge_average_identity] using h

end Asakura.Chapter12
