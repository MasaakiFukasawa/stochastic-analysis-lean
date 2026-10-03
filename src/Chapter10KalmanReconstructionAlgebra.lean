import Chapter10ReconstructedInformationAE

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Cancel the predicted drift in the original filter equation after the
actual integral identities have identified (KD) dot I with K dot Y minus
the integral of KCm. This is the second reconstruction equation. -/
theorem kalman_mean_reconstruction {d : ℕ}
    (T : ℝ) (hT : 0≤T) (m ZKY ZKDI : C(Icc (0:ℝ) T,Fin d → ℝ))
    (m0 : Fin d → ℝ) (A KC : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hA : Continuous A) (hKC : Continuous KC)
    (hm : ∀ t,m t=m0+(∫ s in 0..t.val,(A s-KC s) (m (projIcc 0 T hT s)))+ZKY t)
    (hKDI : ∀ t,ZKDI t=ZKY t-∫ s in 0..t.val,KC s (m (projIcc 0 T hT s))) :
    ∀ t,m t=m0+(∫ s in 0..t.val,A s (m (projIcc 0 T hT s)))+ZKDI t := by
  intro t
  have hmc : Continuous (fun s => m (projIcc 0 T hT s)) := m.continuous.comp continuous_projIcc
  have hsub := intervalIntegral.integral_sub ((hA.clm_apply hmc).intervalIntegrable (μ := volume) 0 t.val)
    ((hKC.clm_apply hmc).intervalIntegrable (μ := volume) 0 t.val)
  have he : (∫ s in 0..t.val,(A s-KC s) (m (projIcc 0 T hT s)))=
      (∫ s in 0..t.val,A s (m (projIcc 0 T hT s)))-
        ∫ s in 0..t.val,KC s (m (projIcc 0 T hT s)) := by
    simpa only [ContinuousLinearMap.sub_apply,Pi.sub_apply] using hsub
  rw [hm t,hKDI t,he]
  abel

/-- The inverse-integral identity recovers the original observation after
the predicted drift has been removed; Y0=0 is retained explicitly. -/
theorem kalman_observation_reconstruction {r : ℕ}
    (Y B ZDI : Fin r → ℝ) (hzero : ∀ i,Y i-B i=ZDI i) : Y=B+ZDI := by
  ext i
  have hh := hzero i
  change Y i=B i+ZDI i
  linarith

end Asakura.Chapter10
