import Chapter5GaussianObservationInterval

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Spatial derivatives of the extension equal the actual Gaussian
averages of Df, including the boundary of the chosen time strip. -/
theorem backward_extension_spatial_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C)
    (g : E × ℝ → ℝ) (hg : ContDiff ℝ 2 g) (b S : ℝ)
    (he : ∀ p : E × ℝ,p.2≤b → g p=∫ z,f (p.1+Real.sqrt (S-p.2) • z) ∂ν)
    (p : E × ℝ) (hp : p.2≤b) (u : E) :
    fderiv ℝ g p (u,0)=∫ z,D (p.1+Real.sqrt (S-p.2) • z) u ∂ν := by
  obtain ⟨hA,_,_,_⟩ := averaged_bounded_fderiv ν hi f D hd hDc C hD
  have hs : (fun y => g (y,p.2))=(fun y => ∫ z,f (y+Real.sqrt (S-p.2) • z) ∂ν) :=
    funext (fun y => he (y,p.2) hp)
  have hgD := ((hg.differentiable (by norm_num)).differentiableAt (x := p)).hasFDerivAt
  have hmap : HasFDerivAt (fun y : E => (y,p.2)) (ContinuousLinearMap.inl ℝ E ℝ) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hh := hgD.comp p.1 hmap
  dsimp only [Function.comp_def] at hh
  rw [hs] at hh
  have heD := hh.unique (hA p.1 (S-p.2))
  have hDi : Integrable (fun z => D (p.1+Real.sqrt (S-p.2) • z)) ν :=
    Integrable.of_bound (hDc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hD _)
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L u) heD
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.integral_apply hDi] using hev


theorem spaceTimeCoordinates_basis_succ {k : ℕ} (i : Fin k) :
    spaceTimeCoordinates k (Pi.single i.succ 1)=(Pi.single i 1,0) := by
  ext j <;> simp [spaceTimeCoordinates,Pi.single_apply,Fin.succ_inj,Fin.succ_ne_zero]

/-- The derivative in a Brownian observation coordinate is the common
Gaussian-gradient integrand, independent of the chosen C² extension. -/
theorem backward_extension_coordinate_gradient
    {k : ℕ} (ν : Measure (Fin k → ℝ)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : Fin k → ℝ => z) ν)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C)
    (g : ((Fin k → ℝ) × ℝ) → ℝ) (hg : ContDiff ℝ 2 g) (b S : ℝ)
    (he : ∀ p : (Fin k → ℝ) × ℝ,p.2≤b → g p=∫ z,f (p.1+Real.sqrt (S-p.2) • z) ∂ν)
    (x : Fin (k+1) → ℝ) (hx : x 0≤b) (i : Fin k) :
    fderiv ℝ (fun y => g (spaceTimeCoordinates k y)) x (Pi.single i.succ 1)=
      ∫ z,D ((fun j => x j.succ)+Real.sqrt (S-x 0) • z) (Pi.single i 1) ∂ν := by
  have hh := ((hg.differentiable (by norm_num)).differentiableAt
    (x := spaceTimeCoordinates k x)).hasFDerivAt.comp x (spaceTimeCoordinates k).hasFDerivAt
  dsimp only [Function.comp_def] at hh
  rw [hh.fderiv,ContinuousLinearMap.comp_apply,spaceTimeCoordinates_basis_succ]
  exact backward_extension_spatial_gradient ν hi f D hd hDc C hD g hg b S he
    (spaceTimeCoordinates k x) hx (Pi.single i 1)

end Asakura.Chapter5
