import Chapter5SpaceTimeCoordinates
import Chapter5BackwardGaussianGenerator

open Set
open scoped BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The covariance density of stopped observation coordinates gives
exactly the backwards heat generator on the current interval. -/
theorem stopped_observation_generator_zero {d k : ℕ}
    (index : Fin k → Fin d) (active : Fin k → Prop) [DecidablePred active]
    (τ : Fin k → ℝ) (a b r : ℝ) (hab : a≤b) (hr : r∈Icc a b)
    (hpast : ∀ i,¬active i → τ i≤a) (hcurrent : ∀ i,active i → τ i=b)
    (g : ((Fin k → ℝ) × ℝ) → ℝ) (hg : ContDiff ℝ 2 g)
    (hzero : ∀ p : (Fin k → ℝ) × ℝ,p.2≤b →
      fderiv ℝ g p (0,1)+(1/2:ℝ)*∑ l : Fin d,
        fderiv ℝ (fderiv ℝ g) p (observationNoiseMap index active (Pi.single l 1),0)
          (observationNoiseMap index active (Pi.single l 1),0)=0)
    (x : Fin (k+1) → ℝ) (hx : x 0=r) :
    let B := Fin.cons ((Iio b).indicator (fun _ => (1:ℝ)) r) (fun _ : Fin k => (0:ℝ))
    let Q := fun l : Fin d => Fin.cons 0 (fun i : Fin k => if r<τ i ∧ index i=l then (1:ℝ) else 0)
    (∑ i,fderiv ℝ (fun y => g (spaceTimeCoordinates k y)) x (Pi.single i 1)*B i)+
      (∑ i,∑ j,fderiv ℝ (fderiv ℝ (fun y => g (spaceTimeCoordinates k y))) x
        (Pi.single i 1) (Pi.single j 1)*(∑ l,Q l i*Q l j))/2=0 := by
  dsimp only
  apply linear_generator_pullback g hg (spaceTimeCoordinates k) x
  simp only [spaceTimeCoordinates_cons]
  by_cases h : r<b
  · have he l : (fun i : Fin k => if r<τ i ∧ index i=l then (1:ℝ) else 0)=
        observationNoiseMap index active (Pi.single l 1) := by
      funext i
      exact observation_noise_before_endpoint index active τ a b r hr.1 h hpast hcurrent l i
    simp_rw [he]
    rw [indicator_of_mem (show r∈Iio b from h)]
    exact hzero _ (by simpa only [spaceTimeCoordinates_time,hx] using hr.2)
  · have hre : r=b := le_antisymm hr.2 (le_of_not_gt h)
    have hτ i : τ i≤b := by
      by_cases hi : active i
      · exact (hcurrent i hi).le
      · exact (hpast i hi).trans hab
    have he l : (fun i : Fin k => if r<τ i ∧ index i=l then (1:ℝ) else 0)=0 := by
      funext i
      rw [hre]
      exact observation_noise_at_endpoint index τ b hτ l i
    simp_rw [he]
    rw [indicator_of_notMem (show r∉Iio b from h)]
    change fderiv ℝ g (spaceTimeCoordinates k x) (0 : (Fin k → ℝ) × ℝ)+
      (1/2:ℝ)*∑ l : Fin d,fderiv ℝ (fderiv ℝ g) (spaceTimeCoordinates k x)
        (0 : (Fin k → ℝ) × ℝ) (0 : (Fin k → ℝ) × ℝ)=0
    simp

end Asakura.Chapter5
