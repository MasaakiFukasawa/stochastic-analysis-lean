import Chapter9StationaryExample

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem reversed_path_endpoint {E : Type*} [TopologicalSpace E]
    (X : ℝ → E) (hX : ContinuousAt X 0) (T : ℝ) :
    Tendsto (fun s => X (T-s)) (𝓝[<] T) (𝓝 (X 0)) := by
  have ht : Tendsto (fun s : ℝ => T-s) (𝓝[<] T) (𝓝 0) := by
    simpa using (show Continuous (fun s : ℝ => T-s) by fun_prop).continuousAt (x := T) |>.tendsto.mono_left nhdsWithin_le_nhds
  exact hX.tendsto.comp ht

theorem point_initial_reverse_drift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a v : ℝ) (x y : E) :
    y+(2:ℝ) • ((-1/v) • (y-a • x)) = y-(2/v) • (y-a • x) := by
  rw [smul_smul]
  have he : (2:ℝ)*(-1/v)=-(2/v) := by ring
  rw [he,neg_smul]
  simp only [sub_eq_add_neg]

/-- Stationary OU two-time laws cannot equal those of constant paths:
their expected squared displacement is strictly positive. -/
theorem stationary_two_time_laws_differ {d : ℕ} (hd : 0<d) (t : ℝ) (ht : 0<t) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    (γ.prod γ).map (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (z.1,Real.exp (-t) • z.1+Real.sqrt (1-Real.exp (-2*t)) • z.2)) ≠
      γ.map (fun x => (x,x)) := by
  dsimp only
  intro he
  let F := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖z.2-z.1‖^2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hleft : (∫ z,F z ∂(((stdGaussian (EuclideanSpace ℝ (Fin d))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
      (fun z => (z.1,Real.exp (-t) • z.1+Real.sqrt (1-Real.exp (-2*t)) • z.2))))=
      2*(d:ℝ)*(1-Real.exp (-t)) := by
    rw [integral_map (by fun_prop) hF.aestronglyMeasurable]
    have hx (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
        F (z.1,Real.exp (-t) • z.1+Real.sqrt (1-Real.exp (-2*t)) • z.2)=
        ‖(Real.exp (-t)-1) • z.1+Real.sqrt (1-Real.exp (-2*t)) • z.2‖^2 := by
      dsimp [F]
      congr 2
      rw [sub_smul,one_smul]
      abel
    simp_rw [hx]
    exact stationary_ou_displacement t ht
  rw [he,integral_map (by fun_prop) hF.aestronglyMeasurable] at hleft
  simp only [F,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero] at hleft
  exact (stationary_ou_displacement_positive hd t ht).ne' hleft.symm
end Asakura.Chapter9
