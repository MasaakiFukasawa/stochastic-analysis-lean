import Chapter12FiniteBrownianPolygonal
import Chapter12VectorPolygonalLp
import Chapter12AdditiveApproximationLp

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Constructing the additive solution map and the finite-grid approximants
from the Brownian paths proves the zeroth-order convergence in the SDE
approximation lemma, for any constant diffusion map. -/
theorem brownian_sde_solution_approximation {Ω E : Type*} {d : ℕ} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : Fin d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i,IsPreBrownianReal (B i) P) (hm : ∀ i t,Measurable (B i t))
    (hc : ∀ i w,Continuous (fun t => B i t w))
    (A : (Fin d → ℝ) →L[ℝ] E) (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b)
    (T : ℝ≥0) (hT : 0<T) (x : E) :
    let X := fun w => (A.compLeftContinuous ℝ (Icc (0:ℝ) T)) (finiteBrownianCompactPath B hc T w)
    ∃ S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),Continuous S ∧
      (∀ q t,S q t=q.1+(∫ s in 0..t.val,b (S q (projIcc (0:ℝ) (T:ℝ) T.property s)))+q.2 t) ∧
      ∀ p : ℝ≥0∞,1≤p → p≠⊤ →
      Tendsto (fun n => eLpNorm (fun w =>
        S (x,polygonalCompact (fun t => A (fun i => B i ⟨max t 0,le_max_right _ _⟩ w))
          T ((T:ℝ)/(n+1:ℕ)) (n+1))-S (x,X w)) p P) atTop (𝓝 0) := by
  intro X
  obtain ⟨S,hcS,hS⟩ := Asakura.Chapter8.additive_path_map_exists b K hb T T.property
  refine ⟨S,hcS,hS,?_⟩
  let f := fun t w => A (fun i => B i ⟨max t 0,le_max_right _ _⟩ w)
  have hfm : ∀ t,Measurable (f t) := fun t => A.continuous.measurable.comp
    (Measurable.of_eval (fun i => hm i _))
  have he : ∀ w t,X w t=f t w := by
    intro w t
    change A (fun i => B i ⟨t.val,t.property.1⟩ w)=A (fun i => B i ⟨max t.val 0,le_max_right _ _⟩ w)
    simp only [max_eq_left t.property.1]
  have hmesh (n : ℕ) : 0<(T:ℝ)/(n+1:ℕ) := div_pos hT (by positivity)
  have hmeshT (n : ℕ) : ((n+1:ℕ):ℝ)*((T:ℝ)/(n+1:ℕ))=T := by field_simp
  have hmeshl : Tendsto (fun n : ℕ => (T:ℝ)/(n+1:ℕ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (T:ℝ))
  intro p hp hpt
  have hX : MemLp X p P := (A.compLeftContinuous ℝ (Icc (0:ℝ) T)).comp_memLp'
    (finite_brownian_path_memLp P B hB hm hc T p hpt)
  apply additive_approximation_Lp P b K hb T T.property S hcS hS x X
    (fun n w => polygonalCompact (f · w) T ((T:ℝ)/(n+1:ℕ)) (n+1))
    (fun n => (polygonalCompact_measurable_vector f hfm T _ _).aestronglyMeasurable) ?_ ?_ p hp hpt hX
  · intro n
    exact ae_of_all _ (fun w => constructed_polygonal_norm_bound (f · w) T _ (hmesh n)
      (n+1) (Nat.succ_pos n) (hmeshT n) (X w) (he w))
  · exact ae_of_all _ (fun w => constructed_polygonal_convergence (f · w) T (X w) (he w)
      _ _ hmesh (fun n => Nat.succ_pos n) hmeshT hmeshl)

end Asakura.Chapter12
