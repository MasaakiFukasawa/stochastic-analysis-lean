import Chapter4VectorAdaptedLimit
import Chapter4VectorPrefixMoment
import Chapter4PathMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
variable {dim : ℕ}
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma prefix_path_endpoint {R : ℝ} (hR : 0≤R) (Y : C(Icc (0:ℝ) R,Fin dim → ℝ)) :
    prefixPath hR Y R=Y := by
  apply ContinuousMap.ext
  intro r
  change Y (min r (projIcc 0 R hR R))=Y r
  rw [projIcc_of_mem hR ⟨hR,le_rfl⟩,min_eq_left (show r≤(⟨R,hR,le_rfl⟩ : Icc (0:ℝ) R) from r.property.2)]

/-- Assemble the manuscript's Volterra estimate, factorial iteration,
Tonelli argument, completed adaptation and L² convergence in one result. -/
theorem volterra_adapted_path_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0≤R) (F : Icc (0:ℝ) R → MeasurableSpace Ω)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X : ℕ → Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm : ∀ n,Measurable[m] (X n)) (hi : ∀ n,MemLp (X n) 2 P)
    (ha : ∀ n t,Measurable[F t] (fun w => X n w t))
    (c : ℝ) (hc : 0≤c)
    (hstep : ∀ n t,t∈Icc 0 R →
      (∫ w,‖prefixPath hR (X (n+2) w-X (n+1) w) t‖^2 ∂P)≤
        c*(∫ r in 0..t,(∫ w,‖prefixPath hR (X (n+1) w-X n w) r‖^2 ∂P))) :
    ∃ Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ),Measurable[m] Y ∧
      (∀ t,Measurable[F t] (fun w => Y w t)) ∧ MemLp Y 2 P ∧
      (∀ᵐ w ∂P,Tendsto (fun n => X n w) atTop (𝓝 (Y w))) ∧
      Tendsto (fun n => eLpNorm (fun w => Y w-X n w) 2 P) atTop (𝓝 0) := by
  letI : MeasurableSpace Ω := m
  let A := ∫ w,‖X 1 w-X 0 w‖^2 ∂P
  let u := fun n t => ∫ w,‖prefixPath hR (X (n+1) w-X n w) t‖^2 ∂P
  have hA : 0≤A := integral_nonneg (fun _ => sq_nonneg _)
  have hu n : Continuous (u n) :=
    prefix_square_moment_continuous P hR _ ((hm (n+1)).sub (hm n)) ((hi (n+1)).sub (hi n))
  have hbase t (_ht : t∈Icc 0 R) : u 0 t≤A := by
    have hnorm := ((hi 1).sub (hi 0)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
    have hint : Integrable (fun w => ‖prefixPath hR (X 1 w-X 0 w) t‖^2) P := by
      apply hnorm.mono' ((prefix_path_measurable hR _ ((hm 1).sub (hm 0)) t).norm.pow_const 2).aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro w
      simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sq] using
        (pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hR (X 1 w-X 0 w) t) 2)
    exact integral_mono hint hnorm (fun w =>
      pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hR (X 1 w-X 0 w) t) 2)
  have hfac := picard_factorial_bound u A c R hc hu hbase hstep
  have hb n : eLpNorm (fun w => X (n+1) w-X n w) 2 P≤
      ENNReal.ofReal (Real.sqrt A*Real.sqrt ((c*R)^n/(n.factorial:ℝ))) := by
    have h := hfac n R ⟨hR,le_rfl⟩
    simp only [u,prefix_path_endpoint] at h
    rw [path_eLpNorm_eq_sqrt_moment P (fun w => X (n+1) w-X n w) ((hi (n+1)).sub (hi n))]
    apply ENNReal.ofReal_le_ofReal
    calc Real.sqrt (∫ w,‖X (n+1) w-X n w‖^2 ∂P) ≤ Real.sqrt (A*c^n*R^n/(n.factorial:ℝ)) := Real.sqrt_le_sqrt h
         _ = Real.sqrt A*Real.sqrt ((c*R)^n/(n.factorial:ℝ)) := by
           rw [← Real.sqrt_mul hA,mul_pow]
           congr 1
           ring
  exact adapted_picard_iterates_limit P F hnull X hm ha (hi 0) (Real.sqrt A) (c*R) (mul_nonneg hc hR) hb

end Asakura.Chapter4.Vector
