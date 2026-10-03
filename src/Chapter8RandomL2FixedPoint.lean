import Chapter8PullbackLimit
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the pullback random fixed point in L2. The random evolution
operator is built from the one-step flow and a measure-preserving past shift;
its contraction and convergence are conclusions, not assumed cocycle bounds. -/
theorem random_L2_fixed_point {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → Ω) (hS : MeasurePreserving S P P)
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F))
    (hF0 : MemLp (F 0) 2 P) (ρ : ℝ≥0) (hρ : ρ<1)
    (hLip : ∀ w x y,‖F x w-F y w‖≤(ρ:ℝ)*‖x-y‖) :
    ∃ (T : Lp E 2 P → Lp E 2 P) (Y : Lp E 2 P),
      (∀ u,(T u : Ω → E)=ᵐ[P] fun w => F (u (S w)) w) ∧
      LipschitzWith ρ T ∧ T Y=Y ∧
      Tendsto (fun n : ℕ => T^[n] 0) atTop (nhds Y) ∧
      (∀ n : ℕ,‖T^[n] 0-Y‖≤‖T 0‖*(ρ:ℝ)^n/(1-ρ)) ∧
      (Y : Ω → E)=ᵐ[P] fun w => F (Y (S w)) w := by
  have hmem (u : Lp E 2 P) : MemLp (fun w => F (u (S w)) w) 2 P := by
    have hu := (Lp.memLp u).comp_measurePreserving hS
    have hm : AEStronglyMeasurable (fun w => F (u (S w)) w) P :=
      (hF.comp_aemeasurable (hu.aestronglyMeasurable.aemeasurable.prodMk measurable_id.aemeasurable)).aestronglyMeasurable
    apply ((hu.norm.const_mul (ρ:ℝ)).add hF0.norm).mono' hm
    apply ae_of_all
    intro w
    have hh := hLip w (u (S w)) 0
    simpa only [sub_zero,Pi.add_apply,Function.comp_def] using
      (norm_le_norm_sub_add (F (u (S w)) w) (F 0 w)).trans (add_le_add hh le_rfl)
  let T : Lp E 2 P → Lp E 2 P := fun u => (hmem u).toLp (fun w => F (u (S w)) w)
  have hTe u : (T u : Ω → E)=ᵐ[P] fun w => F (u (S w)) w := (hmem u).coeFn_toLp
  have hTL : LipschitzWith ρ T := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm,dist_eq_norm]
    let U := Lp.compMeasurePreserving S hS u
    let V := Lp.compMeasurePreserving S hS v
    have hb : ∀ᵐ w ∂P,‖(T u-T v) w‖≤(ρ:ℝ)*‖(U-V) w‖ := by
      filter_upwards [Lp.coeFn_sub (T u) (T v),hTe u,hTe v,Lp.coeFn_sub U V,
        Lp.coeFn_compMeasurePreserving u hS,Lp.coeFn_compMeasurePreserving v hS] with w h1 h2 h3 h4 h5 h6
      rw [h1,h4]
      simp only [Pi.sub_apply]
      rw [h2,h3]
      change ‖F (u (S w)) w-F (v (S w)) w‖≤(ρ:ℝ)*‖U w-V w‖
      rw [show U w=u (S w) from h5,show V w=v (S w) from h6]
      exact hLip w _ _
    have hh := Lp.norm_le_mul_norm_of_ae_le_mul hb
    have he : ‖U-V‖=‖u-v‖ := by
      dsimp only [U,V]
      rw [←map_sub,Lp.norm_compMeasurePreserving]
    rwa [he] at hh
  have hTc : ContractingWith ρ T := ⟨hρ,hTL⟩
  let Y := hTc.fixedPoint
  have hy : T Y=Y := hTc.fixedPoint_isFixedPt
  refine ⟨T,Y,hTe,hTL,hy,hTc.tendsto_iterate_fixedPoint 0,?_,?_⟩
  · intro n
    have h := hTc.apriori_dist_iterate_fixedPoint_le 0 n
    simpa only [dist_eq_norm,zero_sub,norm_neg,Y] using h
  · have h := hTe Y
    rwa [hy] at h

end Asakura.Chapter8
