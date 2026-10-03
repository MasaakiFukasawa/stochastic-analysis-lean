import Chapter12ConcreteCylinderDensity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Approximation using only the specified directions. In Clark--Ocone the
coordinates and directions here are restricted to times not exceeding a. -/
theorem restricted_cylinder_mem_closure {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (direction : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (direction t) : Ω → ℝ))
    (V : Set H) (hV : ∀ t, direction t ∈ V)
    (times : ℕ → K) (htimes : DenseRange times)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (F : Lp ℝ p P)
    (hgen : AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] F P) :
    F ∈ closure {G : Lp ℝ p P | ∃ c : SmoothCylinder H,
      (∀ j, c.direction j ∈ V) ∧ G = c.valueLp P W S hS hcore p hp} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n,g,hgc,hgd,hge⟩ := continuous_process_cylinder_Lp_density P X hXm hXc times htimes
    F hgen p (Fact.out : 1 ≤ p) hp (Lp.memLp F) ε hε
  let c := compactSmoothCylinder (fun i : Fin n => direction (times i)) g hgd hgc
  have hc : (c.valueLp P W S hS hcore p hp : Ω → ℝ) =ᵐ[P]
      (fun w => g (fun i => X (times i) w)) := by
    filter_upwards [(c.value_memLp P W S hS hcore p hp).coeFn_toLp,
      ae_all_iff.mpr (fun i : Fin n => hXW (times i))] with w hw hcoord
    change (c.value_memLp P W S hS hcore p hp).toLp _ w = _
    rw [hw]
    dsimp only [SmoothCylinder.value,c,compactSmoothCylinder]
    congr 1
    exact (funext hcoord).symm
  refine ⟨c.valueLp P W S hS hcore p hp,⟨c,fun j => hV (times j),rfl⟩,?_⟩
  rw [dist_eq_norm,Lp.norm_def]
  have he : ((F-c.valueLp P W S hS hcore p hp : Lp ℝ p P) : Ω → ℝ) =ᵐ[P]
      (fun w => F w-g (fun i => X (times i) w)) := by
    filter_upwards [Lp.coeFn_sub F (c.valueLp P W S hS hcore p hp),hc] with w hw hv
    rw [hw,Pi.sub_apply,hv]
  rw [eLpNorm_congr_ae he]
  exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hge) ENNReal.ofReal_ne_top).mpr hge |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

end Asakura.Chapter12
