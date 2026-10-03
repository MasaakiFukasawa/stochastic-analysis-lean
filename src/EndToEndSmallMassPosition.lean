import Chapter8SmallMassConvergence
import Chapter8SmallMassUniformInputs
import Chapter8SmallMassUniformPosition
import Chapter8PositionKernel
import Chapter8OverdampedDifference

open MeasureTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The two Gronwall steps are connected: no mass-uniform position or force
moment bound, moment continuity, or small remainder is assumed. -/
theorem small_mass_position_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (Γ M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α T : ℝ) (hα : 0<α) (hT : 0≤T)
    (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫) (S : Fin d → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0) (hg : LipschitzWith L g)
    (q v : Ω → EuclideanSpace ℝ (Fin d)) (hq : MemLp q 2 P) (hv : MemLp v 2 P)
    (Q : ℝ → Ω → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin d)))
    (X : Ω → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin d)))
    (hQm : ∀ m,Measurable (Q m)) (hQ2 : ∀ m,0<m → m≤1 → MemLp (Q m) 2 P)
    (hXm : Measurable X) (hX2 : MemLp X 2 P)
    (N : ℝ → ℝ → Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ i j,LocalMProcessWitness P B.F (N m t i j))
    (hNI : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => (NormedSpace.exp ((t-z.2) • (-m⁻¹ • Γ)) (WithLp.toLp 2 (fun i => S i j))) i) (N m t i j))
    (hpos : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ᵐ w ∂P,
      Q m w (projIcc 0 T hT t)=q w-M (∫s in 0..t,g (Q m w (projIcc 0 T hT s)))+
        M (WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp t) w))+
        (m • M (v w-NormedSpace.exp (t • (-m⁻¹ • Γ)) (v w))+
          M (∫s in 0..t,NormedSpace.exp ((t-s) • (-m⁻¹ • Γ)) (g (Q m w (projIcc 0 T hT s))))-
          M (WithLp.toLp 2 (fun i => ∑ j,N m t i j (realTimeClamp t) w))))
    (hx : ∀ t∈Icc 0 T,∀ᵐ w ∂P,X w (projIcc 0 T hT t)=
      q w-M (∫s in 0..t,g (X w (projIcc 0 T hT s)))+
        M (WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp t) w))) :
    Tendsto (fun m => sSup ((fun t => ∫w,‖Q m w (projIcc 0 T hT t)-X w (projIcc 0 T hT t)‖^2 ∂P) '' Icc 0 T))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let A := fun (m t : ℝ) w => q w+m • M (v w-NormedSpace.exp (t • (-m⁻¹ • Γ)) (v w))
  let Z := fun (m t : ℝ) w => M (WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp t) w)-
    WithLp.toLp 2 (fun i => ∑ j,N m t i j (realTimeClamp t) w))
  let K0 := fun (m t s : ℝ) => M.comp (NormedSpace.exp ((t-s) • (-m⁻¹ • Γ))-ContinuousLinearMap.id ℝ _)
  let CA := 3*((∫w,‖q w‖^2 ∂P)+4*‖M‖^2*(∫w,‖v w‖^2 ∂P))
  let CN := 3*‖M‖^2*(T*(∑j,‖WithLp.toLp 2 (fun i => S i j)‖^2)+(∑j,‖WithLp.toLp 2 (fun i => S i j)‖^2)/(2*α))
  have hCA : 0≤CA := by dsimp [CA]; positivity
  have hCN : 0≤CN := by dsimp [CN]; positivity
  have hi m hm hm1 t ht := small_mass_uniform_inputs P B Γ M S α m t T hα hm hm1 ht.1 ht.2 hΓ q v hq hv
    (N m t) (hN m hm hm1 t ht) (hNI m hm hm1 t ht)
  have hec (m t : ℝ) : Continuous (fun s : ℝ => NormedSpace.exp ((t-s) • (-m⁻¹ • Γ))) :=
    (continuous_iff_continuousAt.mpr (fun r => (hasDerivAt_exp_smul_const (-m⁻¹ • Γ) r).continuousAt)).comp
      (continuous_const.sub continuous_id)
  have hKc m t : Continuous (K0 m t) := continuous_const.clm_comp ((hec m t).sub continuous_const)
  have hKb m (hm : 0<m) t s (hs : s∈Icc 0 t) : ‖K0 m t s‖≤2*‖M‖ :=
    position_kernel_norm_bound Γ M α m (t-s) hα.le hm (sub_nonneg.mpr hs.2) hΓ
  have he (m : ℝ) (hm : 0<m) (hm1 : m≤1) (t : ℝ) (ht : t∈Icc 0 T) : ∀ᵐ w ∂P,Q m w (projIcc 0 T hT t)=
      A m t w+(∫s in 0..t,K0 m t s (g (Q m w (projIcc 0 T hT s))))+Z m t w := by
    filter_upwards [hpos m hm hm1 t ht] with w hw
    have hh := position_drift_kernel_identity M _ (hec m t)
      (fun s => g (Q m w (projIcc 0 T hT s))) (hg.continuous.comp ((Q m w).continuous.comp continuous_projIcc)) t
    dsimp only [A,Z,K0]
    rw [←hh,hw]
    simp only [map_sub]
    abel
  obtain ⟨CQ,hCQ,hCQb⟩ := small_mass_uniform_position P T hT g L hg Q (fun m _ _ => hQm m) hQ2
    K0 (2*‖M‖) (by positivity) (fun m _ _ t _ => hKc m t)
    (fun m hm _ t _ s hs => hKb m hm t s hs) A Z CA CN hCA hCN
    (fun m hm hm1 t ht => (hi m hm hm1 t ht).1)
    (fun m hm hm1 t ht => (hi m hm hm1 t ht).2.1)
    (fun m hm hm1 t ht => (hi m hm hm1 t ht).2.2.1)
    (fun m hm hm1 t ht => (hi m hm hm1 t ht).2.2.2) he
  obtain ⟨G,hG,hgG⟩ := random_lipschitz_force_moment P g L hg
  let H := fun m (z : Ω × ℝ) => g (Q m z.1 (projIcc 0 T hT z.2))
  let K := fun m (z : Ω × ℝ) => H m z-g (X z.1 (projIcc 0 T hT z.2))
  let D := fun m t w => Q m w (projIcc 0 T hT t)-X w (projIcc 0 T hT t)
  have hHm m : Measurable (H m) := hg.continuous.measurable.comp
    ((measurable_uncurry_of_continuous_of_measurable
      (fun w => (Q m w).continuous.comp continuous_projIcc)
      (fun s => by
        change Measurable (fun w => Q m w (projIcc 0 T hT s))
        exact (continuous_eval_const (projIcc 0 T hT s)).measurable.comp (hQm m))).comp measurable_swap)
  have hxF := finite_path_force_integrability P T hT X hXm hX2 g L hg
  have hqF m hm hm1 := finite_path_force_integrability P T hT (Q m) (hQm m) (hQ2 m hm hm1) g L hg
  have heval m hm hm1 s := random_path_evaluation_memLp P (Q m) (hQm m) (hQ2 m hm hm1) (projIcc 0 T hT s)
  have hxval s := random_path_evaluation_memLp P X hXm hX2 (projIcc 0 T hT s)
  apply small_mass_convergence_from_position_formula P B Γ M α T (G*(1+CQ)) L hα hT (by positivity)
    hΓ (fun j => WithLp.toLp 2 (fun i => S i j)) v hv H K hHm (fun m => (hHm m).sub hxF.1)
    (fun m hm hm1 => (hqF m hm hm1).2)
    (fun m hm hm1 t ht => ((hqF m hm hm1).2 t ht).sub (hxF.2 t ht))
    (fun m hm hm1 s hs => ((hgG _ (heval m hm hm1 s)).2).trans
      (mul_le_mul_of_nonneg_left (by linarith [hCQb m hm hm1 s hs]) hG))
    N hN hNI D
  · intro m hm hm1
    exact ((path_square_moment_continuous P (fun w => Q m w-X w)
      ((hQm m).sub hXm) ((hQ2 m hm hm1).sub hX2)).comp continuous_projIcc).continuousOn
  · intro m hm hm1 s hs
    exact (random_force_difference P g L hg _ _ (heval m hm hm1 s) (hxval s)).2
  · intro m hm hm1 t ht
    filter_upwards [hpos m hm hm1 t ht,hx t ht] with w hp hxx
    have hh := overdamped_position_difference M
      (fun s => Q m w (projIcc 0 T hT s)) (fun s => X w (projIcc 0 T hT s)) g
      ((Q m w).continuous.comp continuous_projIcc) ((X w).continuous.comp continuous_projIcc)
      hg.continuous (q w) _ _ t hp hxx
    simpa only [D,H,K,ContinuousLinearMap.neg_apply,sub_eq_add_neg] using hh

#print axioms small_mass_position_limit
end Asakura.EndToEnd
