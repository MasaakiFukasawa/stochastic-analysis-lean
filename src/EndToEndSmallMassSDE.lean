import EndToEndSmallMassPosition
import EndToEndSmallMassCoefficients
import Chapter8NewtonActualPosition

open MeasureTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- The small-mass limit for actual SDE solutions. Both moment estimates and
the position formula are derived; no estimate uniform in the mass is input. -/
theorem small_mass_sde_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (Γ : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hα : 0<α) (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0) (hg : LipschitzWith L g)
    (σ : Fin d → Fin n → ℝ) (ξ : Ω → Fin (d+d) → ℝ) (hξ : MemLp ξ 2 P)
    (Y : ℝ → HalfClosedTime → Ω → Fin (d+d) → ℝ)
    (hY : ∀ m,VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ.toContinuousLinearMap) (e (velocityProjection d z))) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => m⁻¹*σ i j)) ξ (Y m))
    (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun i z => e.symm (-Γ.symm (g (e z))) i)
      (fun i j _ => e.symm (Γ.symm (e (fun k => σ k j))) i)
      (fun w => positionProjection d (ξ w)) X)
    (T : ℝ) (hT : 0≤T) :
    Tendsto (fun m => sSup ((fun t => ∫w,‖e (positionProjection d (Y m (realTimeClamp t) w))-
      e (X (realTimeClamp t) w)‖^2 ∂P) '' Icc 0 T)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let b : ℝ → Fin (d+d) → (Fin (d+d) → ℝ) → ℝ := fun m => Fin.addCases (fun i z => velocityProjection d z i)
    (fun i z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ.toContinuousLinearMap) (e (velocityProjection d z))) i)
  let a : ℝ → Fin (d+d) → Fin n → (Fin (d+d) → ℝ) → ℝ := fun m => Fin.addCases (fun _ _ _ => (0:ℝ)) (fun i j _ => m⁻¹*σ i j)
  have hylip m : ∃K:ℝ,0≤K ∧ ∀ x y,(∑i,(b m i x-b m i y)^2)+
      (∑i,∑j,(a m i j x-a m i j y)^2)≤K*∑i,(x i-y i)^2 := by
    obtain ⟨K,hK,hk⟩ := newton_mass_lipschitz e Γ.toContinuousLinearMap g L hg m
    refine ⟨K,hK,?_⟩
    intro x y
    have he i j : a m i j x=a m i j y := by
      refine Fin.addCases ?_ ?_ i <;> intro k <;> simp only [a,Fin.addCases_left,Fin.addCases_right]
    simpa only [he,sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero] using hk x y
  let A := e.toContinuousLinearMap.comp (positionProjection d)
  have hpath (m : ℝ) : ∃Q:Ω → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin d)),
      Measurable Q ∧ MemLp Q 2 P ∧ ∀w (t:Icc (0:ℝ) T),Q w t=A (Y m (realTimeClamp t.val) w) := by
    obtain ⟨K,hK,hk⟩ := hylip m
    exact sde_coordinate_path P B K hK (b m) (a m) hk ξ hξ (Y m) (hY m) A T hT
  choose Q hQm hQ2 hQe using hpath
  obtain ⟨KX,hKX,hkx⟩ := overdamped_drift_lipschitz e Γ.symm.toContinuousLinearMap g L hg
  have hxlip x y : (∑i,(e.symm (-Γ.symm (g (e x))) i-e.symm (-Γ.symm (g (e y))) i)^2)+
      (∑i,∑j:Fin n,(e.symm (Γ.symm (e (fun k => σ k j))) i-e.symm (Γ.symm (e (fun k => σ k j))) i)^2)≤KX*∑i,(x i-y i)^2 := by
    simpa using hkx x y
  obtain ⟨Z,hZm,hZ2,hZe⟩ := sde_coordinate_path P B KX hKX _ _ hxlip _
    ((positionProjection d).comp_memLp' hξ) X hX e.toContinuousLinearMap T hT
  have hQat m w s (hs:s∈Icc 0 T) : Q m w (projIcc 0 T hT s)=e (positionProjection d (Y m (realTimeClamp s) w)) := by
    rw [projIcc_of_mem hT hs]
    exact hQe m w ⟨s,hs⟩
  have hZat w s (hs:s∈Icc 0 T) : Z w (projIcc 0 T hT s)=e (X (realTimeClamp s) w) := by
    rw [projIcc_of_mem hT hs]
    exact hZe w ⟨s,hs⟩
  have hqi m w t (ht:t∈Icc 0 T) (f:ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
      (∫s in 0..t,f s (Q m w (projIcc 0 T hT s)))=
      ∫s in 0..t,f s (e (positionProjection d (Y m (realTimeClamp s) w))) := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hQat m w s ⟨(uIcc_of_le ht.1 ▸ hs).1,(uIcc_of_le ht.1 ▸ hs).2.trans ht.2⟩]
  have hzi w t (ht:t∈Icc 0 T) : (∫s in 0..t,g (Z w (projIcc 0 T hT s)))=
      ∫s in 0..t,g (e (X (realTimeClamp s) w)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hZat w s ⟨(uIcc_of_le ht.1 ▸ hs).1,(uIcc_of_le ht.1 ▸ hs).2.trans ht.2⟩]
  have hj (m : {m:ℝ // 0<m}) := newton_actual_position P B e Γ g hg.continuous m.val m.property σ ξ (Y m.val) (hY m.val)
  choose J hJ hJI hJe using hj
  let N := fun m => if hm:0<m then J ⟨m,hm⟩ else 0
  let S := fun i j => e (fun k => σ k j) i
  have hs j : WithLp.toLp 2 (fun i => S i j)=e (fun k => σ k j) := by ext i; rfl
  have hb t w : WithLp.toLp 2 (fun i => ∑j,S i j*B.W j (realTimeClamp t) w)=
      ∑j,B.W j (realTimeClamp t) w • e (fun k => σ k j) := by
    ext i
    simp only [WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,S]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hN (m : ℝ) (hm : 0<m) (_hm1 : m≤1) (t : ℝ) (_ht : t∈Icc 0 T) i j : LocalMProcessWitness P B.F (N m t i j) := by
    simpa only [N,dif_pos hm] using hJ ⟨m,hm⟩ t i j
  have hNI (m : ℝ) (hm : 0<m) (_hm1 : m≤1) (t : ℝ) (_ht : t∈Icc 0 T) i j : ItoCovarianceFormula P B.F (B.W j)
      (fun z => (NormedSpace.exp ((t-z.2) • (-m⁻¹ • Γ.toContinuousLinearMap)) (WithLp.toLp 2 (fun i => S i j))) i) (N m t i j) := by
    simpa only [N,dif_pos hm,hs] using hJI ⟨m,hm⟩ t i j
  have hxraw := sde_random_linear_coordinate_equation P B
    (fun z => e.symm (-Γ.symm (g (e z))))
    (e.symm.continuous.comp ((Γ.symm.continuous.comp (hg.continuous.comp e.continuous)).neg))
    (fun i j => e.symm (Γ.symm (e (fun k => σ k j))) i) _ X hX e.toContinuousLinearMap
  have hxc w : Continuous (fun s => e (X (realTimeClamp s) w)) := e.continuous.comp
    (continuous_iff_continuousAt.mpr fun s => (hX.path w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt)
  have hx t (ht:t∈Icc 0 T) : ∀ᵐ w ∂P,Z w (projIcc 0 T hT t)=
      e (positionProjection d (ξ w))-Γ.symm (∫s in 0..t,g (Z w (projIcc 0 T hT s)))+
        Γ.symm (WithLp.toLp 2 (fun i => ∑j,S i j*B.W j (realTimeClamp t) w)) := by
    filter_upwards [hxraw] with w hw
    rw [hZat w t ht,hzi w t ht,hb]
    have hi := Γ.symm.toContinuousLinearMap.intervalIntegral_comp_comm ((hg.continuous.comp (hxc w)).intervalIntegrable 0 t (μ:=volume))
    change (∫s in 0..t,Γ.symm (g (e (X (realTimeClamp s) w))))=Γ.symm (∫s in 0..t,g (e (X (realTimeClamp s) w))) at hi
    simpa only [ContinuousLinearEquiv.coe_coe,e.apply_symm_apply,intervalIntegral.integral_neg,hi,
      map_sum,map_smul,sub_eq_add_neg] using hw t ht.1
  have hlim := small_mass_position_limit P B Γ.toContinuousLinearMap Γ.symm.toContinuousLinearMap α T hα hT hΓ S g L hg
    (fun w => e (positionProjection d (ξ w))) (fun w => e (velocityProjection d (ξ w)))
    (A.comp_memLp' hξ) ((e.toContinuousLinearMap.comp (velocityProjection d)).comp_memLp' hξ)
    Q Z hQm (fun m _ _ => hQ2 m) hZm hZ2 N hN hNI
    (fun m hm _ t ht => by
      filter_upwards [hJe ⟨m,hm⟩] with w hw
      rw [hQat m w t ht,hqi m w t ht (fun _ y => g y),
        hqi m w t ht (fun s y => NormedSpace.exp ((t-s) • (-m⁻¹ • Γ.toContinuousLinearMap)) (g y)),hb]
      simpa only [N,dif_pos hm,ContinuousLinearEquiv.coe_coe] using hw t ht.1) hx
  convert hlim using 1
  funext m
  congr 1
  apply Set.image_congr
  intro t ht
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp only
    rw [hQat m w t ht,hZat w t ht]

#print axioms small_mass_sde_limit
end Asakura.EndToEnd
