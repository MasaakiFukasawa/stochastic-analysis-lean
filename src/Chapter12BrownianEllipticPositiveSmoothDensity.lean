import Chapter12BrownianEllipticSmoothDensity
import Chapter12EllipticDensityPositive
import Chapter12ProbabilityTrim
open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology ContDiff NNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
theorem brownian_elliptic_positive_smooth_density {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (d n:ℕ) (T:ℝ) (hT:0<T)
    (mT:MeasurableSpace Ω) (hle:mT≤m) [IsProbabilityMeasure (P.trim hle)]
    [Nontrivial (FiniteWienerHilbert d T)]
    (W:FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 (P.trim hle))
    (hW:∀u,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) (P.trim hle))
    (B:Asakura.Chapter4.BrownianSystem P (d+1))
    (hB:∀z:BrownianTimeCoordinates d T,B.W z.1 (Asakura.FullAudit.realTimeClamp z.2.val)=ᵐ[P.trim hle]
      (W (brownianTimeDirection z):Ω → ℝ))
    (hYm:Measurable[mT] (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T))
    (hYp:∀p:ℝ≥0∞,p≠⊤ → MemLp (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T) p (P.trim hle))
    (D:Lp ℝ 2 (P.trim hle) →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 (P.trim hle)) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair (P.trim hle) W univ dense_univ (fun u _ => hW u) 2 (by simp))))
    (hd:DenseRange (fun f:D.domain => (f:Lp ℝ 2 (P.trim hle))))
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder (FiniteWienerHilbert d T) => c.valueLp (P.trim hle) W univ dense_univ (fun u _ => hW u) q hq))
    (v:Fin (d+1) → EuclideanSpace ℝ (Fin (n+1))) (x:EuclideanSpace ℝ (Fin (n+1)))
    (b:EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (ell:ℝ) (hell:0<ell)
    (hv:∀z:EuclideanSpace ℝ (Fin (n+1)),ell*‖z‖^2≤∑j,(inner ℝ z (v j))^2) :
    ∃S:C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))) → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))),
      ContDiff ℝ ∞ S ∧ (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s))) ∧
      ∃p:EuclideanSpace ℝ (Fin (n+1)) → ℝ,ContDiff ℝ ∞ p ∧ (∀y,0<p y) ∧
        @Measure.map Ω _ m _ (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T w)) ⟨T,hT.le,le_rfl⟩) P=
          volume.withDensity (fun y => ENNReal.ofReal (p y)) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨S,hS,hSeq,p,hp,hpn,hmap⟩ := @brownian_elliptic_smooth_density Ω mT (P.trim hle) inferInstance d n T hT inferInstance W hW
    (fun z => B.W z.1 (Asakura.FullAudit.realTimeClamp z.2.val)) hB
    (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T) hYm
    (fun _ _ _ => rfl) hYp D hD hg hd hdense v x b hb hbound ell hell hv
  let X := fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ _
    (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T w)) ⟨T,hT.le,le_rfl⟩
  have hXm:Measurable[mT] X := ((ContinuousMap.evalCLM ℝ (⟨T,hT.le,le_rfl⟩:Icc (0:ℝ) T) :
    C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))).continuous.comp
    (hS.continuous.comp (continuous_const.add ((columnOperator v).compLeftContinuous ℝ _).continuous))).measurable.comp hYm
  have htrim:@Measure.map Ω _ mT _ X (P.trim hle)=@Measure.map Ω _ m _ X P := by
    ext a ha
    rw [Measure.map_apply hXm ha,Measure.map_apply (hXm.mono hle le_rfl) ha,
      trim_measurableSet_eq hle (hXm ha)]
  have hmapP:@Measure.map Ω _ m _ X P=volume.withDensity (fun y => ENNReal.ofReal (p y)) := htrim.symm.trans hmap
  obtain ⟨K,hKb⟩ := hbound 1 le_rfl
  have hLip:LipschitzWith K b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hb.differentiable (by simp))
    intro y
    have hh : ‖fderiv ℝ b y‖≤(K:ℝ) := by simpa only [norm_iteratedFDeriv_one] using hKb y
    exact_mod_cast hh
  exact ⟨S,hS,hSeq,p,hp,elliptic_density_positive P B v ell hell hv x b K hLip T hT S
    hS.continuous hSeq p hp.continuous hpn hmapP,hmapP⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_elliptic_positive_smooth_density
