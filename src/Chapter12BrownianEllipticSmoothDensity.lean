import Chapter12BrownianForcingCovariance
import Chapter12BrownianClosedForcingGradient
import Chapter12SmoothSolutionAllSobolev
import Chapter12ForcingSolutionUniqueness
import Chapter12MalliavinNondegenerateSmoothDensity
import Chapter12CovarianceInverseMoments

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology ContDiff NNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem brownian_elliptic_smooth_density {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (d n:ℕ) (T:ℝ) (hT:0<T)
    [Nontrivial (FiniteWienerHilbert d T)]
    (W:FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW:∀u,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B:BrownianTimeCoordinates d T → Ω → ℝ)
    (hB:∀z,B z=ᵐ[P] (W (brownianTimeDirection z):Ω → ℝ))
    (Y:Ω → C(Icc (0:ℝ) T,Fin (d+1) → ℝ)) (hYm:Measurable Y)
    (hY:∀w t i,Y w t i=B (i,t) w) (hYp:∀p:ℝ≥0∞,p≠⊤ → MemLp Y p P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W univ dense_univ (fun u _ => hW u) 2 (by simp))))
    (hd:DenseRange (fun f:D.domain => (f:Lp ℝ 2 P)))
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder (FiniteWienerHilbert d T) => c.valueLp P W univ dense_univ (fun u _ => hW u) q hq))
    (v:Fin (d+1) → EuclideanSpace ℝ (Fin (n+1))) (x:EuclideanSpace ℝ (Fin (n+1)))
    (b:EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (ell:ℝ) (hell:0<ell)
    (hv:∀z:EuclideanSpace ℝ (Fin (n+1)),ell*‖z‖^2≤∑j,(inner ℝ z (v j))^2) :
    ∃S:C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))) → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))),
      ContDiff ℝ ∞ S ∧ (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s))) ∧
      ∃p:EuclideanSpace ℝ (Fin (n+1)) → ℝ,ContDiff ℝ ∞ p ∧ (∀y,0≤p y) ∧
        P.map (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w)) ⟨T,hT.le,le_rfl⟩)=
          volume.withDensity (fun y => ENNReal.ofReal (p y)) := by
  let H := finiteWienerHilbertData d T
  let hc := fun u (_:u∈(univ:Set H)) => hW u
  obtain ⟨S,hS,hSeq,hSB⟩ := smooth_forcing_all_bounds b hb hbound T hT.le
  obtain ⟨K,hKb⟩ := hbound 1 le_rfl
  have hK:∀y,‖fderiv ℝ b y‖≤(K:ℝ) := by simpa only [norm_iteratedFDeriv_one] using hKb
  have hLip:LipschitzWith K b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hb.differentiable (by simp))
    intro y
    exact_mod_cast hK y
  obtain ⟨S',hS',hSeq',hAll⟩ := smooth_solution_all_sobolev P d T hT W hW B hB Y hYm hY hYp v x b hb hbound hdense
  have hSS:S'=S := forcing_solution_uniqueness b K hLip T hT.le S' S hSeq' hSeq
  subst S'
  let t:Icc (0:ℝ) T := ⟨T,hT.le,le_rfl⟩
  let a := fun w => ContinuousMap.const (Icc (0:ℝ) T) x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w)
  let R := hilbertKernelForcing (brownianKernelPath d T) v
  let pr : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ := fun i => PiLp.proj 2 (fun _ : Fin (n+1) => ℝ) i
  have hgraph i := brownian_closed_forcing_gradient P d T hT W hW B hB Y hYm hY (hYp 2 (by simp))
    v x b K hLip S hS hSeq hSB D hD hg (pr i) t
  choose F hU hFe hFU using hgraph
  let U := fun i => (hU i).toLp _
  have hUe i:(U i:Ω → H)=ᵐ[P] (fun w => forcingGradient S (a w) R (pr i) t) := (hU i).coeFn_toLp
  have hFa i:HasAllSobolevJets H P W univ dense_univ hc (F i) :=
    all_sobolev_congr H P W univ dense_univ hc _ _ (hAll (pr i) t) (hFe i).symm
  let c := ell*T*Real.exp (-2*(K:ℝ)*T)
  have hc0:0<c := mul_pos (mul_pos hell hT) (Real.exp_pos _)
  let G := fun w => derivativeGram (fun i => U i w)
  have hGb:∀ᵐw∂P,(G w).IsHermitian ∧ ∀z:Fin (n+1) → ℝ,
      c*(∑i,(z i)^2)≤∑i,z i*((G w).mulVec z) i := by
    filter_upwards [ae_all_iff.mpr hUe] with w hw
    refine ⟨derivativeGram_hermitian _,?_⟩
    intro z
    have hh := brownian_forcing_covariance b hb hbound T hT.le S hS hSeq (a w) v K hK ell hell.le hv z
    change c*(∑i,(z i)^2)≤∑i,z i*((derivativeGram (fun i => U i w)).mulVec z) i
    simp_rw [hw]
    exact hh
  have hGm:Measurable (fun w => (G w).det) := by
    apply continuous_id.matrix_det.measurable.comp
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact ((Lp.stronglyMeasurable (U i)).inner (𝕜:=ℝ) (Lp.stronglyMeasurable (U j))).measurable
  obtain ⟨hpos,hi⟩ := covariance_inverse_all_moments P G hGm c hc0 hGb
  obtain ⟨p,hp,hpp,hmap⟩ := malliavin_nondegenerate_smooth_density H P W univ dense_univ hc D hD hg hd hdense
    n F U hFa hFU hpos (fun p _ hp => hi p hp)
  refine ⟨S,hS,hSeq,p,hp,hpp,?_⟩
  have he:(fun w => WithLp.toLp 2 (fun i => F i w))=ᵐ[P] (fun w => S (a w) t) := by
    filter_upwards [ae_all_iff.mpr hFe] with w hw
    apply PiLp.ext
    intro i
    exact hw i
  exact (Measure.map_congr he).symm.trans hmap
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_elliptic_smooth_density
