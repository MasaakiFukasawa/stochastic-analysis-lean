import Chapter5RevisedBurgersExample
import Chapter5SmoothExtension

open Set
open scoped Topology ContDiff
namespace Asakura.Chapter5
set_option maxHeartbeats 5000000

lemma fin2_space_slice_derivative (t x : ℝ) :
    HasDerivAt (fun y : ℝ => (![t,y] : Fin 2 → ℝ)) (Pi.single 1 1) x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i <;> simp <;> first | exact hasDerivAt_const _ _ | exact hasDerivAt_id _

lemma fin2_time_slice_derivative (t x : ℝ) :
    HasDerivAt (fun r : ℝ => (![r,x] : Fin 2 → ℝ)) (Pi.single 0 1) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i <;> simp <;> first | exact hasDerivAt_const _ _ | exact hasDerivAt_id _

lemma fin2_space_derivative (v : (Fin 2 → ℝ) → ℝ) (t x : ℝ)
    (hv : DifferentiableAt ℝ v ![t,x]) :
    fderiv ℝ v ![t,x] (Pi.single 1 1)=deriv (fun y => v ![t,y]) x :=
  ((hv.hasFDerivAt.comp_hasDerivAt x (fin2_space_slice_derivative t x)).deriv).symm

lemma fin2_space_second_derivative (v : (Fin 2 → ℝ) → ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (hv : ContDiffOn ℝ 2 v O) (t x : ℝ) (ht : ∀ y,(![t,y] : Fin 2 → ℝ)∈O) :
    fderiv ℝ (fderiv ℝ v) ![t,x] (Pi.single 1 1) (Pi.single 1 1)=
      deriv (fun y => deriv (fun z => v ![t,z]) y) x := by
  have hd y : DifferentiableAt ℝ v ![t,y] :=
    (hv.contDiffAt (hO.mem_nhds (ht y))).differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ v) ![t,x] :=
    ((hv.fderiv_of_isOpen hO (by norm_num : (1:ℕ∞ω)+1≤2)).contDiffAt
      (hO.mem_nhds (ht x))).differentiableAt (by norm_num)
  have hG := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single 1 (1:ℝ)) (![t,x] : Fin 2 → ℝ))
  have he := (hG.comp_hasDerivAt x (fin2_space_slice_derivative t x)).deriv
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,
    map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply,Function.comp_def] at he
  rw [show (fun y => deriv (fun z => v ![t,z]) y)=
    (fun y => fderiv ℝ v ![t,y] (Pi.single 1 1)) from funext (fun y => (fin2_space_derivative v t y (hd y)).symm)]
  exact he.symm

/-- Time reversal converts the proved forward PDE, including its boundary,
into precisely the Frechet-derivative input of the chapter's Feynman--Kac theorem. -/
theorem time_reverse_forward_PDE (u : ℝ × ℝ → ℝ) (O : Set (ℝ × ℝ))
    (hO : IsOpen O) (hstrip : {p : ℝ × ℝ | 0≤p.1} ⊆ O) (hu : ContDiffOn ℝ 2 u O)
    (b : ℝ → ℝ → ℝ)
    (hpde : ∀ t x,0≤t → deriv (fun r => u (r,x)) t=
      deriv (fun y => deriv (fun z => u (t,z)) y) x/2+b (u (t,x)) (deriv (fun y => u (t,y)) x))
    (R : ℝ) (hR : 0≤R) :
    let v := fun p : Fin 2 → ℝ => u (R-p 0,p 1)
    let U := {p : Fin 2 → ℝ | (R-p 0,p 1)∈O}
    IsOpen U ∧ {p : Fin 2 → ℝ | p 0∈Icc 0 R} ⊆ U ∧ ContDiffOn ℝ 2 v U ∧
      (∀ x,v ![R,x]=u (0,x)) ∧
      (∀ t∈Icc 0 R,∀ x,
        fderiv ℝ v ![t,x] (Pi.single 0 1)+
        fderiv ℝ (fderiv ℝ v) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2+
        b (v ![t,x]) (fderiv ℝ v ![t,x] (Pi.single 1 1))=0) := by
  dsimp only
  let v := fun p : Fin 2 → ℝ => u (R-p 0,p 1)
  let U := {p : Fin 2 → ℝ | (R-p 0,p 1)∈O}
  have hU : IsOpen U := hO.preimage (by fun_prop)
  have hv : ContDiffOn ℝ 2 v U := hu.comp (by fun_prop) (fun p hp => hp)
  have hs : {p : Fin 2 → ℝ | p 0∈Icc 0 R} ⊆ U :=
    fun p hp => hstrip (sub_nonneg.mpr hp.2)
  refine ⟨hU,hs,hv,?_,?_⟩
  · intro x; simp [v]
  · intro t ht x
    have htx : (![t,x] : Fin 2 → ℝ)∈U := hs (by simpa using ht)
    have hvd : DifferentiableAt ℝ v ![t,x] :=
      (hv.contDiffAt (hU.mem_nhds htx)).differentiableAt (by norm_num)
    have huD : DifferentiableAt ℝ u (R-t,x) :=
      (hu.contDiffAt (hO.mem_nhds (hstrip (sub_nonneg.mpr ht.2)))).differentiableAt (by norm_num)
    have hut := huD.hasFDerivAt.comp_hasDerivAt (R-t)
      ((hasDerivAt_id (R-t)).prodMk (hasDerivAt_const (R-t) x))
    have hrev := hut.comp t ((hasDerivAt_id t).const_sub R)
    have hvt := hvd.hasFDerivAt.comp_hasDerivAt t (fin2_time_slice_derivative t x)
    have het : fderiv ℝ v ![t,x] (Pi.single 0 1)= -deriv (fun r => u (r,x)) (R-t) := by
      simp only [Function.comp_def,id_eq] at hut
      rw [hut.deriv]
      have he := hvt.unique hrev
      simpa only [mul_neg_one] using he
    rw [het,fin2_space_derivative v t x hvd,fin2_space_second_derivative v U hU hv t x
      (fun y => hs (by simpa using ht))]
    have hp := hpde (R-t) x (sub_nonneg.mpr ht.2)
    dsimp only [v,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
    linarith

end Asakura.Chapter5
