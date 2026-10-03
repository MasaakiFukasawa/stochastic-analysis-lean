import Chapter12PolygonalConstruction

open Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def polygonalGridOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (n : ℕ) (t : ℝ) : (Fin (n+1) → E) →L[ℝ] E :=
  (ContinuousLinearMap.proj 0 : (Fin (n+1) → E) →L[ℝ] E)+∑ k∈Finset.range n,
    ((min (((k:ℝ)+1)*h) t-min ((k:ℝ)*h) t)/h) •
      ((ContinuousLinearMap.proj (Fin.ofNat (n+1) (k+1)) : (Fin (n+1) → E) →L[ℝ] E)-
        ContinuousLinearMap.proj (Fin.ofNat (n+1) k))

theorem polygonalGridOperator_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (n : ℕ) : Continuous (polygonalGridOperator (E := E) h n) := by
  unfold polygonalGridOperator
  fun_prop

/-- The finite-sum path is exactly a linear function of its grid values.
This identifies the finite-dimensional parameters used in the ODE proof. -/
theorem polygonalGridOperator_samples {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ℝ) (n : ℕ) (t : ℝ) :
    polygonalGridOperator h n t (fun i => f ((i:ℝ)*h))=polygonalPath f h n t := by
  simp only [polygonalGridOperator,polygonalPath,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.proj_apply,Fin.val_zero,Nat.cast_zero,zero_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k<n+1 := (Finset.mem_range.mp hk).trans (Nat.lt_succ_self n)
  have hk1 : k+1<n+1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
  simp only [Fin.ofNat_eq_cast,Fin.coe_natCast_eq_mod,Nat.mod_eq_of_lt hk0,Nat.mod_eq_of_lt hk1,Nat.cast_add,Nat.cast_one]

end Asakura.Chapter12
