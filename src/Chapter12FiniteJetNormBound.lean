import Chapter12VectorSobolevJetCore

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Coordinate Sobolev estimates give a bounded map between finite jets;
the constant depends on the derivative order and exponent, not dimension. -/
theorem finite_jet_norm_bound {k m : ℕ}
    (E : Fin (k+m+1) → Type*) (F : Fin (k+1) → Type*)
    [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedAddCommGroup (F i)]
    (x : PiLp 1 E) (y : PiLp 1 F) (C : ℝ) (hC : 0≤C)
    (h0 : ‖y 0‖≤C*∑ j : Fin (m+1),‖x ⟨j.val,by omega⟩‖)
    (hs : ∀ r : Fin k,‖y r.succ‖≤
      (r.val+1:ℕ)*‖x ⟨r.val,by omega⟩‖+
      C*∑ j : Fin (m+1),‖x ⟨j.val+(r.val+1),by omega⟩‖) :
    ‖y‖≤(k+1:ℕ)*((k:ℝ)+C*(m+1:ℕ))*‖x‖ := by
  classical
  have hsum (a : Fin (m+1) → Fin (k+m+1)) :
      (∑ j : Fin (m+1),‖x (a j)‖)≤(m+1:ℕ)*‖x‖ := by
    calc
      _≤∑ _j : Fin (m+1),‖x‖ := Finset.sum_le_sum (fun j _ => PiLp.norm_apply_le x (a j))
      _=_ := by simp
  have hcoord (i : Fin (k+1)) : ‖y i‖≤((k:ℝ)+C*(m+1:ℕ))*‖x‖ := by
    refine Fin.cases ?_ (fun r => ?_) i
    · have hh := h0.trans (mul_le_mul_of_nonneg_left (hsum (fun j => ⟨j.val,by omega⟩)) hC)
      nlinarith [norm_nonneg x,show (0:ℝ)≤k by positivity]
    · have hfirst : (r.val+1:ℕ)*‖x ⟨r.val,by omega⟩‖≤(k:ℝ)*‖x‖ :=
        mul_le_mul (by exact_mod_cast (show r.val+1≤k by omega))
          (PiLp.norm_apply_le x ⟨r.val,by omega⟩) (norm_nonneg _) (by positivity)
      have hsecond := mul_le_mul_of_nonneg_left
        (hsum (fun j => ⟨j.val+(r.val+1),by omega⟩)) hC
      have hh := (hs r).trans (add_le_add hfirst hsecond)
      nlinarith
  rw [PiLp.norm_eq_of_L1]
  calc
    _≤∑ _i : Fin (k+1),((k:ℝ)+C*(m+1:ℕ))*‖x‖ := Finset.sum_le_sum (fun i _ => hcoord i)
    _=_ := by simp [mul_assoc]

end Asakura.Chapter12
