import Chapter12HigherChainPartitions
import Mathlib.Order.Preorder.Finite

open Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def oneBlockPartition (n : ℕ) : OrderedFinpartition (n+1) where
  length := 1
  partSize _ := n+1
  partSize_pos _ := Nat.zero_lt_succ n
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro i _ j _ hij
    exact False.elim (hij (Subsingleton.elim i j))
  cover x := ⟨0,x,rfl⟩

theorem partition_length_one {n : ℕ} (c : OrderedFinpartition (n+1))
    (hc : c.length=1) : c=oneBlockPartition n := by
  have hsum : (∑ m,c.partSize m)=n+1 := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr c.equivSigma
  rcases c with ⟨length,partSize,hpos,emb,hmono,hparts,hdisj,hcover⟩
  dsimp only at hc hsum
  subst length
  have hsize : partSize=(fun _ => n+1) := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi,Fin.sum_univ_one] using hsum
  subst partSize
  have hem : emb=(fun _ => id) := by
    funext i
    exact (hmono i).eq_id
  subst emb
  rfl

theorem partition_ne_oneBlock {n : ℕ} (c : OrderedFinpartition (n+1)) :
    c≠oneBlockPartition n ↔ 2≤c.length := by
  have hp := c.length_pos (Nat.zero_lt_succ n)
  constructor
  · intro h
    by_contra hn
    have he : c.length=1 := by omega
    exact h (partition_length_one c he)
  · intro h he
    rw [he] at h
    change 2≤1 at h
    omega

end Asakura.Chapter12
