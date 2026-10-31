import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! A stopping search for the growing clique level.
The function tests levels in order and stops at the first failure; it does not
evaluate the sequence at every index up to k. These are parameter correctness
lemmas. Evaluating K and accounting for bit operations are separate obligations.
-/

namespace CSPConsequence.LevelSelection

def search (K : ℕ → ℕ) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, l => l
  | fuel+1, l => if K (l+1)^32 ≤ k then search K k fuel (l+1) else l

theorem index_lower (K : ℕ → ℕ) (h0 : 2 ≤ K 0)
    (hstep : ∀ l, K l < K (l+1)) (l : ℕ) : l+2 ≤ K l := by
  induction l with
  | zero => simpa using h0
  | succ l ih => have := hstep l; omega

theorem search_spec (K : ℕ → ℕ) (k : ℕ) (h0 : 2 ≤ K 0)
    (hstep : ∀ l, K l < K (l+1)) (fuel l : ℕ)
    (hbudget : k ≤ fuel+l) (hvalid : K l^32 ≤ k) :
    K (search K k fuel l)^32 ≤ k ∧ k < K (search K k fuel l+1)^32 := by
  induction fuel generalizing l with
  | zero =>
    have hl := index_lower K h0 hstep l
    have hp : K l ≤ K l^32 := le_self_pow (by omega) (by decide)
    omega
  | succ fuel ih =>
    simp only [search]
    split_ifs with hn
    · exact ih (l+1) (by omega) hn
    · exact ⟨hvalid, Nat.lt_of_not_ge hn⟩

def select (K : ℕ → ℕ) (k : ℕ) : ℕ := search K k k 0

theorem selected_bounds (K : ℕ → ℕ) (k : ℕ) (h0 : 2 ≤ K 0)
    (hstep : ∀ l, K l < K (l+1)) (hgrow : ∀ l, K (l+1) ≤ K l^10)
    (hlarge : K 0^32 ≤ k) :
    K (select K k)^32 ≤ k ∧ k < K (select K k)^320 := by
  obtain ⟨h1,h2⟩ := search_spec K k h0 hstep k 0 (by omega) hlarge
  refine ⟨h1, h2.trans_le ?_⟩
  calc
    K (search K k k 0+1)^32 ≤ (K (search K k k 0)^10)^32 :=
      Nat.pow_le_pow_left (hgrow _) 32
    _ = K (select K k)^320 := by rw [← pow_mul]; rfl

theorem grouping_fits {K k : ℕ} (hK : 2 ≤ K) (hsize : K^32 ≤ k) :
    3*K^8 ≤ k := by
  have h24 : 3 ≤ K^24 := (by decide : 3 ≤ (2 : ℕ)^24).trans
    (Nat.pow_le_pow_left hK 24)
  calc
    3*K^8 ≤ K^24*K^8 := Nat.mul_le_mul_right _ h24
    _ = K^32 := by rw [← pow_add]
    _ ≤ k := hsize

#print axioms search_spec
#print axioms selected_bounds
#print axioms grouping_fits

end CSPConsequence.LevelSelection
