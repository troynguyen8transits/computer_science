import Downstream.ProviderTables

set_option autoImplicit false

/-! Uniform state-size bounds for the actual provider queries. These bound
encoded context, indices, strings and answers, rather than cardinalities of
sets of assignments. Native step-time certificates are supplied separately.
-/

namespace CSPConsequence.QuerySizes

open Groundwork Finset

theorem word_size (w : List Bool) : size w = 2*w.length+1 := by
  simp [size_list, List.map_const, List.sum_replicate, mul_comm]

theorem index_size {g : ℕ} (a : Fin g) : size a.val ≤ g+1 := by
  rw [size_nat]
  have h : Nat.size a.val ≤ a.val := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem integer_size {B : ℕ} (z : ℤ) (hz : |z| < 2^B) : size z ≤ B+1 := by
  rw [size_int]
  apply Nat.add_le_add_right
  apply Nat.size_le.mpr
  have h : (z.natAbs : ℤ) < 2^B := by simpa only [Int.natCast_natAbs] using hz
  exact_mod_cast h

theorem capacity_le {g P B : ℕ} (N : Eight.SecNetworks.Net g) (hN : N.Is P B)
    (a v : Fin g) (hne : a ≠ v) : N.c a v ≤ P := by
  have hm : v ∈ (univ.erase a : Finset (Fin g)) := by simp [hne.symm]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm).trans (hN.i a)

def room {C : Type} [HasSize C] (c : C) (g P B : ℕ) : ℕ :=
  size c + 2*g + 4*P + B + 12

variable {C : Type} [HasSize C] {g P B : ℕ}

theorem mem_room (c : C) (a : Fin g) (w : List Bool) (hw : w.length ≤ P) (z : Bool) :
    max (size (c,a.val,w)) (size z)+1 ≤ room c g P B := by
  have hi := index_size a
  have hs := word_size w
  simp only [room, size_prod, size_bool]
  omega

theorem one_room (c : C) (a : Fin g) (w : List Bool) (hw : w.length ≤ P)
    (z : ℤ) (hz : |z| < 2^B) :
    max (size (c,a.val,w)) (size z)+1 ≤ room c g P B := by
  have hi := index_size a
  have hs := word_size w
  have ho := integer_size z hz
  simp only [room, size_prod]
  omega

theorem two_room (c : C) (a v : Fin g) (w w' : List Bool)
    (hw : w.length ≤ P) (hw' : w'.length ≤ P) (z : ℤ) (hz : |z| < 2^B) :
    max (size (c,(a.val,v.val),(w,w'))) (size z)+1 ≤ room c g P B := by
  have hi := index_size a
  have hi' := index_size v
  have hs := word_size w
  have hs' := word_size w'
  have ho := integer_size z hz
  simp only [room, size_prod]
  omega

#print axioms capacity_le
#print axioms one_room
#print axioms two_room

end CSPConsequence.QuerySizes
