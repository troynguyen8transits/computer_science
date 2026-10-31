import Downstream.ProviderMetadata
import Downstream.LevelSelection
import CliqueLevelsStatement

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! One polynomial-time adapter from clique size K_l back to level l. It uses
the bounded level computer, so native simulation constants are uniform in l. -/

namespace CSPConsequence.InverseLevels

open Groundwork Printed
abbrev U := List Unit
variable (kf : U × U → Option U)

def test (p : U × ℕ) : Bool :=
  decide (kf (List.replicate (min p.2 p.1.length) (),p.1) = some p.1)

@[fun_prop] theorem test_polyT (hKF : PolyT kf) : PolyT (test kf) := by
  have hcap : Unary (fun p : U × ℕ => min p.2 p.1.length) :=
    Unary.of_le (g := fun p : U × ℕ => p.1.length)
      (Unary.of_length (by fun_prop)) (by fun_prop) (fun p => Nat.min_le_right _ _)
  have hcall : PolyT (fun p : U × ℕ => kf (List.replicate (min p.2 p.1.length) (),p.1)) :=
    hKF.comp (PolyT.prodMk hcap (by fun_prop))
  exact PolyT.decide_eq hcall (by fun_prop)

def search (u : U) : Option ℕ := (List.range u.length).find? (fun l => test kf (u,l))

@[fun_prop] theorem search_polyT (hKF : PolyT kf) : PolyT (search kf) := by
  unfold search
  exact PolyT.find? (test_polyT kf hKF) (PolyT.range (Unary.of_length (by fun_prop)))

def index (u : U) : ℕ := (search kf u).getD 0

@[fun_prop] theorem index_polyT (hKF : PolyT kf) : PolyT (index kf) := by
  unfold index
  have h := search_polyT kf hKF
  fun_prop (disch := assumption)

def inverse (u : U) : U := List.replicate (min (index kf u) u.length) ()

@[fun_prop] theorem inverse_polyT (hKF : PolyT kf) : PolyT (inverse kf) := by
  have hi := index_polyT kf hKF
  exact Unary.of_le (g := fun u : U => u.length)
    (Unary.of_length (by fun_prop)) (by fun_prop (disch := assumption))
    (fun u => Nat.min_le_right _ _)

theorem test_of {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (l j : ℕ) (hj : j ≤ K l) : test kf (unary (K l),j) = true ↔ K j = K l := by
  have hlen : (unary (K l)).length = K l := by simp [unary]
  simp only [test, hlen]
  rw [Nat.min_eq_left hj]
  change decide (kf (unary j,unary (K l)) = some (unary (K l))) = true ↔ _
  rw [hC.2]
  simp only [decide_eq_true_eq]
  by_cases h : K j ≤ K l
  · simp only [if_pos h, Option.some.injEq]
    constructor
    · intro heq
      have he := congrArg List.length heq
      simpa [unary] using he
    · intro heq
      rw [heq]
  · have hn : K j ≠ K l := fun heq => h heq.le
    simp [if_neg h, hn]

theorem index_correct {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (h0 : 2 ≤ K 0) (hstep : ∀ l, K l < K (l+1)) (l : ℕ) :
    index kf (unary (K l)) = l := by
  have hlow := LevelSelection.index_lower K h0 hstep l
  have hl : l < K l := by omega
  have hmono : StrictMono K := strictMono_nat_of_lt_succ hstep
  cases hs : search kf (unary (K l)) with
  | none =>
    have hf : (List.range (K l)).find? (fun j => test kf (unary (K l),j)) = none := by
      simpa [search, unary] using hs
    have hb := List.find?_eq_none.mp hf l (by simp [hl])
    have ht := (test_of kf hC l l hl.le).mpr rfl
    simp [ht] at hb
  | some j =>
    have hf : (List.range (K l)).find? (fun j => test kf (unary (K l),j)) = some j := by
      simpa [search, unary] using hs
    have hj : j < K l := by simpa using List.mem_of_find?_eq_some hf
    have ht : test kf (unary (K l),j) = true :=
      List.find?_some (p := fun j : ℕ => test kf (unary (K l),j)) hf
    have he := (test_of kf hC l j hj.le).mp ht
    have hji : j = l := hmono.injective he
    simp [index, hs, hji]

theorem inverse_correct {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (h0 : 2 ≤ K 0) (hstep : ∀ l, K l < K (l+1)) (l : ℕ) :
    inverse kf (unary (K l)) = unary l := by
  have hlow := LevelSelection.index_lower K h0 hstep l
  unfold inverse
  rw [index_correct kf hC h0 hstep l]
  simp [unary, Nat.min_eq_left (by omega : l ≤ K l)]

#print axioms inverse_polyT
#print axioms inverse_correct

end CSPConsequence.InverseLevels
