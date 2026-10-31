import Downstream.InverseLevels
import ToTuring.Lib.List1b
import Mathlib.Data.List.Range

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A polynomial-time level selector on the unary variable count. Every call
to the level computer has a unary cutoff k, and the loop has only k iterations.
It never evaluates the unbounded rapidly growing sequence directly. -/

namespace CSPConsequence.BoundedSelection

open Groundwork Printed
abbrev U := List Unit

variable (kf : U × U → Option U)

def test (p : U × ℕ) : Bool :=
  ((kf (List.replicate (min p.2 p.1.length) (),p.1)).map
    (fun v => decide (v.length^32 ≤ p.1.length))).getD false

@[fun_prop] theorem test_polyT (hKF : PolyT kf) : PolyT (test kf) := by
  have hcap : Unary (fun p : U × ℕ => min p.2 p.1.length) :=
    Unary.of_le (g := fun p : U × ℕ => p.1.length)
      (Unary.of_length (by fun_prop)) (by fun_prop) (fun _ => Nat.min_le_right _ _)
  have hc : PolyT (fun p : U × ℕ => kf (List.replicate (min p.2 p.1.length) (),p.1)) :=
    hKF.comp (PolyT.prodMk hcap (by fun_prop))
  unfold test
  exact PolyT.optionGetD (PolyT.optionMap (by fun_prop) hc) (by fun_prop)

def validLevels (u : U) : List ℕ :=
  (List.range u.length).filter (fun j => test kf (u,j))

@[fun_prop] theorem validLevels_polyT (hKF : PolyT kf) : PolyT (validLevels kf) := by
  have ht := test_polyT kf hKF
  have hr : PolyT (fun u : U => List.range u.length) :=
    PolyT.range (Unary.of_length (by fun_prop))
  unfold validLevels
  fun_prop (disch := assumption)

def index (u : U) : ℕ := (validLevels kf u).getLast?.getD 0

@[fun_prop] theorem index_polyT (hKF : PolyT kf) : PolyT (index kf) := by
  have hv := validLevels_polyT kf hKF
  unfold index
  fun_prop (disch := assumption)

def sizeWord (u : U) : U :=
  (kf (List.replicate (min (index kf u) u.length) (),u)).getD []

@[fun_prop] theorem sizeWord_polyT (hKF : PolyT kf) : PolyT (sizeWord kf) := by
  have hi := index_polyT kf hKF
  have hu : Unary (fun u : U => min (index kf u) u.length) :=
    Unary.of_le (g := fun u : U => u.length)
      (Unary.of_length (by fun_prop)) (by fun_prop (disch := assumption))
      (fun _ => Nat.min_le_right _ _)
  have hc : PolyT (fun u : U => kf (List.replicate (min (index kf u) u.length) (),u)) :=
    hKF.comp (PolyT.prodMk hu (by fun_prop))
  unfold sizeWord
  exact PolyT.optionGetD hc (by fun_prop)

theorem test_of {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (k j : ℕ) (hj : j ≤ k) (hK : 1 ≤ K j) :
    test kf (unary k,j) = true ↔ K j^32 ≤ k := by
  have hlen : (unary k).length = k := by simp [unary]
  simp only [test,hlen,Nat.min_eq_left hj]
  change ((kf (unary j,unary k)).map (fun v => decide (v.length^32 ≤ k))).getD false = true ↔ _
  rw [hC.2]
  by_cases h : K j ≤ k
  · simp [h,unary]
  · have hp : ¬K j^32 ≤ k := fun hh => h ((le_self_pow hK (by decide)).trans hh)
    simp [h,hp]

theorem filter_range_le (n m : ℕ) :
    (List.range n).filter (fun j => decide (j ≤ m)) = List.range (min n (m+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filter_append,ih]
    by_cases h : n ≤ m
    · have hn : n ≤ m+1 := by omega
      have hn' : n+1 ≤ m+1 := by omega
      simp [h,Nat.min_eq_left hn,Nat.min_eq_left hn',List.range_succ]
    · have hn : m+1 ≤ n := by omega
      have hn' : m+1 ≤ n+1 := by omega
      simp [h,Nat.min_eq_right hn,Nat.min_eq_right hn']

theorem validLevels_of {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (h0 : 2 ≤ K 0) (hstep : ∀ l, K l < K (l+1))
    (k : ℕ) (hlarge : K 0^32 ≤ k) :
    validLevels kf (unary k) = List.range (LevelSelection.select K k+1) := by
  let l := LevelSelection.select K k
  obtain ⟨hl,hnext⟩ := LevelSelection.search_spec K k h0 hstep k 0 (by omega) hlarge
  change K l^32 ≤ k at hl
  change k < K (l+1)^32 at hnext
  have hm : StrictMono K := strictMono_nat_of_lt_succ hstep
  have hlow := LevelSelection.index_lower K h0 hstep l
  have hKlow : 1 ≤ K l := by omega
  have hlk : l+1 ≤ k := by
    have hp : K l ≤ K l^32 := le_self_pow hKlow (by decide)
    omega
  have he : (List.range k).filter (fun j => test kf (unary k,j)) =
      (List.range k).filter (fun j => decide (j ≤ l)) := by
    apply List.filter_congr
    intro j hj
    have hjk : j < k := List.mem_range.mp hj
    have hjK : 1 ≤ K j := by have := LevelSelection.index_lower K h0 hstep j; omega
    apply Bool.eq_iff_iff.mpr
    rw [test_of kf hC k j hjk.le hjK, decide_eq_true_eq]
    constructor
    · intro hjpow
      by_contra hjl
      have hjl' : l+1 ≤ j := by omega
      have hp := Nat.pow_le_pow_left (hm.monotone hjl') 32
      omega
    · intro hjl
      exact (Nat.pow_le_pow_left (hm.monotone hjl) 32).trans hl
  unfold validLevels
  have hlen : (unary k).length = k := by simp [unary]
  rw [hlen,he,filter_range_le,Nat.min_eq_right hlk]

theorem index_correct {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (h0 : 2 ≤ K 0) (hstep : ∀ l, K l < K (l+1))
    (k : ℕ) (hlarge : K 0^32 ≤ k) :
    index kf (unary k) = LevelSelection.select K k := by
  unfold index
  rw [validLevels_of kf hC h0 hstep k hlarge]
  simp [List.range_succ]

theorem sizeWord_correct {K : ℕ → ℕ} (hC : CliqueLevels.ComputesLevels K kf)
    (h0 : 2 ≤ K 0) (hstep : ∀ l, K l < K (l+1))
    (k : ℕ) (hlarge : K 0^32 ≤ k) :
    sizeWord kf (unary k) = unary (K (LevelSelection.select K k)) := by
  let l := LevelSelection.select K k
  have hl := (LevelSelection.search_spec K k h0 hstep k 0 (by omega) hlarge).1
  change K l^32 ≤ k at hl
  have hlo := LevelSelection.index_lower K h0 hstep l
  have hk : K l ≤ k := (le_self_pow (by omega : 1 ≤ K l) (by decide : 32 ≠ 0)).trans hl
  have hli : l ≤ k := by omega
  unfold sizeWord
  rw [index_correct kf hC h0 hstep k hlarge]
  have hlen : (unary k).length = k := by simp [unary]
  rw [hlen,Nat.min_eq_left hli]
  change (kf (unary l,unary k)).getD [] = _
  rw [hC.2]
  simp [hk,l]

#print axioms index_polyT
#print axioms index_correct
#print axioms sizeWord_polyT
#print axioms sizeWord_correct

end CSPConsequence.BoundedSelection
