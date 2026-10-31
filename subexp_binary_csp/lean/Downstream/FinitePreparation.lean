import Downstream.BoundedSelection
import Downstream.CounterExistence

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The grouping count, domain bit width and clique size are computed from the
finite CSP input, rather than supplied as uncharged advice. Correctness here
covers the large-k branch; a small-input fallback is supplied separately. -/

namespace CSPConsequence.FinitePreparation

open Groundwork Printed FiniteInput NodeRefinement

theorem unary_pow {α : Type} [Enc α] (f : α → ℕ) (hf : Unary f) (n : ℕ) :
    Unary (fun x => f x^n) := by
  induction n with
  | zero => simpa using (Unary.const 1 : Unary (fun _ : α => 1))
  | succ n ih => simpa only [pow_succ] using Unary.mul ih hf

def bitWidth (input : Input) : ℕ := Nat.size (domain input)

theorem bitWidth_unary : Unary bitWidth := by
  have hd : Unary domain := Unary.of_length (by fun_prop)
  exact Unary.of_le hd (by unfold bitWidth domain; fun_prop)
    (fun input => Nat.size_le.mpr Nat.lt_two_pow_self)

def prepare (kf : List Unit × List Unit → Option (List Unit))
    (input : Input) : DynamicPreparation.PreparedInput :=
  let w := BoundedSelection.sizeWord kf input.1
  ((input,unary (3*w.length^8),unary (bitWidth input)),w)

theorem prepare_polyT (kf : List Unit × List Unit → Option (List Unit))
    (hKF : PolyT kf) : PolyT (prepare kf) := by
  have hw : PolyT (fun input : Input => BoundedSelection.sizeWord kf input.1) :=
    (BoundedSelection.sizeWord_polyT kf hKF).comp (by fun_prop)
  have hkw : Unary (fun input : Input => (BoundedSelection.sizeWord kf input.1).length) :=
    Unary.of_length hw
  have hg := Unary.mul (Unary.const 3) (unary_pow _ hkw 8)
  have hb := bitWidth_unary
  unfold prepare unary
  exact PolyT.prodMk (PolyT.prodMk (by fun_prop) (PolyT.prodMk hg hb)) hw

theorem prepare_of {K : ℕ → ℕ} (kf : List Unit × List Unit → Option (List Unit))
    (hC : CliqueLevels.ComputesLevels K kf) (h0 : 2 ≤ K 0)
    (hstep : ∀ l, K l < K (l+1)) {k D : ℕ} (I : Instance k D)
    (hlarge : K 0^32 ≤ k) :
    prepare kf (tabulate I) =
      (paramsOf I (3*(K (LevelSelection.select K k))^8) (Nat.size D),
        unary (K (LevelSelection.select K k))) := by
  have hw : BoundedSelection.sizeWord kf (tabulate I).1 =
      unary (K (LevelSelection.select K k)) :=
    BoundedSelection.sizeWord_correct kf hC h0 hstep k hlarge
  unfold prepare
  rw [hw]
  simp [paramsOf,bitWidth,domain_tabulate,unary]

theorem bitWidth_capacity {D : ℕ} : D ≤ 2^(Nat.size D) := (Nat.lt_size_self _).le

theorem bitWidth_pos {D : ℕ} (hD : 0 < D) : 1 ≤ Nat.size D := Nat.size_pos.mpr hD

#print axioms bitWidth_unary
#print axioms prepare_polyT
#print axioms prepare_of

end CSPConsequence.FinitePreparation
