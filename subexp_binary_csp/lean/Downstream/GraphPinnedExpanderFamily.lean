import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Convert

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Source port of the pinned OpenAI/math expander and weighted-tree proofs,
commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, Apache-2.0.
Every original source block retains its attribution below. The old root Mathlib
import is replaced by selected imports. TreewidthL1.Model contributes only its
HasTreeDecomposition definition; unrelated metric/L1 declarations are omitted.
See GraphPortManifest.json for exact copied source ranges and hashes.
Verification status belongs to GraphPortManifest.json; preparation alone is
not evidence of a successful Lean 4.33.1 check. -/

/- Source: OAI.Combinatorics.IndependentSets.PCP.ConstraintGraph; pinned OAI proof, Apache-2.0. -/
section PinnedSource0

namespace OAI

namespace IndependentSetsGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

theorem rejectionCount_le [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) : G.rejectionCount labeling ≤ Fintype.card E := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rejected_exists_of_not_satisfiable (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    ∃ e, G.edgeSatisfied labeling e = false := by
  classical
  by_contra none
  apply unsat
  refine ⟨labeling, fun e => ?_⟩
  have notFalse : G.edgeSatisfied labeling e ≠ false := by
    intro h
    exact none ⟨e, h⟩
  cases h : G.edgeSatisfied labeling e <;> simp_all

theorem rejectionCount_positive [Fintype E] (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    1 ≤ G.rejectionCount labeling := by
  obtain ⟨e, he⟩ := G.rejected_exists_of_not_satisfiable unsat labeling
  exact Finset.one_le_card.mpr ⟨e, (G.mem_rejectedDarts labeling e).mpr he⟩

end ConstraintGraph

end IndependentSetsGames.Foundations.PCP

end OAI


end PinnedSource0


/- Source: OAI.Combinatorics.IndependentSets.Expansion.PoweringWalks; pinned OAI proof, Apache-2.0. -/
section PinnedSource1

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

def permutePorts {t : Nat} (σ : Fin t ≃ Fin t) : Walk V D t ≃ Walk V D t where
  toFun w := (w.1, fun j => w.2 (σ j))
  invFun w := (w.1, fun j => w.2 (σ.symm j))
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.apply_symm_apply j)
  right_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.symm_apply_apply j)

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

theorem natCard_walk [Finite V] [Finite D] (n : Nat) :
    Nat.card (Walk V D n) = Nat.card V * Nat.card D ^ n := by
  simp [Walk, Nat.card_prod, Nat.card_fun]

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

theorem pivotEquiv_zero_apply (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    pivotEquiv G n 0 w = ((w.1, w.2 0), fun j => w.2 j.succ) := by
  cases n <;> rfl

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def projectedFiberEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (a : E) : {x // f x = a} ≃ R where
  toFun x := (e x.val).2
  invFun r := ⟨e.symm (a, r), by
    exact (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (a, r)))⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext ((he x.val).trans x.property).symm rfl
  right_inv r := congrArg Prod.snd (e.apply_symm_apply (a, r))

def projectedEventEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (P : E → Prop) :
    {x // P (f x)} ≃ ({a // P a} × R) where
  toFun x := (⟨(e x.val).1, by rw [he]; exact x.property⟩, (e x.val).2)
  invFun ar := ⟨e.symm (ar.1.val, ar.2), by
    have h : f (e.symm (ar.1.val, ar.2)) = ar.1.val :=
      (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2)))
    simpa only [h] using ar.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv ar := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2))
    · change (e (e.symm (ar.1.val, ar.2))).2 = ar.2
      exact congrArg Prod.snd (e.apply_symm_apply (ar.1.val, ar.2))

theorem natCard_edgeAt_fiber (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (a : Edge V D) :
    Nat.card {w : Walk V D (n + 1) // edgeAt G n w k = a} = Nat.card D ^ n := by
  calc
    _ = Nat.card (Fin n → D) := Nat.card_congr
      (projectedFiberEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) a)
    _ = _ := by simp [Nat.card_fun]

theorem natCard_edgeAt_event (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (P : Edge V D → Prop) :
    Nat.card {w : Walk V D (n + 1) // P (edgeAt G n w k)} =
      Nat.card {a : Edge V D // P a} * Nat.card D ^ n := by
  calc
    _ = Nat.card ({a : Edge V D // P a} × (Fin n → D)) := Nat.card_congr
      (projectedEventEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) P)
    _ = _ := by simp [Nat.card_prod, Nat.card_fun]

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_zero (G : PortGraph V D) (n : Nat)
    (v : V) (r : Fin n → D) : leftFromPivot G n 0 v r = v := by
  cases n <;> rfl

theorem rightFromPivot_zero (G : PortGraph V D) (n : Nat)
    (e : Edge V D) (r : Fin n → D) :
    rightFromPivot G n 0 e r = wordEnd G n (next G e.1 e.2) r := by
  cases n <;> rfl

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end IndependentSetsGames.Foundations.PCP.PoweringWalks

end OAI


end PinnedSource1


/- Source: OAI.Combinatorics.IndependentSets.Expansion.DegreeReplacement; pinned OAI proof, Apache-2.0. -/
section PinnedSource2

namespace OAI

open scoped BigOperators

namespace IndependentSetsGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem replacement_satisfiable [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (h : G.Satisfiable) : (replacementGraph G H).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact ⟨liftLabel G labeling, replacement_complete G H labeling hlabeling⟩

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem replacement_rejectionCount [Fintype E] [Fintype D] [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) :
    (replacementGraph G H).rejectionCount (liftLabel G labeling) =
      G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [replacement_satisfied_inl, replacement_satisfied_inr,
    Bool.true_eq_false, ite_false, Fintype.sum_unique, Finset.sum_const_zero, zero_add]
  rfl

abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

theorem padded_satisfiable (G : ConstraintGraph V E A) (dummy : V → Type*)
    (h : G.Satisfiable) : (paddedGraph G dummy).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact ⟨labeling, padded_complete G dummy labeling hlabeling⟩

theorem card_paddedDart [Fintype V] [Fintype E] (G : ConstraintGraph V E A)
    (dummy : V → Type*) [∀ v, Fintype (dummy v)] :
    Fintype.card (PaddedDart G dummy) =
      Fintype.card E + ∑ v, Fintype.card (dummy v) := by
  rw [Fintype.card_sum, Fintype.card_sigma]

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type]
  simp only [padded_satisfied_inl, padded_satisfied_inr,
    Bool.true_eq_false, ite_false, Finset.sum_const_zero, add_zero]
  rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

theorem paddedReplacement_rejectionCount
    [Fintype V] [Fintype E] [Fintype D] [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) (labeling : V → A) :
    (paddedReplacementGraph G dummy H).rejectionCount
        (liftLabel (paddedGraph G dummy) labeling) = G.rejectionCount labeling :=
  (replacement_rejectionCount (paddedGraph G dummy) H labeling).trans
    (padded_rejectionCount G dummy labeling)

def noDummyEquiv (G : ConstraintGraph V E A) :
    PaddedDart G (fun _ : V => Empty) ≃ E where
  toFun z := match z with
    | Sum.inl e => e
    | Sum.inr z => Empty.elim z.2
  invFun := Sum.inl
  left_inv := by
    intro z
    cases z with
    | inl e => rfl
    | inr z => exact Empty.elim z.2
  right_inv _ := rfl

end IndependentSetsGames.Foundations.PCP.DegreeReplacement

end OAI


end PinnedSource2


/- Source: OAI.Combinatorics.IndependentSets.Fourier.Walsh; pinned OAI proof, Apache-2.0. -/
section PinnedSource3

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def support (s : Cube I) : Finset I := Finset.univ.filter fun i => s i = true

def noiseWeight (ε : ℝ) (μ : Cube I) : ℝ :=
  ∏ i, if μ i then ε else 1 - ε

omit [DecidableEq I] in
theorem noiseWeight_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) (μ : Cube I) :
    0 ≤ noiseWeight ε μ := by
  apply Finset.prod_nonneg
  intro i _
  split <;> linarith

theorem noiseWeight_sum (ε : ℝ) : (∑ μ : Cube I, noiseWeight ε μ) = 1 := by
  unfold noiseWeight
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => if b then ε else 1 - ε)]
  simp

theorem noise_walsh (ε : ℝ) (s : Cube I) :
    (∑ μ, noiseWeight ε μ * walsh s μ) = (1 - 2 * ε) ^ (support s).card := by
  unfold noiseWeight walsh
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    (if b then ε else 1 - ε) * bitSign (s i && b))]
  have hc (i : I) : (∑ b : Bool,
      (if b then ε else 1 - ε) * bitSign (s i && b)) =
        if s i then 1 - 2 * ε else 1 := by
    cases s i <;> simp [bitSign]
    ring
  simp_rw [hc]
  simp [support, Finset.prod_ite]

def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

def projectedCoefficient (π : J → I) (A : Cube I → ℝ) (s : Cube J) : ℝ :=
  𝔼 f, A f * walsh s (fun y => f (π y))

def testBias (ε : ℝ) (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ * A f *
    (𝔼 g, B g * B (thirdQuery π f g μ))

theorem testBias_fourier (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → ℝ) :
    testBias ε π A B = ∑ s,
      projectedCoefficient π A s * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
  unfold testBias thirdQuery
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (f : Cube I) :
      (∑ μ, noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * walsh s (cubeXor (fun y => f (π y)) μ))) =
      (A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
    simp_rw [walsh_xor]
    have heq (μ : Cube J) : noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * (walsh s (fun y => f (π y)) * walsh s μ)) =
      ((A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2) *
        (noiseWeight ε μ * walsh s μ) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, noise_walsh]
  simp_rw [hterm, ← Finset.expect_mul]
  rfl

def testAcceptance (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

theorem threeBit_indicator (a b c : Bool) :
    (if a ^^ b ^^ c then (0 : ℝ) else 1) =
      (1 + bitSign a * bitSign b * bitSign c) / 2 := by
  cases a <;> cases b <;> cases c <;> norm_num [bitSign]

theorem testAcceptance_eq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    testAcceptance ε π A B =
      (1 + testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g))) / 2 := by
  unfold testAcceptance testBias
  simp_rw [threeBit_indicator, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp only [Fintype.expect_const]
  have hterm (f : Cube I) (μ : Cube J) :
      noiseWeight ε μ * ((1 + 𝔼 g,
        bitSign (A f) * bitSign (B g) * bitSign (B (thirdQuery π f g μ))) * 2⁻¹) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (A f) *
        (𝔼 g, bitSign (B g) * bitSign (B (thirdQuery π f g μ)))) * 2⁻¹ := by
    simp_rw [mul_assoc (bitSign (A f)), ← Finset.mul_expect]
    ring
  simp_rw [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp

end IndependentSetsGames.Foundations.Hastad

end

end OAI


end PinnedSource3


/- Source: OAI.Combinatorics.IndependentSets.Fourier.Folding; pinned OAI proof, Apache-2.0. -/
section PinnedSource4

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

theorem sum_cubeFlip (F : Cube I → ℝ) : (∑ f, F (cubeFlip f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeFlip f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg cubeFlip h
    simpa only [cubeFlip_cubeFlip] using h'
  · intro g _
    exact ⟨cubeFlip g, Finset.mem_univ _, cubeFlip_cubeFlip g⟩
  · intro f _
    rfl

theorem coefficient_zero_of_odd (F : Cube I → ℝ)
    (hF : ∀ f, F (cubeFlip f) = -F f) :
    coefficient F (fun _ => false) = 0 := by
  have hs : (∑ f, F f) = 0 := by
    have h := sum_cubeFlip F
    simp_rw [hF, Finset.sum_neg_distrib] at h
    linarith
  simp [coefficient, walsh, bitSign, Fintype.expect_eq_sum_div_card, hs]

theorem coefficient_sign_zero_of_folded (A : Cube I → Bool)
    (hA : ∀ f, A (cubeFlip f) = !(A f)) :
    coefficient (fun f => bitSign (A f)) (fun _ => false) = 0 := by
  apply coefficient_zero_of_odd
  intro f
  rw [hA, bitSign_not]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

omit [Fintype I] [DecidableEq I] in
theorem representative_flip (i₀ : I) (f : Cube I) :
    representative i₀ (cubeFlip f) = representative i₀ f := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

omit [Fintype I] [DecidableEq I] in
theorem canonicalInput_flip (i₀ : I) (f : Cube I) :
    canonicalInput i₀ (cubeFlip f) = canonicalInput i₀ f := by
  apply Subtype.ext
  exact representative_flip i₀ f

def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_flip (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) :
    foldedAnswer i₀ table (cubeFlip f) = !(foldedAnswer i₀ table f) := by
  unfold foldedAnswer
  rw [canonicalInput_flip]
  change (table (canonicalInput i₀ f) ^^ !(f i₀)) =
    !(table (canonicalInput i₀ f) ^^ f i₀)
  cases table (canonicalInput i₀ f) <;> cases f i₀ <;> rfl

theorem foldedAnswer_zero_coefficient (i₀ : I) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (foldedAnswer i₀ table f)) (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (foldedAnswer_flip i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_dictator (i₀ i : I) (f : Cube I) :
    foldedAnswer i₀ (fun h => h.val i) f = f i := by
  cases hf : f i₀ <;> cases hi : f i <;>
    simp [foldedAnswer, canonicalInput, representative, cubeFlip, hf, hi]

def coordinateMask (i : I) : Cube I := fun j => decide (j = i)

def cubeToggle (i : I) (f : Cube I) : Cube I :=
  cubeXor f (coordinateMask i)

omit [Fintype I] in
@[simp] theorem cubeToggle_twice (i : I) (f : Cube I) :
    cubeToggle i (cubeToggle i f) = f := by
  funext j
  change ((f j ^^ coordinateMask i j) ^^ coordinateMask i j) = f j
  cases f j <;> cases coordinateMask i j <;> rfl

theorem walsh_coordinateMask (s : Cube I) (i : I) :
    walsh s (coordinateMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [coordinateMask]
  · intro j _ hj
    simp [coordinateMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem walsh_cubeToggle (s : Cube I) (i : I) (f : Cube I) (hs : s i = true) :
    walsh s (cubeToggle i f) = -walsh s f := by
  rw [cubeToggle, walsh_xor, walsh_coordinateMask, hs]
  simp [bitSign]

theorem sum_cubeToggle (i : I) (F : Cube I → ℝ) :
    (∑ f, F (cubeToggle i f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeToggle i f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg (cubeToggle i) h
    simpa only [cubeToggle_twice] using h'
  · intro g _
    exact ⟨cubeToggle i g, Finset.mem_univ _, cubeToggle_twice i g⟩
  · intro f _
    rfl

def restrictQuery (valid : I → Bool) (f : Cube I) :
    Cube {i : I // valid i = true} := fun i => f i.val

omit [Fintype I] in
theorem restrictQuery_cubeToggle (valid : I → Bool) (i : I)
    (hi : valid i = false) (f : Cube I) :
    restrictQuery valid (cubeToggle i f) = restrictQuery valid f := by
  funext j
  have hj : j.val ≠ i := by
    intro heq
    have hp := j.property
    rw [heq, hi] at hp
    contradiction
  simp [restrictQuery, cubeToggle, cubeXor, coordinateMask, hj]

theorem conditioned_coefficient_zero_invalid (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I) (i : I)
    (hi : valid i = false) (hs : s i = true) :
    coefficient (fun f => B (restrictQuery valid f)) s = 0 := by
  have hsum := sum_cubeToggle i (fun f => B (restrictQuery valid f) * walsh s f)
  simp_rw [restrictQuery_cubeToggle valid i hi, walsh_cubeToggle s i _ hs,
    mul_neg, Finset.sum_neg_distrib] at hsum
  have hz : (∑ f, B (restrictQuery valid f) * walsh s f) = 0 := by linarith
  simp [coefficient, Fintype.expect_eq_sum_div_card, hz]

theorem conditioned_coefficient_support (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I)
    (hne : coefficient (fun f => B (restrictQuery valid f)) s ≠ 0) :
    ∀ i ∈ support s, valid i = true := by
  intro i hi
  have hs := (Finset.mem_filter.mp hi).2
  cases hv : valid i
  · exact False.elim (hne (conditioned_coefficient_zero_invalid valid B s i hv hs))
  · rfl

def conditionedFoldedAnswer (valid : I → Bool) (i₀ : {i : I // valid i = true})
    (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  foldedAnswer i₀ table (restrictQuery valid f)

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_flip (valid : I → Bool)
    (i₀ : {i : I // valid i = true}) (table : HalfCube i₀ → Bool) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ table (cubeFlip f) =
      !(conditionedFoldedAnswer valid i₀ table f) := by
  change foldedAnswer i₀ table (cubeFlip (restrictQuery valid f)) = _
  exact foldedAnswer_flip i₀ table (restrictQuery valid f)

theorem conditionedFoldedAnswer_zero_coefficient (valid : I → Bool)
    (i₀ : {i : I // valid i = true}) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (conditionedFoldedAnswer valid i₀ table f))
      (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (conditionedFoldedAnswer_flip valid i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_dictator (valid : I → Bool)
    (i₀ i : {i : I // valid i = true}) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ (fun h => h.val i) f = f i.val := by
  exact foldedAnswer_dictator i₀ i (restrictQuery valid f)

end IndependentSetsGames.Foundations.Hastad
end

end OAI


end PinnedSource4


/- Source: OAI.Combinatorics.IndependentSets.Fourier.Decoder; pinned OAI proof, Apache-2.0. -/
section PinnedSource5

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def parityProjection (π : J → I) (s : Cube J) : Cube I := fun i =>
  decide (Odd ((support s).filter fun y => π y = i).card)

theorem walsh_support (s x : Cube I) :
    walsh s x = ∏ i ∈ support s, bitSign (x i) := by
  unfold walsh support
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [bitSign]

theorem sign_power_parity (b : Bool) (n : Nat) :
    bitSign b ^ n = bitSign (decide (Odd n) && b) := by
  cases b
  · simp [bitSign]
  · simp only [Bool.and_true, bitSign, ite_true, decide_eq_true_eq]
    rw [neg_one_pow_eq_ite]
    by_cases h : Even n
    · simp [h, Nat.not_odd_iff_even.mpr h]
    · simp [h, Nat.not_even_iff_odd.mp h]

theorem walsh_pullback (π : J → I) (s : Cube J) (f : Cube I) :
    walsh s (fun y => f (π y)) = walsh (parityProjection π s) f := by
  rw [walsh_support]
  rw [← Finset.prod_fiberwise' (support s) π (fun i => bitSign (f i))]
  unfold walsh parityProjection
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const]
  exact sign_power_parity (f i) _

theorem projectedCoefficient_eq (π : J → I) (A : Cube I → ℝ) (s : Cube J) :
    projectedCoefficient π A s = coefficient A (parityProjection π s) := by
  simp only [projectedCoefficient, coefficient, walsh_pullback]

omit [DecidableEq J] in
theorem projection_has_preimage (π : J → I) (s : Cube J) (i : I)
    (hi : i ∈ support (parityProjection π s)) :
    ∃ y ∈ support s, π y = i := by
  have hodd : Odd ((support s).filter fun y => π y = i).card := by
    have hbit := (Finset.mem_filter.mp hi).2
    simpa only [parityProjection, decide_eq_true_eq] using hbit
  have hp : 0 < ((support s).filter fun y => π y = i).card := by
    obtain ⟨n, hn⟩ := hodd
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
  exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩

theorem scaled_geometric_power_le_one {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (n : Nat) :
    (n : ℝ) * (1 - t) * t ^ n ≤ 1 := by
  have hsum : (n : ℝ) * t ^ n ≤ ∑ j ∈ Finset.range n, t ^ j := by
    calc
      (n : ℝ) * t ^ n = ∑ _j ∈ Finset.range n, t ^ n := by simp
      _ ≤ ∑ j ∈ Finset.range n, t ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one ht ht' (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht')
  rw [geom_sum_mul_neg] at hm
  have hp : 0 ≤ t ^ n := pow_nonneg ht _
  nlinarith

theorem noise_decay_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    {k : Nat} (hk : 0 < k) :
    4 * ε * ((1 - 2 * ε) ^ k) ^ 2 ≤ 1 / (k : ℝ) := by
  have h := scaled_geometric_power_le_one (t := 1 - 2 * ε)
    (by linarith) (by linarith) (2 * k)
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkp).mpr
  have hpow : (1 - 2 * ε) ^ (2 * k) = ((1 - 2 * ε) ^ k) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hpow] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

def zeroMask : Cube I := fun _ => false

omit [DecidableEq I] in
theorem support_eq_empty_iff (s : Cube I) : support s = ∅ ↔ s = zeroMask := by
  constructor
  · intro h
    funext i
    have hi : i ∉ support s := by rw [h]; simp
    have : s i ≠ true := by simpa [support] using hi
    cases hs : s i <;> simp_all [zeroMask]
  · intro h
    subst s
    simp [zeroMask, support]

omit [Fintype I] [DecidableEq J] in
theorem parityProjection_zero (π : J → I) :
    parityProjection π (zeroMask : Cube J) = zeroMask := by
  funext i
  simp [parityProjection, support, zeroMask]

def agreementProbability (π : J → I) (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a, (((support b).filter fun y => π y = i).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem agreementProbability_nonneg (π : J → I) (a : Cube I) (b : Cube J) :
    0 ≤ agreementProbability π a b := by
  unfold agreementProbability
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [DecidableEq J] in
theorem agreementProbability_projection (π : J → I) (b : Cube J)
    (ha : (support (parityProjection π b)).Nonempty) :
    1 / ((support b).card : ℝ) ≤ agreementProbability π (parityProjection π b) b := by
  have hca : (0 : ℝ) < (support (parityProjection π b)).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ha)
  have hb : (support b).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    obtain ⟨y, hy, _⟩ := projection_has_preimage π b i hi
    exact ⟨y, hy⟩
  have hcb : (0 : ℝ) < (support b).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hb)
  have hsum : ((support (parityProjection π b)).card : ℝ) ≤
      ∑ i ∈ support (parityProjection π b),
        (((support b).filter fun y => π y = i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ support (parityProjection π b), (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨y, hy, hπ⟩ := projection_has_preimage π b i hi
        have hp : 0 < ((support b).filter fun y => π y = i).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hπ⟩⟩
        exact_mod_cast hp
  unfold agreementProbability
  apply (div_le_div_iff₀ hcb (mul_pos hca hcb)).mpr
  nlinarith

def decoderSuccess (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)

def decodingEnergy (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  ∑ b, projectedCoefficient π A b ^ 2 * coefficient B b ^ 2 / (support b).card

theorem decodingEnergy_le_success (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    decodingEnergy π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ≤
      decoderSuccess π A B := by
  unfold decodingEnergy decoderSuccess
  apply Finset.sum_le_sum
  intro b _
  rw [projectedCoefficient_eq]
  have hsum :
      coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        agreementProbability π (parityProjection π b) b ≤
      ∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun a => coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)
    · intro a _
      exact mul_nonneg (sq_nonneg _) (agreementProbability_nonneg π a b)
    · exact Finset.mem_univ _
  have hm := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (coefficient (fun g => bitSign (B g)) b))
  by_cases ha : (support (parityProjection π b)).Nonempty
  · have hagree := agreementProbability_projection π b ha
    have ht := mul_le_mul_of_nonneg_left hagree
      (mul_nonneg (sq_nonneg (coefficient (fun f => bitSign (A f))
        (parityProjection π b))) (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    have heq : coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2 / (support b).card =
      (coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2) * (1 / (support b).card) := by ring
    rw [heq]
    exact ht.trans (by convert hm using 1; ring)
  · have hempty : support (parityProjection π b) = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hz := (support_eq_empty_iff _).mp hempty
    simpa [hz, hzero] using hm

theorem bias_sq_le_weighted_energy (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → Bool) :
    testBias ε π A (fun g => bitSign (B g)) ^ 2 ≤
      ∑ b, (projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
        (1 - 2 * ε) ^ (support b).card) ^ 2 := by
  rw [testBias_fourier]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
      (1 - 2 * ε) ^ (support b).card)
    (fun b => coefficient (fun g => bitSign (B g)) b)
  rw [sign_parseval, mul_one] at h
  convert h using 1
  congr 1
  apply congrArg (fun x : Real => x^2)
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem decoder_four_epsilon_bias_sq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    4 * ε * testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ^ 2 ≤
      decoderSuccess π A B := by
  apply le_trans _ (decodingEnergy_le_success π A B hzero)
  have hcs := mul_le_mul_of_nonneg_left
    (bias_sq_le_weighted_energy ε π (fun f => bitSign (A f)) B)
    (by linarith : 0 ≤ 4 * ε)
  apply hcs.trans
  rw [Finset.mul_sum]
  unfold decodingEnergy
  apply Finset.sum_le_sum
  intro b _
  by_cases hk : 0 < (support b).card
  · have hd := noise_decay_bound hε hε' hk
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (sq_nonneg (projectedCoefficient π (fun f => bitSign (A f)) b))
        (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    convert hm using 1 <;> ring
  · have hb : support b = ∅ := Finset.card_eq_zero.mp (by omega)
    have hbzero := (support_eq_empty_iff b).mp hb
    subst b
    simp [projectedCoefficient_eq, parityProjection_zero, hzero, support, zeroMask]

theorem folded_decoder_bound (ε : ℝ) (π : J → I)
    (i₀ : I) (table : HalfCube i₀ → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ table f))
      (fun g => bitSign (B g)) ^ 2 ≤ decoderSuccess π (foldedAnswer i₀ table) B := by
  exact decoder_four_epsilon_bias_sq ε π (foldedAnswer i₀ table) B hε hε'
    (foldedAnswer_zero_coefficient i₀ table)

def validAgreementProbability (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a,
    (((support b).filter fun y => π y = i ∧ valid y = true).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem validAgreementProbability_eq (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) (hb : ∀ y ∈ support b, valid y = true) :
    validAgreementProbability valid π a b = agreementProbability π a b := by
  unfold validAgreementProbability agreementProbability
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro y hy
  simp [hb y hy]

def validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 *
      validAgreementProbability valid π a b)

theorem conditioned_validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (j₀ : {j : J // valid j = true})
    (table : HalfCube j₀ → Bool) :
    validDecoderSuccess valid π A (conditionedFoldedAnswer valid j₀ table) =
      decoderSuccess π A (conditionedFoldedAnswer valid j₀ table) := by
  unfold validDecoderSuccess decoderSuccess
  apply Finset.sum_congr rfl
  intro b _
  by_cases hc : coefficient (fun g => bitSign (conditionedFoldedAnswer valid j₀ table g)) b = 0
  · simp [hc]
  · have hb : ∀ y ∈ support b, valid y = true := by
      apply conditioned_coefficient_support valid (fun g => bitSign (foldedAnswer j₀ table g)) b
      exact hc
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [validAgreementProbability_eq valid π a b hb]

theorem conditioned_folded_decoder_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validDecoderSuccess valid π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  rw [conditioned_validDecoderSuccess]
  exact folded_decoder_bound ε π i₀ tableA
    (conditionedFoldedAnswer valid j₀ tableB) hε hε'

end IndependentSetsGames.Foundations.Hastad
end

end OAI


end PinnedSource5


/- Source: OAI.Combinatorics.IndependentSets.PCP.AssignmentTester; pinned OAI proof, Apache-2.0. -/
section PinnedSource6

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AssignmentTester

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

theorem truth_nonneg (b : Bool) : 0 ≤ truth b := by cases b <;> norm_num [truth]

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

theorem disagree_xor_le (a b c d : Bool) :
    disagree (a ^^ b) (c ^^ d) ≤ disagree a c + disagree b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [disagree]

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

theorem bitSign_parity (s f : Cube A) : bitSign (parity s f) = walsh s f := by
  have hw : walsh s f = (-1 : ℝ) ^
      (Finset.univ.filter fun a => s a && f a = true).card := by
    simp [walsh, bitSign, Finset.prod_ite]
  rw [hw]
  simpa [parity, bitSign] using
    (sign_power_parity true (Finset.univ.filter fun a => s a && f a = true).card).symm

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign] <;> linarith

theorem parity_xor (s f g : Cube A) :
    parity s (cubeXor f g) = (parity s f ^^ parity s g) := by
  apply bitSign_injective
  rw [bitSign_parity, bitSign_xor, bitSign_parity, bitSign_parity, walsh_xor]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

theorem expect_cubeXor (F : Cube A → ℝ) (g : Cube A) :
    (𝔼 f, F (cubeXor f g)) = 𝔼 f, F f := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_bij (fun f _ => cubeXor f g) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ h _ heq
    have hh := congrArg (fun x => cubeXor x g) heq
    simpa only [cubeXor_right_twice] using hh
  · intro f _
    exact ⟨cubeXor f g, Finset.mem_univ _, cubeXor_right_twice f g⟩
  · intro f _
    rfl

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

theorem distance_nonneg {K : Type*} [Fintype K] (f g : K → Bool) :
    0 ≤ distance f g := by
  apply Finset.expect_nonneg
  intro k _
  exact disagree_nonneg _ _

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

theorem blr_correlation (F : Cube A → Bool) :
    (𝔼 f, 𝔼 g, bitSign (F f) * bitSign (F g) * bitSign (F (cubeXor f g))) =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3 := by
  simp_rw [mul_assoc, ← Finset.mul_expect]
  conv_lhs =>
    enter [2, f, 2, 2, g, 2, 1]
    rw [cubeXor_comm]
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have heq (f : Cube A) : bitSign (F f) *
      (coefficient (fun f => bitSign (F f)) s ^ 2 * walsh s f) =
    coefficient (fun f => bitSign (F f)) s ^ 2 * (bitSign (F f) * walsh s f) := by ring
  simp_rw [heq, ← Finset.mul_expect]
  change coefficient (fun f => bitSign (F f)) s ^ 2 *
    coefficient (fun f => bitSign (F f)) s = _
  ring

theorem blrReject_fourier (F : Cube A → Bool) :
    blrReject F = (1 - ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3) / 2 := by
  unfold blrReject
  simp_rw [disagree_eq, bitSign_xor, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rw [blr_correlation]

theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let c := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, c s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, c t ^ 3) ≤ c s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < c s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        c s ^ 3 ≤ (∑ t, c t ^ 3) * c s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg (c s))
      nlinarith
    have hlt : c s₀ ^ 3 < (∑ t, c t ^ 3) * c s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [c] at hs
  linarith

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

theorem parity_selfCorrect (s x r : Cube A) :
    (parity s r ^^ parity s (cubeXor r x)) = parity s x := by
  rw [parity_xor]
  cases parity s r <;> cases parity s x <;> rfl

theorem selfCorrect_error (F : Cube A → Bool) (s x : Cube A) :
    (𝔼 r, disagree (selfCorrect F x r) (parity s x)) ≤ 2 * distance F (parity s) := by
  have hle (r : Cube A) :
      disagree (selfCorrect F x r) (parity s x) ≤
      disagree (F r) (parity s r) +
        disagree (F (cubeXor r x)) (parity s (cubeXor r x)) := by
    rw [← parity_selfCorrect s x r]
    exact disagree_xor_le _ _ _ _
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hle r)
  rw [Finset.expect_add_distrib,
    expect_cubeXor (fun r => disagree (F r) (parity s r)) x] at h
  change _ ≤ distance F (parity s) + distance F (parity s) at h
  linarith

def singleMask (i : A) : Cube A := fun j => decide (j = i)

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem expect_flipAt (F : Cube A → ℝ) (i : A) :
    (𝔼 f, F (flipAt i f)) = 𝔼 f, F f := by
  simp_rw [flipAt_eq_xor]
  exact expect_cubeXor F _

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

theorem andLawFailure_flipAt_second (s : Cube A) (i : A) (f g : Cube A)
    (hi : s i = true) :
    andLawFailure s f (flipAt i g) =
      (andLawFailure s f g ^^ (parity s f ^^ f i)) := by
  have hAnd : cubeAnd f (flipAt i g) =
      (if f i then flipAt i (cubeAnd f g) else cubeAnd f g) := by
    funext a
    by_cases ha : a = i
    · subst a
      cases hfi : f i <;> simp [cubeAnd, flipAt, hfi]
    · cases hfi : f i <;> simp [cubeAnd, flipAt, ha]
  have hg := parity_flipAt s i g hi
  have hfg := parity_flipAt s i (cubeAnd f g) hi
  cases hfi : f i <;> cases hf : parity s f <;>
    cases hg₀ : parity s g <;> cases ha : parity s (cubeAnd f g) <;>
    simp [andLawFailure, hAnd, hg, hfg, hfi, hf, hg₀, ha]

private theorem four_truth_lower (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem parity_and_rejection (s : Cube A) (i j : A)
    (hi : s i = true) (hj : s j = true) (hij : i ≠ j) :
    (1 : ℝ) / 4 ≤ 𝔼 f, 𝔼 g, truth (andLawFailure s f g) := by
  have hpoint (f g : Cube A) : (1 : ℝ) ≤
      truth (andLawFailure s f g) + truth (andLawFailure s f (flipAt i g)) +
      truth (andLawFailure s (flipAt j f) g) +
      truth (andLawFailure s (flipAt j f) (flipAt i g)) := by
    rw [andLawFailure_flipAt_second s i f g hi,
      andLawFailure_flipAt_second s i (flipAt j f) g hi]
    have hD : (parity s (flipAt j f) ^^ (flipAt j f) i) =
        !(parity s f ^^ f i) := by
      rw [parity_flipAt s j f hj]
      simp only [flipAt, if_neg hij]
      cases hf : parity s f <;> cases hfi : f i <;> simp
    rw [hD]
    exact four_truth_lower _ _ _
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hpoint f g))
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  have hinner (f : Cube A) :
      (𝔼 g, truth (andLawFailure s f (flipAt i g))) =
        𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun g => truth (andLawFailure s f g)) i
  have houter : (𝔼 f, 𝔼 g, truth (andLawFailure s (flipAt j f) g)) =
      𝔼 f, 𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun f => 𝔼 g, truth (andLawFailure s f g)) j
  simp only [hinner, houter] at havg
  linarith

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

theorem disagree_triangle (a b c : Bool) :
    disagree a c ≤ disagree a b + disagree b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

theorem andReject_nonneg (F : Cube A → Bool) : 0 ≤ andReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  apply Finset.expect_nonneg
  intro r₀ _
  apply Finset.expect_nonneg
  intro r₁ _
  apply Finset.expect_nonneg
  intro r₂ _
  exact disagree_nonneg _ _

theorem unitReject_nonneg (F : Cube A → Bool) : 0 ≤ unitReject F := by
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

omit [Nonempty K] in
theorem inputReject_nonneg (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) :
    0 ≤ inputReject label σ F := by
  apply Finset.expect_nonneg
  intro k _
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

theorem andReject_transfer (F : Cube A → Bool) (s : Cube A) :
    (𝔼 f, 𝔼 g, truth (andLawFailure s f g)) ≤
      andReject F + 6 * distance F (parity s) := by
  have hlocal (f g : Cube A) : truth (andLawFailure s f g) ≤
      (𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
        disagree (selfCorrect F (cubeAnd f g) r₀)
          (selfCorrect F f r₁ && selfCorrect F g r₂)) +
      6 * distance F (parity s) := by
    have hp (r₀ r₁ r₂ : Cube A) := and_disagree_transfer
      (parity s (cubeAnd f g)) (parity s f) (parity s g)
      (selfCorrect F (cubeAnd f g) r₀) (selfCorrect F f r₁) (selfCorrect F g r₂)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r₀ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun r₁ _ =>
        Finset.expect_le_expect (s := Finset.univ) (fun r₂ _ => hp r₀ r₁ r₂)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
    have h₀ := selfCorrect_error F s (cubeAnd f g)
    have h₁ := selfCorrect_error F s f
    have h₂ := selfCorrect_error F s g
    rw [andLawFailure, truth_xor]
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hlocal f g))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, andReject] using h

theorem parity_zero (f : Cube A) : parity (fun _ => false) f = false := by
  apply bitSign_injective
  rw [bitSign_parity]
  simp [walsh, bitSign]

theorem unitReject_zero_parity (F : Cube A → Bool) :
    1 - 2 * distance F (parity (fun _ => false)) ≤ unitReject F := by
  have herr := selfCorrect_error F (fun _ => false) (fun _ => true)
  simp only [parity_zero] at herr
  have heq : unitReject F +
      (𝔼 r, disagree (selfCorrect F (fun _ => true) r) false) = 1 := by
    unfold unitReject
    rw [← Finset.expect_add_distrib]
    have hp (b : Bool) : disagree b true + disagree b false = 1 := by
      cases b <;> norm_num [disagree]
    simp only [hp, Fintype.expect_const]
  linarith

theorem parity_singleMask_eval (a : A) (f : Cube A) :
    parity (singleMask a) f = f a := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_symm, walsh_singleMask]

theorem inputReject_transfer (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) (a : A) :
    distance σ (label a) ≤ inputReject label σ F +
      2 * distance F (parity (singleMask a)) := by
  have hlocal (k : K) : disagree (σ k) (label a k) ≤
      (𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)) +
        2 * distance F (parity (singleMask a)) := by
    have hp (r : Cube A) := disagree_triangle (σ k)
      (selfCorrect F (fun a => label a k) r) (label a k)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
    simp only [Fintype.expect_const, Finset.expect_add_distrib] at havg
    have herr := selfCorrect_error F (singleMask a) (fun a => label a k)
    simp only [parity_singleMask_eval] at herr
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun k _ => hlocal k)
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, inputReject, distance] using h

theorem tester_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ testerReject label σ F := by
  have hblr := blrReject_nonneg F
  have hand := andReject_nonneg F
  have hunit := unitReject_nonneg F
  have hin := inputReject_nonneg label σ F
  by_cases hb : δ / 64 ≤ blrReject F
  · unfold testerReject
    linarith
  obtain ⟨s, hs⟩ := blr_near_parity F
  by_cases hz : s = fun _ => false
  · subst s
    have hu := unitReject_zero_parity F
    unfold testerReject
    linarith
  have hsome : ∃ i, s i = true := by
    by_contra hh
    push Not at hh
    apply hz
    funext i
    have h := hh i
    cases hi : s i <;> simp_all
  obtain ⟨i, hi⟩ := hsome
  by_cases htwo : ∃ j, i ≠ j ∧ s j = true
  · obtain ⟨j, hij, hj⟩ := htwo
    have ha := parity_and_rejection s i j hi hj hij
    have ht := andReject_transfer F s
    unfold testerReject
    linarith
  · have heq : s = singleMask i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [singleMask, hi]
      · have hj : s j = false := by
          cases hv : s j
          · rfl
          · exact False.elim (htwo ⟨j, Ne.symm hji, hv⟩)
        simp [singleMask, hji, hj]
    subst s
    have ht := inputReject_transfer label σ F i
    have hf := hfar i
    unfold testerReject
    linarith

omit [Fintype A] [DecidableEq A] in
theorem selfCorrect_dictator (a : A) (x r : Cube A) :
    selfCorrect (fun f => f a) x r = x a := by
  change (r a ^^ (r a ^^ x a)) = x a
  cases r a <;> cases x a <;> rfl

omit [Nonempty K] in
theorem tester_perfect_completeness (label : A → K → Bool) (a : A) :
    testerReject label (label a) (fun f => f a) = 0 := by
  have hb : blrReject (fun f : Cube A => f a) = 0 := by
    simp [blrReject, cubeXor, disagree]
  have ha : andReject (fun f : Cube A => f a) = 0 := by
    simp [andReject, selfCorrect_dictator, cubeAnd, disagree]
  have hu : unitReject (fun f : Cube A => f a) = 0 := by
    simp [unitReject, selfCorrect_dictator, disagree]
  have hi : inputReject label (label a) (fun f => f a) = 0 := by
    simp [inputReject, selfCorrect_dictator, disagree]
  simp [testerReject, hb, ha, hu, hi]

def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem event_perfect_completeness (label : A → K → Bool) (a : A)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
      (eventQueries label kind k f g r₀ r₁ r₂ slot)) = true := by
  have hkind : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hreject : eventReject label (label a) (fun x => x a) kind k f g r₀ r₁ r₂ = 0 := by
    rcases hkind with h | h | h | h <;> subst kind
    · simp [eventReject_blr, cubeXor, disagree]
    · simp [eventReject_and, selfCorrect_dictator, cubeAnd, disagree]
    · simp [eventReject_unit, selfCorrect_dictator, disagree]
    · simp [eventReject_input, selfCorrect_dictator, disagree]
  unfold eventReject at hreject
  cases h : eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
    (eventQueries label kind k f g r₀ r₁ r₂ slot)) <;> simp_all [truth]

def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

theorem explicitTesterReject_eq (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) : explicitTesterReject label σ F = testerReject label σ F := by
  unfold explicitTesterReject
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fin.sum_univ_succ, eventReject_blr, eventReject_and, eventReject_unit,
    eventReject_input, testerReject, blrReject, andReject, unitReject, inputReject, add_assoc]

theorem explicit_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ explicitTesterReject label σ F := by
  rw [explicitTesterReject_eq]
  exact tester_proximity_soundness label σ F hδ hδ' hfar

end IndependentSetsGames.Foundations.PCP.AssignmentTester
end

end OAI


end PinnedSource6


/- Source: OAI.Combinatorics.IndependentSets.Reduction.Cube; pinned OAI proof, Apache-2.0. -/
section PinnedSource7

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

@[reducible] def Cube : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI := cubeFintype n
      exact inferInstanceAs (Fintype (Bool × Cube n))

instance cubeNonempty : (n : ℕ) → Nonempty (Cube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => @instNonemptyProd Bool (Cube n) _ (cubeNonempty n)

noncomputable def mean {n : ℕ} (f : Cube n → ℝ) : ℝ := 𝔼 x, f x

lemma mean_zero (f : Cube 0 → ℝ) : mean f = f () := by
  change (𝔼 x : Unit, f x) = f ()
  simp [Finset.expect_eq_sum_div_card]

lemma mean_succ {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean f = (mean (fun x => f (false,x)) + mean (fun x => f (true,x))) / 2 := by
  change (𝔼 x : Bool × Cube n, f x) = _
  rw [show (Finset.univ : Finset (Bool × Cube n)) = Finset.univ ×ˢ Finset.univ from rfl,
    Finset.expect_product]
  simp [Finset.expect_eq_sum_div_card, mean, add_comm]

lemma mean_add {n : ℕ} (f g : Cube n → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := Finset.expect_add_distrib _ _ _

lemma mean_sub {n : ℕ} (f g : Cube n → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := Finset.expect_sub_distrib _ _ _

lemma mean_mul {n : ℕ} (a : ℝ) (f : Cube n → ℝ) :
    mean (fun x => a * f x) = a * mean f := (Finset.mul_expect _ _ _).symm

lemma mean_nonneg {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

lemma mean_mono {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

lemma mean_cauchy {n : ℕ} (f g : Cube n → ℝ) :
    (mean (fun x => f x * g x))^2 ≤ mean (fun x => f x^2) * mean (fun x => g x^2) :=
  Finset.expect_mul_sq_le_sq_mul_sq _ _ _

noncomputable def evenPart {n : ℕ} (f : Cube (n+1) → ℝ) (x : Cube n) :=
  (f (false,x) + f (true,x)) / 2

noncomputable def oddPart {n : ℕ} (f : Cube (n+1) → ℝ) (x : Cube n) :=
  (f (false,x) - f (true,x)) / 2

noncomputable def noise (ρ : ℝ) : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => noise ρ (evenPart f) x + (if b then -ρ else ρ) * noise ρ (oddPart f) x

lemma mean_square_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean (fun x => f x^2) = mean (fun x => evenPart f x^2) + mean (fun x => oddPart f x^2) := by
  rw [mean_succ, ← mean_add]
  rw [← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul]
  congr 1
  funext x
  dsimp [evenPart, oddPart]
  ring

lemma mean_noise_fourth {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    mean (fun x => noise ρ f x ^ 4) =
      mean (fun x => noise ρ (evenPart f) x ^ 4) +
      6 * ρ^2 * mean (fun x => (noise ρ (evenPart f) x)^2 * (noise ρ (oddPart f) x)^2) +
      ρ^4 * mean (fun x => noise ρ (oddPart f) x ^ 4) := by
  rw [mean_succ, ← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul, ← mean_mul, ← mean_add,
    ← mean_mul, ← mean_add]
  congr 1
  funext x
  dsimp [noise]
  ring

theorem hypercontractive_two_four {n : ℕ} (f : Cube n → ℝ) :
    mean (fun x => noise (1/2) f x ^ 4) ≤ (mean (fun x => f x^2))^2 := by
  induction n with
  | zero =>
    simp only [mean_zero, noise]
    nlinarith
  | succ n ih =>
    let a := evenPart f
    let b := oddPart f
    let A := mean (fun x => a x^2)
    let B := mean (fun x => b x^2)
    let C := mean (fun x => noise (1/2) a x^4)
    let D := mean (fun x => noise (1/2) b x^4)
    let E := mean (fun x => (noise (1/2) a x)^2 * (noise (1/2) b x)^2)
    have hA : 0 ≤ A := mean_nonneg (fun x => sq_nonneg _)
    have hB : 0 ≤ B := mean_nonneg (fun x => sq_nonneg _)
    have hC : 0 ≤ C := mean_nonneg (fun x => by positivity)
    have hD : 0 ≤ D := mean_nonneg (fun x => by positivity)
    have hE : 0 ≤ E := mean_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hCA : C ≤ A^2 := ih a
    have hDB : D ≤ B^2 := ih b
    have hEC : E^2 ≤ C*D := by
      have hc := mean_cauchy (fun x => (noise (1/2) a x)^2) (fun x => (noise (1/2) b x)^2)
      have hpow (x : ℝ) : (x^2)^2 = x^4 := by ring
      simp only [hpow] at hc
      exact hc
    have hmul : C*D ≤ A^2*B^2 := mul_le_mul hCA hDB hD (sq_nonneg A)
    have hEAB : E ≤ A*B := by
      nlinarith [hEC.trans hmul, mul_nonneg hA hB]
    rw [mean_noise_fourth, mean_square_split]
    change C + 6*(1/2:ℝ)^2*E + (1/2:ℝ)^4*D ≤ (A+B)^2
    nlinarith [mul_nonneg hA hB]

lemma evenPart_noise {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    evenPart (noise ρ f) = noise ρ (evenPart f) := by
  funext x
  dsimp [evenPart, noise]
  ring

lemma oddPart_noise {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    oddPart (noise ρ f) = fun x => ρ * noise ρ (oddPart f) x := by
  funext x
  dsimp [oddPart, noise]
  ring

lemma mean_product_split {n : ℕ} (f g : Cube (n+1) → ℝ) :
    mean (fun x => f x * g x) =
      mean (fun x => evenPart f x * evenPart g x) +
      mean (fun x => oddPart f x * oddPart g x) := by
  rw [mean_succ, ← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul,
    ← mean_add]
  congr 1
  funext x
  dsimp [evenPart, oddPart]
  ring

lemma noise_selfadjoint {n : ℕ} (ρ : ℝ) (f g : Cube n → ℝ) :
    mean (fun x => f x * noise ρ g x) = mean (fun x => noise ρ f x * g x) := by
  induction n with
  | zero => simp only [mean_zero, noise]
  | succ n ih =>
    rw [mean_product_split, mean_product_split, evenPart_noise, oddPart_noise,
      evenPart_noise, oddPart_noise, ih]
    have h₁ : mean (fun x => oddPart f x * (ρ * noise ρ (oddPart g) x)) =
        ρ * mean (fun x => oddPart f x * noise ρ (oddPart g) x) := by
      rw [← mean_mul]
      congr 1; funext x; ring
    have h₂ : mean (fun x => ρ * noise ρ (oddPart f) x * oddPart g x) =
        ρ * mean (fun x => noise ρ (oddPart f) x * oddPart g x) := by
      rw [← mean_mul]
      congr 1; funext x; ring
    rw [h₁, h₂, ih]

lemma mean_holder_four {n : ℕ} (g h : Cube n → ℝ) :
    (mean (fun x => g x * h x))^4 ≤
      (mean (fun x => |g x|))^2 * mean (fun x => g x^2) * mean (fun x => h x^4) := by
  let G := mean (fun x => |g x|)
  let U := mean (fun x => |g x| * |h x|)
  let V := mean (fun x => |g x| * h x^2)
  have hG : 0 ≤ G := mean_nonneg (fun x => abs_nonneg _)
  have hU : 0 ≤ U := mean_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hV : 0 ≤ V := mean_nonneg (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have huv : U^2 ≤ G*V := by
    have hc := mean_cauchy (fun x => Real.sqrt |g x|) (fun x => Real.sqrt |g x| * |h x|)
    have he₁ : (fun x => Real.sqrt |g x| * (Real.sqrt |g x| * |h x|)) =
        (fun x => |g x| * |h x|) := by
      funext x
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have he₂ : (fun x => (Real.sqrt |g x|)^2) = (fun x => |g x|) := by
      funext x; exact Real.sq_sqrt (abs_nonneg _)
    have he₃ : (fun x => (Real.sqrt |g x| * |h x|)^2) = (fun x => |g x| * h x^2) := by
      funext x
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    simpa only [he₁, he₂, he₃] using hc
  have hv : V^2 ≤ mean (fun x => g x^2) * mean (fun x => h x^4) := by
    have hc := mean_cauchy (fun x => |g x|) (fun x => h x^2)
    have hpow (x : ℝ) : (x^2)^2 = x^4 := by ring
    simp only [sq_abs, hpow] at hc
    exact hc
  have habs : |mean (fun x => g x * h x)| ≤ U := by
    have hh := Finset.abs_expect_le Finset.univ (fun x => g x*h x)
    simp only [abs_mul] at hh
    exact hh
  have hs : (mean (fun x => g x * h x))^2 ≤ U^2 := by
    have ha := abs_nonneg (mean (fun x => g x*h x))
    nlinarith [sq_abs (mean (fun x => g x*h x))]
  have hsq : (mean (fun x => g x * h x))^4 ≤ (G*V)^2 := by
    nlinarith [hs.trans huv, sq_nonneg (mean (fun x => g x*h x))]
  have hm := mul_le_mul_of_nonneg_left hv (sq_nonneg G)
  nlinarith

theorem noise_small_l1 {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (mean (fun x => noise (1/2) g x^2))^2 ≤ (mean (fun x => |g x|))^3 := by
  let u := noise (1/2) g
  let A := mean (fun x => u x^2)
  let I := mean (fun x => |g x|)
  have hA : 0 ≤ A := mean_nonneg (fun x => sq_nonneg _)
  have hI : 0 ≤ I := mean_nonneg (fun x => abs_nonneg _)
  have hgs : mean (fun x => g x^2) ≤ I := by
    apply mean_mono
    intro x
    nlinarith [hg x, abs_nonneg (g x), sq_abs (g x)]
  have he : mean (fun x => g x * noise (1/2) u x) = A := by
    rw [noise_selfadjoint]
    congr 1; funext x; simp only [u, pow_two]
  have h := mean_holder_four g (noise (1/2) u)
  rw [he] at h
  have hh := hypercontractive_two_four u
  have hp : 0 ≤ I^2 * mean (fun x => g x^2) :=
    mul_nonneg (sq_nonneg _) (mean_nonneg (fun x => sq_nonneg _))
  have h₂ := mul_le_mul_of_nonneg_left hh hp
  have h₃ := mul_le_mul_of_nonneg_left hgs (sq_nonneg I)
  have h₄ := mul_le_mul_of_nonneg_right h₃ (sq_nonneg A)
  change A^2 ≤ I^3
  change _ ≤ _ * A^2 at h₂
  nlinarith [h.trans h₂]

end LargeIndependentSets.BooleanJunta

end OAI


end PinnedSource7


/- Source: OAI.Combinatorics.IndependentSets.Fourier.Fourier; pinned OAI proof, Apache-2.0. -/
section PinnedSource8

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

lemma mean_congr {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x = g x) : mean f = mean g :=
  congrArg mean (funext h)

lemma sum_succ {n : ℕ} (f : Cube (n+1) → ℝ) :
    ∑ x, f x = (∑ x : Cube n, f (false,x)) + ∑ x : Cube n, f (true,x) := by
  change (∑ x : Bool × Cube n, f x) = _
  rw [Fintype.sum_prod_type]
  simp [add_comm]

noncomputable def fourier : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => if b then fourier (oddPart f) x else fourier (evenPart f) x

noncomputable def synth : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => synth (fun s => f (false,s)) x +
      (if b then -1 else 1) * synth (fun s => f (true,s)) x

lemma evenPart_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    evenPart (fun x => f x + g x) = fun x => evenPart f x + evenPart g x := by
  funext x; dsimp [evenPart]; ring

lemma oddPart_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    oddPart (fun x => f x + g x) = fun x => oddPart f x + oddPart g x := by
  funext x; dsimp [oddPart]; ring

lemma evenPart_mul {n : ℕ} (c : ℝ) (f : Cube (n+1) → ℝ) :
    evenPart (fun x => c * f x) = fun x => c * evenPart f x := by
  funext x; dsimp [evenPart]; ring

lemma oddPart_mul {n : ℕ} (c : ℝ) (f : Cube (n+1) → ℝ) :
    oddPart (fun x => c * f x) = fun x => c * oddPart f x := by
  funext x; dsimp [oddPart]; ring

lemma fourier_add {n : ℕ} (f g : Cube n → ℝ) :
    fourier (fun x => f x + g x) = fun s => fourier f s + fourier g s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_add, oddPart_add, ih]

lemma fourier_mul {n : ℕ} (c : ℝ) (f : Cube n → ℝ) :
    fourier (fun x => c * f x) = fun s => c * fourier f s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_mul, oddPart_mul, ih]

lemma fourier_sub {n : ℕ} (f g : Cube n → ℝ) :
    fourier (fun x => f x - g x) = fun s => fourier f s - fourier g s := by
  have he : (fun x => f x - g x) = (fun x => f x + -1 * g x) := by
    funext x; ring
  rw [he, fourier_add, fourier_mul]
  funext s; ring

lemma fourier_parseval {n : ℕ} (f : Cube n → ℝ) :
    (∑ s, (fourier f s)^2) = mean (fun x => f x^2) := by
  induction n with
  | zero => simp [fourier, mean_zero]
  | succ n ih =>
    rw [sum_succ, mean_square_split]
    simp only [fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]

lemma fourier_inner {n : ℕ} (f g : Cube n → ℝ) :
    (∑ s, fourier f s * fourier g s) = mean (fun x => f x*g x) := by
  induction n with
  | zero => simp [fourier, mean_zero]
  | succ n ih =>
    rw [sum_succ, mean_product_split]
    simp only [fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]

lemma synth_fourier {n : ℕ} (f : Cube n → ℝ) : synth (fourier f) = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,x⟩
    simp only [synth, fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]
    cases b <;> dsimp [evenPart, oddPart] <;> ring

lemma evenPart_synth {n : ℕ} (f : Cube (n+1) → ℝ) :
    evenPart (synth f) = synth (fun s => f (false,s)) := by
  funext x; dsimp [evenPart, synth]; ring

lemma oddPart_synth {n : ℕ} (f : Cube (n+1) → ℝ) :
    oddPart (synth f) = synth (fun s => f (true,s)) := by
  funext x; dsimp [oddPart, synth]; ring

lemma fourier_synth {n : ℕ} (f : Cube n → ℝ) : fourier (synth f) = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp only [fourier, Bool.false_eq_true, ↓reduceIte,
      evenPart_synth, oddPart_synth, ih]

def bit : {n : ℕ} → Cube n → Fin n → Bool
  | _+1, (b,x), i => Fin.cases b (bit x) i

def degree : {n : ℕ} → Cube n → ℕ
  | 0, _ => 0
  | _+1, (b,x) => (if b then 1 else 0) + degree x

lemma fourier_noise {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) :
    fourier (noise ρ f) = fun s => ρ^(degree s) * fourier f s := by
  induction n with
  | zero => funext s; simp [noise, fourier, degree]
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_noise, oddPart_noise, fourier_mul,
      ih, degree, pow_add, mul_assoc]

def flip : {n : ℕ} → Fin n → Cube n → Cube n
  | _+1, i, (b,x) => Fin.cases (!b,x) (fun j => (b,flip j x)) i

noncomputable def diff {n : ℕ} (i : Fin n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  (f x - f (flip i x))/2

lemma evenPart_diff_zero {n : ℕ} (f : Cube (n+1) → ℝ) :
    evenPart (diff 0 f) = fun _ => 0 := by
  funext x
  simp only [evenPart, diff, flip, Fin.cases_zero, Bool.not_false, Bool.not_true]
  ring

lemma oddPart_diff_zero {n : ℕ} (f : Cube (n+1) → ℝ) :
    oddPart (diff 0 f) = oddPart f := by
  funext x
  simp only [oddPart, diff, flip, Fin.cases_zero, Bool.not_false, Bool.not_true]
  ring

lemma evenPart_diff_succ {n : ℕ} (i : Fin n) (f : Cube (n+1) → ℝ) :
    evenPart (diff i.succ f) = diff i (evenPart f) := by
  funext x
  dsimp [evenPart, diff, flip]
  ring

lemma oddPart_diff_succ {n : ℕ} (i : Fin n) (f : Cube (n+1) → ℝ) :
    oddPart (diff i.succ f) = diff i (oddPart f) := by
  funext x
  dsimp [oddPart, diff, flip]
  ring

lemma fourier_zero {n : ℕ} : fourier (fun _ : Cube n => (0:ℝ)) = fun _ => 0 := by
  have h := fourier_mul (n := n) 0 (fun _ => 0)
  simpa only [zero_mul] using h

lemma fourier_diff {n : ℕ} (i : Fin n) (f : Cube n → ℝ) :
    fourier (diff i f) = fun s => if bit s i then fourier f s else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    funext ⟨b,s⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> simp [fourier, bit, evenPart_diff_zero, oddPart_diff_zero, fourier_zero]
    · cases b <;> simp [fourier, bit, evenPart_diff_succ, oddPart_diff_succ, ih]

end LargeIndependentSets.BooleanJunta

end OAI


end PinnedSource8


/- Source: OAI.Combinatorics.IndependentSets.Expansion.Supported; pinned OAI proof, Apache-2.0. -/
section PinnedSource9

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators
open scoped Classical

lemma degree_eq_sum {n : ℕ} (s : Cube n) :
    (degree s : ℝ) = ∑ i : Fin n, if bit s i then (1:ℝ) else 0 := by
  induction n with
  | zero => simp [degree]
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    rw [Fin.sum_univ_succ]
    cases b <;> simp only [degree, bit, Bool.false_eq_true, ↓reduceIte,
      Fin.cases_zero, Fin.cases_succ, Nat.cast_add, Nat.cast_one,
      zero_add, ih] <;> rfl

def Supported {n : ℕ} (S : Finset (Fin n)) (s : Cube n) : Prop :=
  ∀ i, bit s i = true → i ∈ S

noncomputable def walsh : {n : ℕ} → Cube n → Cube n → ℝ
  | 0, _, _ => 1
  | _+1, (b,s), (c,x) => (if b && c then -1 else 1) * walsh s x

lemma synth_eq_sum {n : ℕ} (a : Cube n → ℝ) (x : Cube n) :
    synth a x = ∑ s, a s * walsh s x := by
  induction n with
  | zero => simp [synth, walsh]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    rw [sum_succ]
    simp only [synth, walsh, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte, one_mul, ih]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring

lemma walsh_depends {n : ℕ} (s x y : Cube n)
    (h : ∀ i, bit s i = true → bit x i = bit y i) : walsh s x = walsh s y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    obtain ⟨c,x⟩ := x
    obtain ⟨d,y⟩ := y
    have ht : walsh s x = walsh s y := ih s x y (fun i hi => h i.succ hi)
    have hh : b = true → c = d := fun hb => h 0 hb
    cases b
    · simp [walsh, ht]
    · have he := hh rfl
      subst d
      simp [walsh, ht]

noncomputable def truncate {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) : Cube n → ℝ :=
  synth (fun s => if Supported S s then fourier f s else 0)

lemma truncate_depends {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) (x y : Cube n)
    (h : ∀ i ∈ S, bit x i = bit y i) : truncate S f x = truncate S f y := by
  rw [truncate, synth_eq_sum, synth_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Supported S s
  · simp only [if_pos hs]
    rw [walsh_depends s x y (fun i hi => h i (hs i hi))]
  · simp only [if_neg hs, zero_mul]

lemma truncate_error {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) :
    mean (fun x => (f x - truncate S f x)^2) =
      ∑ s, if Supported S s then 0 else (fourier f s)^2 := by
  rw [← fourier_parseval, fourier_sub]
  simp only [truncate, fourier_synth]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

noncomputable def influence {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  mean (fun x => |diff i f x|)

lemma influence_nonneg {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : 0 ≤ influence f i :=
  mean_nonneg (fun _ => abs_nonneg _)

lemma diff_bounded {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1) (i : Fin n) :
    ∀ x, |diff i f x| ≤ 1 := by
  intro x
  dsimp [diff]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have h := abs_sub (f x) (f (flip i x))
  linarith [hf x, hf (flip i x)]

lemma diff_square_le_influence {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (i : Fin n) : mean (fun x => diff i f x^2) ≤ influence f i := by
  apply mean_mono
  intro x
  have h := diff_bounded f hf i x
  nlinarith [abs_nonneg (diff i f x), sq_abs (diff i f x)]

lemma weighted_fourier_energy {n : ℕ} (f : Cube n → ℝ) :
    (∑ s, (degree s : ℝ) * (fourier f s)^2) =
      ∑ i : Fin n, mean (fun x => diff i f x^2) := by
  simp_rw [degree_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fourier_parseval, fourier_diff]
  apply Finset.sum_congr rfl
  intro s _
  cases h : bit s i <;> simp [h]

lemma noise_small_influence {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (i : Fin n) {θ : ℝ} (hθ : 0 ≤ θ) (hi : influence f i ≤ θ^2) :
    mean (fun x => noise (1/2) (diff i f) x^2) ≤ θ * influence f i := by
  have h := noise_small_l1 (diff i f) (diff_bounded f hf i)
  have hI := influence_nonneg f i
  have hN : 0 ≤ mean (fun x => noise (1/2) (diff i f) x^2) := mean_nonneg (fun _ => sq_nonneg _)
  change _ ≤ influence f i ^ 3 at h
  have hm := mul_le_mul_of_nonneg_right hi (sq_nonneg (influence f i))
  nlinarith [mul_nonneg hθ hI]

lemma noise_weight_cancel (d : ℕ) : (4:ℝ)^d * ((1/2:ℝ)^d)^2 = 1 := by
  calc
    _ = ((4:ℝ) * (1/2:ℝ)^2)^d := by rw [mul_pow, pow_right_comm]
    _ = 1 := by norm_num

lemma low_degree_coefficient {n : ℕ} (g : Cube n → ℝ) (s : Cube n) {k : ℕ}
    (hk : degree s ≤ k) :
    (fourier g s)^2 ≤ (4:ℝ)^k * (fourier (noise (1/2) g) s)^2 := by
  rw [fourier_noise]
  have hp : (4:ℝ)^(degree s) ≤ (4:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg ((1/2:ℝ)^(degree s)))
  rw [noise_weight_cancel] at hm
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (fourier g s))
  nlinarith

end LargeIndependentSets.BooleanJunta

end OAI


end PinnedSource9


/- Source: OAI.Combinatorics.IndependentSets.Reduction.Heavy; pinned OAI proof, Apache-2.0. -/
section PinnedSource10

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

noncomputable def heavy {n : ℕ} (θ : ℝ) (f : Cube n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => θ^2 < influence f i)

lemma heavy_card_bound {n : ℕ} (θ : ℝ) (f : Cube n → ℝ) :
    ((heavy θ f).card : ℝ) * θ^2 ≤ ∑ i, influence f i := by
  calc
    _ = ∑ _i ∈ heavy θ f, θ^2 := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ heavy θ f, influence f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, influence f i := Finset.sum_le_univ_sum_of_nonneg (fun i => influence_nonneg f i)

lemma high_degree_tail {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1) (k : ℕ) :
    (∑ s, if k < degree s then (fourier f s)^2 else 0) ≤
      (∑ i, influence f i) / (k+1:ℝ) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ)<k+1)).mpr
  calc
    _ = ∑ s, (if k < degree s then (fourier f s)^2 else 0) * (k+1:ℝ) :=
      Finset.sum_mul ..
    _ ≤ ∑ s, (degree s:ℝ) * (fourier f s)^2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : k < degree s
      · simp only [if_pos hs]
        have hk : (k+1:ℝ) ≤ degree s := by exact_mod_cast hs
        nlinarith [sq_nonneg (fourier f s)]
      · simp only [if_neg hs, zero_mul]
        positivity
    _ = ∑ i, mean (fun x => diff i f x^2) := weighted_fourier_energy f
    _ ≤ ∑ i, influence f i := Finset.sum_le_sum (fun i _ => diff_square_le_influence f hf i)

lemma low_degree_diff_sum {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (k : ℕ) :
    (∑ s, if degree s ≤ k then (fourier (diff i f) s)^2 else 0) ≤
      (4:ℝ)^k * mean (fun x => noise (1/2) (diff i f) x^2) := by
  rw [← fourier_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : degree s ≤ k
  · simpa only [if_pos hs] using low_degree_coefficient (diff i f) s hs
  · simp only [if_neg hs]
    positivity

lemma low_degree_outside {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    (∑ s, if degree s ≤ k ∧ ¬Supported (heavy θ f) s then (fourier f s)^2 else 0) ≤
      (4:ℝ)^k * θ * (∑ i, influence f i) := by
  let S := heavy θ f
  have hpoint (s : Cube n) :
      (if degree s ≤ k ∧ ¬Supported S s then (fourier f s)^2 else 0) ≤
      ∑ i : Fin n, if i ∈ S then 0 else
        if degree s ≤ k then (fourier (diff i f) s)^2 else 0 := by
    have hn (i : Fin n) : 0 ≤ (if i ∈ S then (0:ℝ) else
        if degree s ≤ k then (fourier (diff i f) s)^2 else 0) := by
      split_ifs <;> positivity
    by_cases hs : degree s ≤ k ∧ ¬Supported S s
    · simp only [if_pos hs]
      obtain ⟨i, hi, hni⟩ : ∃ i, bit s i = true ∧ i ∉ S := by
        obtain ⟨i, hi⟩ := not_forall.mp hs.2
        exact ⟨i, (Classical.not_imp.mp hi).1, (Classical.not_imp.mp hi).2⟩
      have hb := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
      simpa only [if_neg hni, if_pos hs.1, fourier_diff, hi, ↓reduceIte] using hb
    · simp only [if_neg hs]
      exact Finset.sum_nonneg (fun i _ => hn i)
  have hb := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Cube n))) => hpoint s)
  rw [Finset.sum_comm] at hb
  apply hb.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [if_pos hi, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hθ) (influence_nonneg f i)
  · simp only [if_neg hi]
    have hsmall : influence f i ≤ θ^2 := by
      have hh : ¬θ^2 < influence f i := by
        intro hlt
        apply hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      exact le_of_not_gt hh
    calc
      _ ≤ (4:ℝ)^k * mean (fun x => noise (1/2) (diff i f) x^2) := low_degree_diff_sum f i k
      _ ≤ (4:ℝ)^k * (θ * influence f i) :=
        mul_le_mul_of_nonneg_left (noise_small_influence f hf i hθ hsmall) (by positivity)
      _ = (4:ℝ)^k * θ * influence f i := by ring

theorem boolean_junta_error {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    mean (fun x => (f x - truncate (heavy θ f) f x)^2) ≤
      (∑ i, influence f i) / (k+1:ℝ) + (4:ℝ)^k * θ * (∑ i, influence f i) := by
  rw [truncate_error]
  have hsplit : (∑ s, if Supported (heavy θ f) s then 0 else (fourier f s)^2) ≤
      (∑ s, if k < degree s then (fourier f s)^2 else 0) +
      (∑ s, if degree s ≤ k ∧ ¬Supported (heavy θ f) s then (fourier f s)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    by_cases ht : Supported (heavy θ f) s <;>
      by_cases hd : degree s ≤ k <;>
      simp [ht, hd, show (k < degree s) ↔ ¬degree s ≤ k from lt_iff_not_ge,
        sq_nonneg]
  exact hsplit.trans (add_le_add (high_degree_tail f hf k) (low_degree_outside f hf hθ k))

lemma mean_const {n : ℕ} (c : ℝ) : mean (fun _ : Cube n => c) = c := Fintype.expect_const c

lemma mean_sum {n : ℕ} {α : Type*} (A : Finset α) (f : α → Cube n → ℝ) :
    mean (fun x => ∑ a ∈ A, f a x) = ∑ a ∈ A, mean (f a) :=
  Finset.expect_sum_comm ..

noncomputable def tailSet {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.succ ∈ S)

@[simp] lemma mem_tailSet {n : ℕ} (S : Finset (Fin (n+1))) (i : Fin n) :
    i ∈ tailSet S ↔ i.succ ∈ S := by simp [tailSet]

lemma supported_cons {n : ℕ} (S : Finset (Fin (n+1))) (b : Bool) (s : Cube n) :
    Supported S (b,s) ↔ (b = true → 0 ∈ S) ∧ Supported (tailSet S) s := by
  constructor
  · intro h
    refine ⟨fun hb => h 0 hb, fun i hi => ?_⟩
    exact (mem_tailSet S i).mpr (h i.succ hi)
  · rintro ⟨h₀, ht⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h₀
    · intro hi
      exact (mem_tailSet S j).mp (ht j hi)

noncomputable def merge : {n : ℕ} → Finset (Fin n) → Cube n → Cube n → Cube n
  | 0, _, x, _ => x
  | _+1, S, (b,x), (c,y) => (if 0 ∈ S then b else c, merge (tailSet S) x y)

lemma bit_merge {n : ℕ} (S : Finset (Fin n)) (x y : Cube n) (i : Fin n) :
    bit (merge S x y) i = if i ∈ S then bit x i else bit y i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [bit, merge]
    · simp [bit, merge, ih]

lemma walsh_merge_mean {n : ℕ} (S : Finset (Fin n)) (s x : Cube n) :
    mean (fun y => walsh s (merge S x y)) = if Supported S s then walsh s x else 0 := by
  induction n with
  | zero =>
    have hs : Supported S s := fun i => Fin.elim0 i
    simp [mean_zero, walsh, hs]
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    obtain ⟨c,x⟩ := x
    rw [mean_succ]
    change (mean (fun y => (if b && (if (0 : Fin (n+1)) ∈ S then c else false) then -1 else 1) *
      walsh s (merge (tailSet S) x y)) +
      mean (fun y => (if b && (if (0 : Fin (n+1)) ∈ S then c else true) then -1 else 1) *
      walsh s (merge (tailSet S) x y))) / 2 = _
    rw [mean_mul, mean_mul, ih]
    simp only [supported_cons, walsh]
    by_cases hs : Supported (tailSet S) s <;> by_cases h₀ : (0 : Fin (n+1)) ∈ S <;>
      cases b <;> cases c <;> simp [hs, h₀]

theorem truncate_eq_coordinate_mean {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) (x : Cube n) :
    truncate S f x = mean (fun y => f (merge S x y)) := by
  rw [truncate, synth_eq_sum]
  calc
    _ = ∑ s, mean (fun y => fourier f s * walsh s (merge S x y)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [mean_mul, walsh_merge_mean]
      split_ifs <;> simp
    _ = mean (fun y => ∑ s, fourier f s * walsh s (merge S x y)) := (mean_sum _ _).symm
    _ = mean (fun y => f (merge S x y)) := by
      apply mean_congr
      intro y
      rw [← synth_eq_sum, synth_fourier]

lemma truncate_bounded {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : ∀ x, |truncate S f x| ≤ 1 := by
  intro x
  rw [truncate_eq_coordinate_mean]
  have ha : |mean (fun y => f (merge S x y))| ≤ mean (fun y => |f (merge S x y)|) :=
    Finset.abs_expect_le _ _
  apply ha.trans
  have h := mean_mono (n:=n) (fun y => hf (merge S x y))
  rwa [mean_const] at h

theorem boolean_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : Cube n → ℝ,
      (∀ x, |f x| ≤ 1) → (∑ i, influence f i) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        mean (fun x => (f x - truncate S f x)^2) < u := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4*L/u)
  have hk₀ : (0:ℝ) < k+1 := by positivity
  have hkL : L/(k+1:ℝ) < u/4 := by
    have he : 4*L < (k:ℝ)*u := (div_lt_iff₀ hu).mp hk
    apply (div_lt_iff₀ hk₀).mpr
    nlinarith
  let θ : ℝ := u / (4 * (4:ℝ)^k * (L+1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : (4:ℝ)^k * θ * (L+1) = u/4 := by
    dsimp [θ]
    field_simp
  have hθL : (4:ℝ)^k * θ * L ≤ u/4 := by
    rw [← hθeq]
    gcongr
    linarith
  refine ⟨⌈L/θ^2⌉₊ + 1, by omega, ?_⟩
  intro n f hf hi
  refine ⟨heavy θ f, ?_, ?_⟩
  · have hc : ((heavy θ f).card:ℝ) ≤ L/θ^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hθ)).mpr
      exact (heavy_card_bound θ f).trans hi
    have hc' := hc.trans (Nat.le_ceil _)
    have hc'' : (heavy θ f).card ≤ ⌈L/θ^2⌉₊ := by exact_mod_cast hc'
    omega
  · have h := boolean_junta_error f hf hθ.le k
    have hd : (∑ i, influence f i)/(k+1:ℝ) ≤ L/(k+1:ℝ) :=
      div_le_div_of_nonneg_right hi hk₀.le
    have hm : (4:ℝ)^k * θ * (∑ i, influence f i) ≤ (4:ℝ)^k * θ * L :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    linarith

end LargeIndependentSets.BooleanJunta

end OAI


end PinnedSource10


/- Source: OAI.Combinatorics.IndependentSets.Reduction.Bits; pinned OAI proof, Apache-2.0. -/
section PinnedSource11

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

def ofBits : {n : ℕ} → (Fin n → Bool) → Cube n
  | 0, _ => ()
  | _+1, x => (x 0, ofBits (fun i => x i.succ))

@[simp] lemma bit_ofBits {n : ℕ} (x : Fin n → Bool) : bit (ofBits x) = x := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [ofBits, bit, Fin.cases_succ, ih]

@[simp] lemma ofBits_bit {n : ℕ} (x : Cube n) : ofBits (bit x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    simp only [ofBits, bit, Fin.cases_zero, Fin.cases_succ, ih]

def bitEquiv (n : ℕ) : Cube n ≃ (Fin n → Bool) where
  toFun := bit
  invFun := ofBits
  left_inv := ofBits_bit
  right_inv := bit_ofBits

lemma bit_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    bit (flip i x) = Function.update (bit x) i (!(bit x i)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    funext j
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [flip, bit]
    · refine Fin.cases ?_ (fun l => ?_) j
      · simp [flip, bit, Function.update_of_ne (Fin.succ_ne_zero k).symm]
      · by_cases h : l = k
        · subst l; simpa [flip, bit] using congrFun (ih k x) k
        · simpa [flip, bit, h, Function.update_of_ne h, Function.update_of_ne (fun he => h (Fin.succ_inj.mp he))] using congrFun (ih k x) l

lemma expect_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : (𝔼 x, f (e x)) = 𝔼 y, f y := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ]
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma mean_bit {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    mean (fun x : Cube n => f (bit x)) = 𝔼 x, f x :=
  expect_equiv (bitEquiv n) f

noncomputable def bitInfluence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (i : ι) : ℝ :=
  𝔼 x, |(f x - f (Function.update x i (!(x i))))/2|

lemma influence_bit {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence (fun x : Cube n => f (bit x)) i = bitInfluence f i := by
  simp only [influence, diff, bit_flip]
  exact mean_bit (fun x => |(f x - f (Function.update x i (!(x i))))/2|)

theorem bits_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : (Fin n → Bool) → ℝ,
      (∀ x, |f x| ≤ 1) → (∑ i, bitInfluence f i) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧ ∃ g : (Fin n → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (f x - g x)^2) < u := by
  obtain ⟨J,hJ,h⟩ := boolean_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro n f hf hI
  let f' : Cube n → ℝ := fun x => f (bit x)
  have hI' : (∑ i, influence f' i) ≤ L := by simpa only [f', influence_bit] using hI
  obtain ⟨S,hS,he⟩ := h n f' (fun x => hf _) hI'
  let g : (Fin n → Bool) → ℝ := fun x => truncate S f' (ofBits x)
  refine ⟨S,hS,g,?_,?_,?_⟩
  · intro x
    exact truncate_bounded S f' (fun x => hf _) _
  · intro x y hxy
    apply truncate_depends
    simpa only [bit_ofBits] using hxy
  · have heq : (𝔼 x, (f x-g x)^2) = mean (fun x : Cube n => (f' x-truncate S f' x)^2) := by
      rw [← mean_bit]
      simp only [f', g, ofBits_bit]
    rwa [heq]

def reindexBits {ι κ : Type*} (e : ι ≃ κ) : (κ → Bool) ≃ (ι → Bool) where
  toFun := fun x i => x (e i)
  invFun := fun x j => x (e.symm j)
  left_inv := by intro x; funext j; simp
  right_inv := by intro x; funext i; simp

lemma reindexBits_update {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (x : κ → Bool) (i : ι) :
    reindexBits e (Function.update x (e i) (!(x (e i)))) =
      Function.update (reindexBits e x) i (!(reindexBits e x i)) := by
  funext j
  by_cases h : j = i
  · subst j; simp [reindexBits]
  · simp [reindexBits, Function.update_of_ne h, Function.update_of_ne (e.injective.ne h)]

lemma bitInfluence_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (ι → Bool) → ℝ) (i : ι) :
    bitInfluence (fun x => f (reindexBits e x)) (e i) = bitInfluence f i := by
  simp only [bitInfluence, reindexBits_update]
  exact expect_equiv (reindexBits e) (fun x => |(f x - f (Function.update x i (!(x i))))/2|)

theorem arbitrary_bits_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ f : (ι → Bool) → ℝ, (∀ x, |f x| ≤ 1) → (∑ i, bitInfluence f i) ≤ L →
      ∃ S : Finset ι, S.card ≤ J ∧ ∃ g : (ι → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (f x - g x)^2) < u := by
  obtain ⟨J,hJ,h⟩ := bits_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hI
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f' : (Fin (Fintype.card ι) → Bool) → ℝ := fun x => f (reindexBits e x)
  have hI' : (∑ i, bitInfluence f' i) ≤ L := by
    rw [← e.sum_comp (fun j => bitInfluence f' j)]
    simpa only [f', bitInfluence_reindex] using hI
  obtain ⟨S,hS,g,hg,hdep,he⟩ := h (Fintype.card ι) f' (fun x => hf _) hI'
  let T : Finset ι := S.map e.symm.toEmbedding
  let g' : (ι → Bool) → ℝ := fun x => g ((reindexBits e).symm x)
  refine ⟨T, by simpa [T] using hS, g', (fun x => hg _), ?_, ?_⟩
  · intro x y hxy
    apply hdep
    intro j hj
    exact hxy (e.symm j) (Finset.mem_map.mpr ⟨j,hj,rfl⟩)
  · have heq : (𝔼 x, (f x-g' x)^2) = 𝔼 x, (f' x-g x)^2 := by
      rw [← expect_equiv (reindexBits e)]
      simp only [g', Equiv.symm_apply_apply, f']
    rwa [heq]

end LargeIndependentSets.BooleanJunta

end OAI


end PinnedSource11


/- Source: OAI.Combinatorics.IndependentSets.Repetition.CayleySampling; pinned OAI proof, Apache-2.0. -/
section PinnedSource12

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem card_boolean_split [Fintype V] (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    Fintype.card V = 2 * Fintype.card (FalseFiber χ) := by
  simpa using Fintype.card_congr (booleanSplitEquiv χ flip hflip hχ)

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end IndependentSetsGames.Foundations.PCP.CayleySampling
end

end OAI


end PinnedSource12


/- Source: OAI.Combinatorics.IndependentSets.Fourier.Walsh2; pinned OAI proof, Apache-2.0. -/
section PinnedSource13

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.CayleySampling
open scoped BigOperators
open Finset
open IndependentSetsGames.Foundations.Hastad
variable {V D : Type*}

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

theorem expect_walsh_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → ℝ) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => walsh s (g d))) =
      𝔼 b : D → Bool, F (fun d => bitSign (b d)) := by
  simpa only [AssignmentTester.bitSign_parity] using
    expect_parity_samples s hs (fun b => F (fun d => bitSign (b d)))

theorem expect_walsh_mean (s : Cube I) (hs : s ≠ fun _ => false) (F : ℝ → ℝ) :
    (𝔼 g : D → Cube I, F (𝔼 d, walsh s (g d))) =
      𝔼 b : D → Bool, F (𝔼 d, bitSign (b d)) :=
  expect_walsh_samples s hs (fun z => F (𝔼 d, z d))

end IndependentSetsGames.Foundations.PCP.CayleySampling

end

end OAI


end PinnedSource13


/- Source: OAI.Combinatorics.IndependentSets.Expansion.CayleyTailCount; pinned OAI proof, Apache-2.0. -/
section PinnedSource14

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in

theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

private theorem ratio_le_of_weight (c m : ℕ)
    (h : c * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    (c : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : (c : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

theorem fixed_parameters : 3 * (448 + 2) ≤ 16384 ∧ 4 * 16384 = 2 ^ 16 := by
  norm_num

theorem fixed_union_bound :
    (2 : ℝ) ^ 448 * (2 * (2 / 3 : ℝ) ^ 16384) ≤ 1 / 2 :=
  union_bound_le_half 448 16384 fixed_parameters.1

theorem seventh_power_size : (2 : ℕ) ^ 448 = (((2 : ℕ) ^ 16) ^ 7) ^ 4 := by
  rw [← pow_mul, ← pow_mul]

theorem seventh_power_abs_le {a : ℝ} (ha : |a| ≤ 1 / 2) : |a ^ 7| ≤ 1 / 128 := by
  rw [abs_pow]
  calc
    |a| ^ 7 ≤ (1 / 2 : ℝ) ^ 7 := pow_le_pow_left₀ (abs_nonneg a) ha 7
    _ = 1 / 128 := by norm_num

end IndependentSetsGames.Foundations.PCP.CayleyTailCount

end OAI


end PinnedSource14


/- Source: OAI.Combinatorics.IndependentSets.Expansion.SpectralReturn; pinned OAI proof, Apache-2.0. -/
section PinnedSource15

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end
end IndependentSetsGames.Foundations.PCP.SpectralReturn

end OAI


end PinnedSource15


/- Source: OAI.Combinatorics.IndependentSets.Expansion.CayleySpectral; pinned OAI proof, Apache-2.0. -/
section PinnedSource16

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open IndependentSetsGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

theorem cubeXor_assoc (x y z : Cube I) :
    cubeXor (cubeXor x y) z = cubeXor x (cubeXor y z) := by
  funext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [cubeXor, hx, hy, hz]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

theorem wordEnd_eq_powerGenerators (g : D → Cube I) (n : Nat)
    (x : Cube I) (p : Fin n → D) :
    wordEnd (cayleyGraph g) n x p = cubeXor x (powerGenerators g n p) := by
  induction n generalizing x with
  | zero => simp [wordEnd, powerGenerators]
  | succ n ih =>
    change wordEnd (cayleyGraph g) n (cubeXor x (g (p 0))) (fun j => p j.succ) =
      cubeXor x (cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ)))
    rw [ih, cubeXor_assoc]

variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

theorem cayleyAverage_walsh (g : D → Cube I) (s x : Cube I) :
    cayleyAverage g (walsh s) x = eigenvalue g s * walsh s x := by
  unfold cayleyAverage
  simp only [cayleyGraph_rot, walsh_xor]
  rw [← Finset.mul_expect]
  rw [mul_comm]
  rfl

theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem power_port_card (n : Nat) :
    Fintype.card (Fin n → D) = Fintype.card D ^ n := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem seven_power_port_card :
    Fintype.card (Fin 7 → Fin (2 ^ 16)) = (2 ^ 16) ^ 7 := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

theorem sevenStep_halfCertificate (g : D → Cube I)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ)) :
    SpectralReturn.SpectralCertificate (cayleyGraph (powerGenerators g 7))
      ((1 / 2 : ℝ) ^ 7) := by
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact power_eigenvalue_bound g (1 / 2) (by norm_num) hbias 7 s hs

end IndependentSetsGames.Foundations.PCP.CayleySpectral
end

end OAI


end PinnedSource16


/- Source: OAI.Combinatorics.IndependentSets.Expansion.Expanders; pinned OAI proof, Apache-2.0. -/
section PinnedSource17

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.Expanders

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad
open CayleySpectral

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, if_pos hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, if_neg hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, if_neg hs, if_pos hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

def baseDimension : Nat := 448
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · simpa only [baseDimension, initialDegree, basePower] using CayleyTailCount.seventh_power_size
  · norm_num [basePower]

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end IndependentSetsGames.Foundations.PCP.Expanders
end
namespace IndependentSetsGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

end IndependentSetsGames.Foundations.PCP.GraphTransport

end OAI


end PinnedSource17


/- Source: OAI.Combinatorics.IndependentSets.Expansion.Finite; pinned OAI proof, Apache-2.0. -/
section PinnedSource18

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTransport
open PoweringWalks SpectralReturn
variable {V W D E : Type*}

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h

end IndependentSetsGames.Foundations.PCP.GraphTransport
namespace IndependentSetsGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

theorem natCard_square_ports : Nat.card (D × D) = Nat.card D ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_square_edges :
    Nat.card (Edge V (D × D)) = Nat.card V * Nat.card D ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

theorem natCard_zigzag_vertices :
    Nat.card (V × D) = Nat.card V * Nat.card D := Nat.card_prod V D

theorem natCard_zigzag_ports : Nat.card (E × E) = Nat.card E ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_zigzag_edges :
    Nat.card (Edge (V × D) (E × E)) =
      Nat.card V * Nat.card D * Nat.card E ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

noncomputable section

def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end

end IndependentSetsGames.Foundations.PCP.ZigzagGraphs

end OAI


end PinnedSource18


/- Source: OAI.Combinatorics.IndependentSets.Expansion.ZigzagSpectral; pinned OAI proof, Apache-2.0. -/
section PinnedSource19

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_projection_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (projection f) ≤ energy f := by
  have h := projection_energy_decomposition f
  have hn := energy_nonnegative (centered f)
  linarith

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end IndependentSetsGames.Foundations.PCP.ZigzagSpectral

end OAI


end PinnedSource19


/- Source: OAI.Combinatorics.IndependentSets.Expansion.ExpanderFamily; pinned OAI proof, Apache-2.0. -/
section PinnedSource20

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

noncomputable def baseOnCloud : PortGraph CloudPort BasePort :=
  GraphTransport.reindex (Classical.choose exists_baseGraph) baseVertexEquiv (Equiv.refl _)

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

def graph (H : PortGraph CloudPort BasePort) : (n : Nat) → PortGraph (Vertex n) Port
  | 0 => { rot := Equiv.refl _, rot_involutive := fun _ => rfl }
  | n + 1 => ZigzagGraphs.zigzag (ZigzagGraphs.square (graph H n)) H

theorem graph_certificate (H : PortGraph CloudPort BasePort)
    (hH : SpectralCertificate H (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph H n) (1 / 2 : ℝ) := by
  induction n with
  | zero =>
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro f hf
    have hm : mean f = f () := by
      change mean (fun x : Unit => f x) = f ()
      have hfun : (fun x : Unit => f x) = fun _ : Unit => f () := by
        funext x
        cases x
        rfl
      rw [hfun, mean_const]
    have hz : f = fun _ => 0 := by
      funext x
      cases x
      exact hm.symm.trans hf
    rw [hz]
    simp [energy, mean, averagingOperator]
  | succ n ih =>
    exact ZigzagSpectral.square_zigzag_halfCertificate (graph H n) H ih hH

noncomputable def family (n : Nat) : PortGraph (Vertex n) Port := graph baseOnCloud n

theorem family_certificate (n : Nat) : SpectralCertificate (family n) (1 / 2 : ℝ) :=
  graph_certificate baseOnCloud baseOnCloud_certificate n

theorem card_vertex (n : Nat) : Fintype.card (Vertex n) = growth ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × CloudPort) = growth ^ (n + 1)
    rw [Fintype.card_prod, ih, card_cloudPort, pow_succ]

def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

theorem padded_family_size {k : Nat} (hk : 0 < k) :
    k ≤ Fintype.card (Vertex (level k)) ∧
      Fintype.card (Vertex (level k)) ≤ growth * k := by
  rw [card_vertex]
  exact ⟨le_size k, size_le_mul hk⟩

end IndependentSetsGames.Foundations.PCP.ExpanderFamily
namespace IndependentSetsGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

theorem paddedSize_of_pos {k : Nat} (hk : 0 < k) :
    paddedSize k = ExpanderFamily.size k := by
  simp only [paddedSize, if_neg (Nat.ne_of_gt hk)]

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, if_neg hk]
    exact ExpanderFamily.le_size k

theorem paddedSize_le_mul (k : Nat) : paddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, if_neg hk]
    exact ExpanderFamily.size_le_mul (Nat.pos_of_ne_zero hk)

def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

end IndependentSetsGames.Foundations.PCP.CloudPadding

end OAI


end PinnedSource20


#print axioms OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.family_certificate
#print axioms OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.card_vertex
#print axioms OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.growth_gt_one

/- Source: OAI.Geometry.HyperbolicGroups.TreeCentroid; pinned OAI proof, Apache-2.0. -/
section PinnedTreeSource0

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset
variable {V : Type*} [Fintype V]

/-- The side of an oriented tree edge towards its second endpoint. -/
def treeBranch (G : SimpleGraph V) (v w : V) : Finset V :=
  Finset.univ.filter (fun x => G.dist x w < G.dist x v)

/-- A finite weighted tree has a centroid: each branch at the selected vertex
has at most half the total weight. This is a genuine weighted-tree theorem,
not a planar-separator assumption. -/
theorem weighted_tree_centroid (G : SimpleGraph V) (hG : G.IsTree) (weight : V → ℝ) :
    ∃ v : V, ∀ w : V, G.Adj v w →
      2 * ∑ x ∈ treeBranch G v w, weight x ≤ ∑ x : V, weight x := by
  let potential : V → ℝ := fun v => ∑ x : V, weight x * G.dist x v
  have : Nonempty V := hG.connected.nonempty
  obtain ⟨v, _, hmin⟩ := Finset.exists_min_image Finset.univ potential Finset.univ_nonempty
  refine ⟨v,?_⟩
  intro w hadj
  have hid : potential w + 2 * ∑ x ∈ treeBranch G v w, weight x =
      potential v + ∑ x : V, weight x := by
    unfold potential treeBranch
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases hG.dist_eq_dist_add_one_of_adj x hadj with h | h
    · have hx : G.dist x w < G.dist x v := by omega
      rw [if_pos hx,h,Nat.cast_add,Nat.cast_one]
      ring
    · have hx : ¬G.dist x w < G.dist x v := by omega
      rw [if_neg hx,h,Nat.cast_add,Nat.cast_one]
      ring
  have hle := hmin w (Finset.mem_univ w)
  linarith

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI


end PinnedTreeSource0

/- Source: OAI.Geometry.HyperbolicGroups.TreeCentroidCut; pinned OAI proof, Apache-2.0. -/
section PinnedTreeSource1

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset SimpleGraph
variable {V : Type*}

lemma tree_path_length_eq_dist {G : SimpleGraph V} (hG : G.IsTree) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) : p.length = G.dist x y := by
  obtain ⟨q,hq,hql⟩ := hG.connected.exists_path_of_dist x y
  have heq := hG.isAcyclic.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨q,hq⟩
  have hwalk : p = q := congrArg Subtype.val heq
  rwa [hwalk]

variable [Fintype V] [DecidableEq V]

lemma treeBranch_of_avoiding_walk {G : SimpleGraph V} (hG : G.IsTree) {v w x : V}
    (hadj : G.Adj v w) (p : G.Walk x w) (havoid : v ∉ p.support) :
    x ∈ treeBranch G v w := by
  let q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hv : v ∉ q.support := fun h => havoid (p.support_bypass_subset_support h)
  obtain ⟨r,hr,hrl⟩ := hG.connected.exists_path_of_dist x v
  have hw : w ∈ r.support :=
    hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hr hq hadj hv
  have hid := hG.isAcyclic.path_concat hq hr hadj.symm hw
  have hql := tree_path_length_eq_dist hG q hq
  rw [hid,Walk.length_concat,hql] at hrl
  simp only [treeBranch,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

/-- The weighted centroid really separates the tree: every connected set
remaining after removing it has at most half the total weight. All weights
are on actual vertices and no combinatorial separation is hypothesized. -/
theorem weighted_tree_vertex_separator (G : SimpleGraph V) (hG : G.IsTree)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) :
    ∃ v : V, ∀ S : Finset V, v ∉ S → (G.induce (S : Set V)).Preconnected →
      2 * ∑ x ∈ S, weight x ≤ ∑ x : V, weight x := by
  obtain ⟨v,hv⟩ := weighted_tree_centroid G hG weight
  refine ⟨v,?_⟩
  intro S hvS hconn
  by_cases hS : S.Nonempty
  · obtain ⟨x,hx⟩ := hS
    obtain ⟨p,hp,_⟩ := hG.connected.exists_path_of_dist v x
    cases p with
    | nil => exact (hvS hx).elim
    | @cons v w x hadj q =>
      have havoid : v ∉ q.support := by
        have hnodup := hp.support_nodup
        exact (List.nodup_cons.mp (by simpa only [Walk.support_cons] using hnodup)).1
      have hsub : S ⊆ treeBranch G v w := by
        intro y hy
        obtain ⟨r⟩ := hconn ⟨y,hy⟩ ⟨x,hx⟩
        let r' := r.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
        have hr' : v ∉ r'.support := by
          intro h
          rw [Walk.support_map] at h
          obtain ⟨z,_,hz⟩ := List.mem_map.mp h
          exact hvS (hz ▸ z.property)
        apply treeBranch_of_avoiding_walk hG hadj (r'.append q.reverse)
        intro h
        have hh := (Walk.mem_support_append_iff r' q.reverse).mp h
        rcases hh with hh | hh
        · exact hr' hh
        · exact havoid (by simpa using hh)
      exact le_trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw x)) (by norm_num)) (hv w hadj)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty,mul_zero]
    exact Finset.sum_nonneg (fun x _ => hw x)

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI


end PinnedTreeSource1

/- Source: OAI.Geometry.HyperbolicGroups.TreeCentroidComponents; pinned OAI proof, Apache-2.0. -/
section PinnedTreeSource2

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
open SimpleGraph
variable {V : Type*}

lemma deleteIncidence_reachable_center_iff (G : SimpleGraph V) (v w : V) :
    (G.deleteIncidenceSet v).Reachable v w ↔ v = w := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact ((deleteIncidenceSet_adj.mp h).2.1 rfl).elim
  · rintro rfl; exact .rfl

lemma deleteIncidence_center_component_iff (G : SimpleGraph V) (v w : V) :
    (G.deleteIncidenceSet v).connectedComponentMk w =
      (G.deleteIncidenceSet v).connectedComponentMk v ↔ w = v := by
  constructor
  · intro h
    exact ((deleteIncidence_reachable_center_iff G v w).mp
      (ConnectedComponent.exact h.symm)).symm
  · rintro rfl; rfl

variable [Fintype V] [DecidableEq V]

/-- Actual components after deleting a weighted tree centroid carry at most
half the total mass. The isolated centroid component is explicitly excluded. -/
theorem weighted_tree_component_separator (G : SimpleGraph V) (hG : G.IsTree)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) :
    ∃ v : V, ∀ C : (G.deleteIncidenceSet v).ConnectedComponent,
      C ≠ (G.deleteIncidenceSet v).connectedComponentMk v →
      2 * ∑ x ∈ C.supp.toFinset, weight x ≤ ∑ x : V, weight x := by
  classical
  obtain ⟨v,hv⟩ := weighted_tree_vertex_separator G hG weight hw
  refine ⟨v,?_⟩
  intro C hC
  have hnot : v ∉ C.supp := fun h => hC h.symm
  apply hv C.supp.toFinset
  · simpa only [Set.mem_toFinset] using hnot
  · have hc := C.connected_toSimpleGraph.preconnected
    change ((G.deleteIncidenceSet v).induce C.supp).Preconnected at hc
    rw [G.induce_deleteIncidenceSet_of_notMem hnot] at hc
    have he : (C.supp.toFinset : Set V) = C.supp := Set.coe_toFinset C.supp
    rw [he]
    exact hc

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI


end PinnedTreeSource2

/- Source: OAI.Combinatorics.TreewidthL1.Model; only the exact finite
bag-decomposition definition is retained, pinned OAI source, Apache-2.0. -/
namespace OAI.BoundedTreewidthL1
universe u_1
variable {V : Type u_1} (G : SimpleGraph V)

def HasTreeDecomposition [DecidableEq V] (k : ℕ) : Prop :=
  ∃ n : ℕ, ∃ T : SimpleGraph (Fin n), ∃ bag : Fin n → Finset V,
    T.IsTree ∧
    (∀ v : V, ∃ t, v ∈ bag t) ∧
    (∀ u v : V, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
    (∀ v : V, (T.induce {t | v ∈ bag t}).Connected) ∧
    (∀ t, (bag t).card ≤ k)

end OAI.BoundedTreewidthL1

#print axioms OAI.HyperbolicObstruction.PlanarRecursion.weighted_tree_component_separator
