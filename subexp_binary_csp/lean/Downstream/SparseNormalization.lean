import Downstream.FiniteInput

set_option autoImplicit false

/-! Exact-graph normalization of sparse binary tuple-list constraints.
Distinct scopes are oriented and intersected, including reversed duplicates.
Repeated-variable constraints are absorbed at both endpoints of every incident
edge. Equivalence requires the explicitly stated nonisolation condition.
All raw query routines use finite natural-number lists and have PolyT proofs.
This is not yet a complete table constructor/parser or a support-pruning proof;
tabulating a compactly specified huge domain is not polynomial in tuple length. -/
namespace CSPConsequence.SparseNormalization
open Groundwork

abbrev Constraint := ℕ × (ℕ × List (ℕ × ℕ))
abbrev SparseInput := List Constraint

def tupleBit (c : Constraint) (x y : ℕ) : Bool :=
  c.2.2.any (fun p => decide (p.1 = x ∧ p.2 = y))

def edgeAt (cs : SparseInput) (a b : ℕ) : Bool :=
  decide (a ≠ b) && cs.any (fun c =>
    decide ((c.1 = a ∧ c.2.1 = b) ∨ (c.1 = b ∧ c.2.1 = a)))

def unaryAt (cs : SparseInput) (a x : ℕ) : Bool :=
  cs.all (fun c => if c.1 = c.2.1 ∧ c.1 = a then tupleBit c x x else true)

def pairAt (cs : SparseInput) (a b x y : ℕ) : Bool :=
  cs.all (fun c =>
    (if c.1 = a ∧ c.2.1 = b then tupleBit c x y else true) &&
    (if c.1 = b ∧ c.2.1 = a then tupleBit c y x else true))

def relationAt (cs : SparseInput) (a b x y : ℕ) : Bool :=
  unaryAt cs a x && unaryAt cs b y && pairAt cs a b x y

theorem tupleBit_iff (c : Constraint) (x y : ℕ) :
    tupleBit c x y = true ↔ (x,y) ∈ c.2.2 := by
  simp only [tupleBit,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨p,hp,hx,hy⟩
    have he : p = (x,y) := Prod.ext hx hy
    simpa only [he] using hp
  · intro h
    exact ⟨(x,y),h,rfl,rfl⟩

theorem edgeAt_iff (cs : SparseInput) (a b : ℕ) :
    edgeAt cs a b = true ↔ a ≠ b ∧ ∃ c ∈ cs,
      (c.1 = a ∧ c.2.1 = b) ∨ (c.1 = b ∧ c.2.1 = a) := by
  simp [edgeAt]

theorem edgeAt_symmetric (cs : SparseInput) (a b : ℕ) : edgeAt cs a b = edgeAt cs b a := by
  simp only [edgeAt,ne_comm,or_comm]

theorem unaryAt_iff (cs : SparseInput) (a x : ℕ) :
    unaryAt cs a x = true ↔
      ∀ c ∈ cs, c.1 = c.2.1 → c.1 = a → (x,x) ∈ c.2.2 := by
  simp only [unaryAt,List.all_eq_true]
  constructor
  · intro h c hc he ha
    have ht := h c hc
    rw [if_pos ⟨he,ha⟩] at ht
    exact (tupleBit_iff c x x).mp ht
  · intro h c hc
    split_ifs with he
    · exact (tupleBit_iff c x x).mpr (h c hc he.1 he.2)
    · rfl

theorem pairAt_iff (cs : SparseInput) (a b x y : ℕ) :
    pairAt cs a b x y = true ↔ ∀ c ∈ cs,
      ((c.1 = a ∧ c.2.1 = b) → (x,y) ∈ c.2.2) ∧
      ((c.1 = b ∧ c.2.1 = a) → (y,x) ∈ c.2.2) := by
  simp only [pairAt,List.all_eq_true,Bool.and_eq_true]
  constructor
  · intro h c hc
    constructor
    · intro he
      have ht := (h c hc).1
      rw [if_pos he] at ht
      exact (tupleBit_iff c x y).mp ht
    · intro he
      have ht := (h c hc).2
      rw [if_pos he] at ht
      exact (tupleBit_iff c y x).mp ht
  · intro h c hc
    constructor
    · split_ifs with he
      · exact (tupleBit_iff c x y).mpr ((h c hc).1 he)
      · rfl
    · split_ifs with he
      · exact (tupleBit_iff c y x).mpr ((h c hc).2 he)
      · rfl

theorem relationAt_iff (cs : SparseInput) (a b x y : ℕ) :
    relationAt cs a b x y = true ↔
      unaryAt cs a x = true ∧ unaryAt cs b y = true ∧ pairAt cs a b x y = true := by
  simp only [relationAt,Bool.and_eq_true,and_assoc]

def normalized (k D : ℕ) (cs : SparseInput) : Instance k D where
  edge a b := edgeAt cs a.val b.val
  symmetric a b := edgeAt_symmetric cs a.val b.val
  relation a b x y := relationAt cs a.val b.val x.val y.val

def extend {k D : ℕ} (z : Fin k → Fin D) (a : ℕ) : ℕ :=
  if h : a < k then (z ⟨a,h⟩).val else 0

theorem extend_fin {k D : ℕ} (z : Fin k → Fin D) (a : Fin k) : extend z a.val = (z a).val := by
  simp [extend,a.isLt]

def ScopeBounded (k : ℕ) (cs : SparseInput) : Prop :=
  ∀ c ∈ cs, c.1 < k ∧ c.2.1 < k

def RawValid {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D) : Prop :=
  ∀ c ∈ cs, (extend z c.1,extend z c.2.1) ∈ c.2.2

def Nonisolated (k : ℕ) (cs : SparseInput) : Prop :=
  ∀ a : Fin k, ∃ b : Fin k, edgeAt cs a.val b.val = true

theorem raw_implies_normalized {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D)
    (hz : RawValid cs z) : (normalized k D cs).valid z := by
  intro a b _ _
  change relationAt cs a.val b.val (z a).val (z b).val = true
  apply (relationAt_iff cs a.val b.val (z a).val (z b).val).mpr
  refine ⟨?_,?_,?_⟩
  · apply (unaryAt_iff cs a.val (z a).val).mpr
    intro c hc he ha
    have hb : c.2.1 = a.val := he.symm.trans ha
    simpa only [ha,hb,extend_fin] using hz c hc
  · apply (unaryAt_iff cs b.val (z b).val).mpr
    intro c hc he hb
    have ha : c.2.1 = b.val := he.symm.trans hb
    simpa only [hb,ha,extend_fin] using hz c hc
  · apply (pairAt_iff cs a.val b.val (z a).val (z b).val).mpr
    intro c hc
    constructor
    · rintro ⟨ha,hb⟩
      simpa only [ha,hb,extend_fin] using hz c hc
    · rintro ⟨hb,ha⟩
      simpa only [hb,ha,extend_fin] using hz c hc

theorem normalized_unary {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D)
    (hni : Nonisolated k cs) (hz : (normalized k D cs).valid z) (a : Fin k) :
    unaryAt cs a.val (z a).val = true := by
  obtain ⟨b,hb⟩ := hni a
  have hab : a ≠ b := by
    intro h
    exact ((edgeAt_iff cs a.val b.val).mp hb).1 (congrArg Fin.val h)
  rcases lt_or_gt_of_ne hab with h | h
  · have hr := hz a b h hb
    exact ((relationAt_iff cs a.val b.val (z a).val (z b).val).mp hr).1
  · have he : edgeAt cs b.val a.val = true := (edgeAt_symmetric cs b.val a.val).trans hb
    have hr := hz b a h he
    exact ((relationAt_iff cs b.val a.val (z b).val (z a).val).mp hr).2.1

theorem normalized_implies_raw {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D)
    (hscope : ScopeBounded k cs) (hni : Nonisolated k cs)
    (hz : (normalized k D cs).valid z) : RawValid cs z := by
  intro c hc
  let a : Fin k := ⟨c.1,(hscope c hc).1⟩
  let b : Fin k := ⟨c.2.1,(hscope c hc).2⟩
  have ha : c.1 = a.val := rfl
  have hb : c.2.1 = b.val := rfl
  have hext : (extend z c.1,extend z c.2.1) = ((z a).val,(z b).val) := by
    rw [ha,hb,extend_fin,extend_fin]
  rw [hext]
  by_cases he : a = b
  · have hu := (unaryAt_iff cs a.val (z a).val).mp (normalized_unary cs z hni hz a) c hc
    have hsame : c.1 = c.2.1 := by rw [ha,hb,he]
    simpa only [he] using hu hsame ha
  · rcases lt_or_gt_of_ne he with h | h
    · have hedge : edgeAt cs a.val b.val = true := (edgeAt_iff cs a.val b.val).mpr
        ⟨(fun heq => he (Fin.ext heq)),c,hc,Or.inl ⟨ha,hb⟩⟩
      have hr := hz a b h hedge
      exact (((pairAt_iff cs a.val b.val (z a).val (z b).val).mp
        ((relationAt_iff cs a.val b.val (z a).val (z b).val).mp hr).2.2) c hc).1 ⟨ha,hb⟩
    · have hedge : edgeAt cs b.val a.val = true := (edgeAt_iff cs b.val a.val).mpr
        ⟨(fun heq => he (Fin.ext heq.symm)),c,hc,Or.inr ⟨ha,hb⟩⟩
      have hr := hz b a h hedge
      exact (((pairAt_iff cs b.val a.val (z b).val (z a).val).mp
        ((relationAt_iff cs b.val a.val (z b).val (z a).val).mp hr).2.2) c hc).2 ⟨ha,hb⟩

theorem valid_iff {k D : ℕ} (cs : SparseInput) (hscope : ScopeBounded k cs)
    (hni : Nonisolated k cs) (z : Fin k → Fin D) :
    (normalized k D cs).valid z ↔ RawValid cs z :=
  ⟨normalized_implies_raw cs z hscope hni,raw_implies_normalized cs z⟩

noncomputable def rawCount {k D : ℕ} (cs : SparseInput) : ℕ := by
  classical
  exact (Finset.univ.filter (fun z : Fin k → Fin D => RawValid cs z)).card

theorem count_eq {k D : ℕ} (cs : SparseInput) (hscope : ScopeBounded k cs)
    (hni : Nonisolated k cs) : (normalized k D cs).count = rawCount (k:=k) (D:=D) cs := by
  classical
  unfold Instance.count rawCount
  congr 1
  ext z
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,valid_iff cs hscope hni]

@[fun_prop] theorem tupleBit_polyT :
    PolyT (fun p : Constraint × (ℕ × ℕ) => tupleBit p.1 p.2.1 p.2.2) := by
  unfold tupleBit
  fun_prop

@[fun_prop] theorem edgeAt_polyT :
    PolyT (fun p : SparseInput × (ℕ × ℕ) => edgeAt p.1 p.2.1 p.2.2) := by
  unfold edgeAt
  fun_prop

@[fun_prop] theorem unaryAt_polyT :
    PolyT (fun p : SparseInput × (ℕ × ℕ) => unaryAt p.1 p.2.1 p.2.2) := by
  unfold unaryAt
  fun_prop

@[fun_prop] theorem pairAt_polyT :
    PolyT (fun p : SparseInput × (ℕ × ℕ × ℕ × ℕ) => pairAt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold pairAt
  fun_prop

@[fun_prop] theorem relationAt_polyT :
    PolyT (fun p : SparseInput × (ℕ × ℕ × ℕ × ℕ) => relationAt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold relationAt
  fun_prop

#print axioms valid_iff
#print axioms count_eq
#print axioms tupleBit_polyT
#print axioms edgeAt_polyT
#print axioms unaryAt_polyT
#print axioms pairAt_polyT
#print axioms relationAt_polyT
end CSPConsequence.SparseNormalization
