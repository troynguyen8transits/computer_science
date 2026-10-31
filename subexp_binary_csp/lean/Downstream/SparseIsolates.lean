import Downstream.SparseRelabelPreparation
import Downstream.TableRefinement

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Global decision normalization without a nonisolation promise. Isolated
variables' self-constraints are checked separately by a polynomial scan of the
computed support. No primal edge is added or removed. -/

namespace CSPConsequence.SparseIsolates

open Groundwork SparseNormalization

def Incident {k : ℕ} (cs : SparseInput) (a : Fin k) : Prop :=
  ∃ b : Fin k, edgeAt cs a.val b.val = true

def Feasible {k D M : ℕ} (cs : SparseInput) (d : Fin M → Fin D) : Prop :=
  ∀ a : Fin k, ¬Incident cs a → ∃ x : Fin M, unaryAt cs a.val (d x).val = true

theorem raw_unary {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D)
    (hz : RawValid cs z) (a : Fin k) : unaryAt cs a.val (z a).val = true := by
  apply (unaryAt_iff cs a.val (z a).val).mpr
  intro c hc he ha
  have hb : c.2.1 = a.val := he.symm.trans ha
  simpa only [ha,hb,extend_fin] using hz c hc

theorem incident_unary {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D)
    (hz : (normalized k D cs).valid z) (a : Fin k) (hi : Incident cs a) :
    unaryAt cs a.val (z a).val = true := by
  obtain ⟨b,hb⟩ := hi
  have hab : a ≠ b := fun h => ((edgeAt_iff cs a.val b.val).mp hb).1 (congrArg Fin.val h)
  rcases lt_or_gt_of_ne hab with h | h
  · exact ((relationAt_iff cs a.val b.val (z a).val (z b).val).mp (hz a b h hb)).1
  · have he : edgeAt cs b.val a.val = true := (edgeAt_symmetric cs b.val a.val).trans hb
    exact ((relationAt_iff cs b.val a.val (z b).val (z a).val).mp (hz b a h he)).2.1

/-- Adapt SparseNormalization.normalized_implies_raw: an explicit unary
certificate replaces its global nonisolation premise. -/
theorem normalized_unary_raw {k D : ℕ} (cs : SparseInput) (z : Fin k → Fin D)
    (hs : ScopeBounded k cs) (hu : ∀ a, unaryAt cs a.val (z a).val = true)
    (hz : (normalized k D cs).valid z) : RawValid cs z := by
  intro c hc
  let a : Fin k := ⟨c.1,(hs c hc).1⟩
  let b : Fin k := ⟨c.2.1,(hs c hc).2⟩
  have ha : c.1 = a.val := rfl
  have hb : c.2.1 = b.val := rfl
  rw [ha,hb,extend_fin,extend_fin]
  by_cases he : a = b
  · have hh := (unaryAt_iff cs a.val (z a).val).mp (hu a) c hc
    have hsame : c.1 = c.2.1 := by rw [ha,hb,he]
    simpa only [he] using hh hsame ha
  · rcases lt_or_gt_of_ne he with h | h
    · have hedge : edgeAt cs a.val b.val = true := (edgeAt_iff cs a.val b.val).mpr
        ⟨(fun heq => he (Fin.ext heq)),c,hc,Or.inl ⟨ha,hb⟩⟩
      exact (((pairAt_iff cs a.val b.val (z a).val (z b).val).mp
        ((relationAt_iff cs a.val b.val (z a).val (z b).val).mp (hz a b h hedge)).2.2) c hc).1 ⟨ha,hb⟩
    · have hedge : edgeAt cs b.val a.val = true := (edgeAt_iff cs b.val a.val).mpr
        ⟨(fun heq => he (Fin.ext heq.symm)),c,hc,Or.inr ⟨ha,hb⟩⟩
      exact (((pairAt_iff cs b.val a.val (z b).val (z a).val).mp
        ((relationAt_iff cs b.val a.val (z b).val (z a).val).mp (hz b a h hedge)).2.2) c hc).2 ⟨ha,hb⟩

theorem decision_image_iff {k D M : ℕ} (cs : SparseInput) (d : Fin M → Fin D)
    (hs : ScopeBounded k cs) :
    (∃ w : Fin k → Fin M, RawValid cs (fun a => d (w a))) ↔
      Feasible (k:=k) cs d ∧ ∃ z : Fin k → Fin M,
        (normalized k D cs).valid (fun a => d (z a)) := by
  classical
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨fun a _ => ⟨z a,raw_unary cs _ hz a⟩,z,raw_implies_normalized cs _ hz⟩
  · rintro ⟨hi,z,hz⟩
    let w : Fin k → Fin M := fun a =>
      if h : Incident cs a then z a else Classical.choose (hi a h)
    have hu : ∀ a, unaryAt cs a.val (d (w a)).val = true := by
      intro a
      by_cases h : Incident cs a
      · simpa only [w,dif_pos h] using incident_unary cs _ hz a h
      · simpa only [w,dif_neg h] using Classical.choose_spec (hi a h)
    have hw : (normalized k D cs).valid (fun a => d (w a)) := by
      intro a b hab he
      have ha : Incident cs a := ⟨b,he⟩
      have hb : Incident cs b := ⟨a,(edgeAt_symmetric cs b.val a.val).trans he⟩
      simpa only [w,dif_pos ha,dif_pos hb] using hz a b hab he
    exact ⟨w,normalized_unary_raw cs _ hs hu hw⟩

theorem any_range_fin (n : ℕ) (f : ℕ → Bool) :
    (List.range n).any f = true ↔ ∃ a : Fin n, f a.val = true := by
  simp only [List.any_eq_true,List.mem_range]
  constructor
  · rintro ⟨a,ha,hf⟩
    exact ⟨⟨a,ha⟩,hf⟩
  · rintro ⟨a,hf⟩
    exact ⟨a.val,a.isLt,hf⟩

open SparseRelabelPreparation

def incident (p : Input × ℕ) : Bool :=
  (vertexList p.1).any (fun b => edgeAt p.1.2.2 p.2 b)
def allowed (p : Input × ℕ) : Bool :=
  (domainList p.1).any (fun x => unaryAt p.1.2.2 p.2 (value (p.1,x)))
def check (p : Input) : Bool :=
  (vertexList p).all (fun a => if incident (p,a) then true else allowed (p,a))

@[fun_prop] theorem incident_polyT : PolyT incident := by unfold incident; fun_prop
@[fun_prop] theorem allowed_polyT : PolyT allowed := by unfold allowed; fun_prop
@[fun_prop] theorem check_polyT : PolyT check := by unfold check; fun_prop

theorem incident_of (p : Input) (a : Fin p.1.length) :
    incident (p,a.val) = true ↔ Incident p.2.2 a := by
  unfold incident vertexList Incident
  exact any_range_fin _ _

theorem allowed_of (p : Input) (a : Fin p.1.length) :
    allowed (p,a.val) = true ↔ ∃ x : Fin (supportList p).length,
      unaryAt p.2.2 a.val (SparseSupportDomain.decode p.2.1 p.2.2 x).val = true := by
  unfold allowed domainList
  rw [any_range_fin]
  simp only [value_of]

theorem check_of (p : Input) : check p = true ↔
    Feasible (k:=p.1.length) p.2.2 (SparseSupportDomain.decode p.2.1 p.2.2) := by
  unfold check vertexList
  rw [TableRefinement.all_range_fin]
  constructor
  · intro h a hi
    have hn : incident (p,a.val) = false :=
      Bool.eq_false_iff.mpr (fun ht => hi ((incident_of p a).mp ht))
    have hh := h a
    simp only [hn,Bool.false_eq_true,if_false] at hh
    exact (allowed_of p a).mp hh
  · intro h a
    by_cases hi : incident (p,a.val) = true
    · simp [hi]
    · have hn : ¬Incident p.2.2 a := fun ht => hi ((incident_of p a).mpr ht)
      have hx := (allowed_of p a).mpr (h a hn)
      simp [hi,hx]

theorem original_decision_iff (p : Input) (hs : ScopeBounded p.1.length p.2.2)
    (hne : p.2.2 ≠ []) :
    (∃ z : Fin p.1.length → Fin p.2.1, RawValid p.2.2 z) ↔
      check p = true ∧ ∃ w, (semantic p).valid w := by
  rw [SparseSupportDomain.exists_relabelled_iff p.2.2 hs hne]
  have hh := decision_image_iff p.2.2 (SparseSupportDomain.decode p.2.1 p.2.2) hs
  rw [← check_of p] at hh
  exact hh

#print axioms decision_image_iff
#print axioms check_polyT
#print axioms original_decision_iff

end CSPConsequence.SparseIsolates
