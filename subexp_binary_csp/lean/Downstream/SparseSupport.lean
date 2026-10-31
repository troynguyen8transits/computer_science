import Downstream.SparseNormalization
import ToTuring.Lib.List3

set_option autoImplicit false

/-! Global tuple support for compactly described domains. The support is a
computed filtered, deduplicated list, of length at most twice the number of
listed tuples. Every constrained satisfying value belongs to it. For decision,
unconstrained variables can be moved to a single supported value; this does not
preserve their contribution to the number of solutions. -/
namespace CSPConsequence.SparseSupport
open Groundwork SparseNormalization

def tupleValues (ts : List (ℕ × ℕ)) : List ℕ := ts.flatMap (fun p => [p.1,p.2])
def values (cs : SparseInput) : List ℕ := cs.flatMap (fun c => tupleValues c.2.2)
def tupleCount (cs : SparseInput) : ℕ := (cs.map (fun c => c.2.2.length)).sum
def support (D : ℕ) (cs : SparseInput) : List ℕ :=
  ((values cs).filter (fun x => decide (x < D))).dedup

theorem tupleValues_length (ts : List (ℕ × ℕ)) : (tupleValues ts).length = 2*ts.length := by
  induction ts with
  | nil => simp [tupleValues]
  | cons p ts ih =>
    simp only [tupleValues,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil]
    change 2+(tupleValues ts).length = 2*(ts.length+1)
    rw [ih]
    omega

theorem values_length (cs : SparseInput) : (values cs).length = 2*tupleCount cs := by
  induction cs with
  | nil => simp [values,tupleCount]
  | cons c cs ih =>
    simp only [values,List.flatMap_cons,List.length_append,tupleValues_length]
    change 2*c.2.2.length+(values cs).length = 2*tupleCount (c::cs)
    rw [ih]
    simp only [tupleCount,List.map_cons,List.sum_cons]
    omega

theorem support_bound (D : ℕ) (cs : SparseInput) : (support D cs).length ≤ 2*tupleCount cs := by
  apply le_trans (List.dedup_sublist _).length_le
  apply le_trans (List.length_filter_le _ _)
  exact le_of_eq (values_length cs)

theorem support_nodup (D : ℕ) (cs : SparseInput) : (support D cs).Nodup := List.nodup_dedup _

theorem mem_support (D : ℕ) (cs : SparseInput) (x : ℕ) :
    x ∈ support D cs ↔ x ∈ values cs ∧ x < D := by
  simp [support,List.mem_filter]

theorem tuple_left_mem (cs : SparseInput) (c : Constraint) (hc : c ∈ cs)
    (x y : ℕ) (hxy : (x,y) ∈ c.2.2) : x ∈ values cs := by
  apply List.mem_flatMap.mpr
  refine ⟨c,hc,?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨(x,y),hxy,by simp⟩

theorem tuple_right_mem (cs : SparseInput) (c : Constraint) (hc : c ∈ cs)
    (x y : ℕ) (hxy : (x,y) ∈ c.2.2) : y ∈ values cs := by
  apply List.mem_flatMap.mpr
  refine ⟨c,hc,?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨(x,y),hxy,by simp⟩

theorem constrained_supported {k D : ℕ} (cs : SparseInput)
    (hs : ScopeBounded k cs) (z : Fin k → Fin D) (hz : RawValid cs z)
    (c : Constraint) (hc : c ∈ cs) :
    extend z c.1 ∈ support D cs ∧ extend z c.2.1 ∈ support D cs := by
  let a : Fin k := ⟨c.1,(hs c hc).1⟩
  let b : Fin k := ⟨c.2.1,(hs c hc).2⟩
  have ha : c.1 = a.val := rfl
  have hb : c.2.1 = b.val := rfl
  refine ⟨(mem_support D cs _).mpr ⟨tuple_left_mem cs c hc _ _ (hz c hc),?_⟩,
    (mem_support D cs _).mpr ⟨tuple_right_mem cs c hc _ _ (hz c hc),?_⟩⟩
  · rw [ha,extend_fin]
    exact (z a).isLt
  · rw [hb,extend_fin]
    exact (z b).isLt

theorem all_supported_of_nonisolated {k D : ℕ} (cs : SparseInput)
    (hs : ScopeBounded k cs) (hni : Nonisolated k cs)
    (z : Fin k → Fin D) (hz : RawValid cs z) (a : Fin k) : (z a).val ∈ support D cs := by
  obtain ⟨b,hb⟩ := hni a
  obtain ⟨_,c,hc,hleft|hright⟩ := (edgeAt_iff cs a.val b.val).mp hb
  · have h := (constrained_supported cs hs z hz c hc).1
    simpa only [hleft.1,extend_fin] using h
  · have h := (constrained_supported cs hs z hz c hc).2
    simpa only [hright.2,extend_fin] using h

theorem exists_supported_iff {k D : ℕ} (cs : SparseInput) (hs : ScopeBounded k cs)
    (hne : cs ≠ []) :
    (∃ z : Fin k → Fin D, RawValid cs z) ↔
      ∃ z : Fin k → Fin D, RawValid cs z ∧ ∀ a, (z a).val ∈ support D cs := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨c,hc⟩ := List.exists_mem_of_ne_nil cs hne
    let a0 : Fin k := ⟨c.1,(hs c hc).1⟩
    have h0 : (z a0).val ∈ support D cs := by
      have h := (constrained_supported cs hs z hz c hc).1
      have ha : c.1 = a0.val := rfl
      simpa only [ha,extend_fin] using h
    let w : Fin k → Fin D := fun a => if (z a).val ∈ support D cs then z a else z a0
    have hw (a : Fin k) : (w a).val ∈ support D cs := by
      dsimp [w]
      split_ifs with h
      · exact h
      · exact h0
    refine ⟨w,?_,hw⟩
    intro d hd
    let a : Fin k := ⟨d.1,(hs d hd).1⟩
    let b : Fin k := ⟨d.2.1,(hs d hd).2⟩
    have ha : d.1 = a.val := rfl
    have hb : d.2.1 = b.val := rfl
    have hv := constrained_supported cs hs z hz d hd
    have hwa : w a = z a := by
      apply if_pos
      simpa only [ha,extend_fin] using hv.1
    have hwb : w b = z b := by
      apply if_pos
      simpa only [hb,extend_fin] using hv.2
    have h := hz d hd
    rw [ha,hb,extend_fin,extend_fin] at h ⊢
    simpa only [hwa,hwb] using h
  · rintro ⟨z,hz,_⟩
    exact ⟨z,hz⟩

@[fun_prop] theorem values_polyT : PolyT values := by
  unfold values tupleValues
  fun_prop

@[fun_prop] theorem support_polyT :
    PolyT (fun p : ℕ × SparseInput => support p.1 p.2) := by
  unfold support
  fun_prop

#print axioms support_bound
#print axioms all_supported_of_nonisolated
#print axioms exists_supported_iff
#print axioms support_polyT
end CSPConsequence.SparseSupport
