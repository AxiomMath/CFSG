module

public import CFSG.Quasithin.H13.L32NS7ConjInputs
public import Certificates.Kernel.H13.S7ConjK
public import Certificates.Kernel.H13.ElemsS8
public import Certificates.Kernel.H13.ElemsS7
public import Certificates.Kernel.H13.DataS7Conj
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Mat8PSet
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Conj CFSG.KC.Mat8P

@[expose] noncomputable def repsStepT (st : NT (List ℕ) × List (List ℕ)) (h : List ℕ) :
    NT (List ℕ) × List (List ℕ) :=
  if memLR st.1 h then st else ((orbOf h).foldl insLR st.1, h :: st.2)

theorem repsStepT_def : repsStepT = fun st h =>
    if memLR st.1 h then st else ((orbOf h).foldl insLR st.1, h :: st.2) := rfl

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem foldl_insert_rel (l : List (List ℕ)) :
    ∀ (hs : Std.HashSet (List ℕ)) (t : NT (List ℕ)), (∀ y, hs.contains y = memLR t y) →
      ∀ y, (l.foldl (fun s x => s.insert x) hs).contains y = memLR (l.foldl insLR t) y := by
  induction l with
  | nil => intro hs t h y; exact h y
  | cons a l ih =>
    intro hs t h y
    apply ih
    intro z
    rw [Std.HashSet.contains_insert, memLR_insLR, h]

theorem reps_fold_rel (l : List (List ℕ)) :
    ∀ (a : Std.HashSet (List ℕ) × List (List ℕ)) (b : NT (List ℕ) × List (List ℕ)),
      a.2 = b.2 → (∀ y, a.1.contains y = memLR b.1 y) →
      (l.foldl (fun (st : Std.HashSet (List ℕ) × List (List ℕ)) h =>
        if st.1.contains h then st else ((orbOf h).foldl (fun s x => s.insert x) st.1, h :: st.2))
        a).2 = (l.foldl repsStepT b).2 := by
  induction l with
  | nil => intro a b h2 _; exact h2
  | cons h l ih =>
    intro a b h2 h1
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · unfold repsStepT
      rw [h1]
      split
      · exact h2
      · simp only [h2]
    · intro y
      unfold repsStepT
      rw [h1 h]
      split
      · exact h1 y
      · exact foldl_insert_rel _ _ _ h1 y

@[expose] noncomputable def s7cRepsF (l : List (List ℕ)) : List (List ℕ) :=
  (l.foldl (fun (st : Std.HashSet (List ℕ) × List (List ℕ)) h =>
    if st.1.contains h then st else ((orbOf h).foldl (fun s x => s.insert x) st.1, h :: st.2))
    ((∅ : Std.HashSet (List ℕ)), [])).2

theorem s7cRepsF_eq (l : List (List ℕ)) : s7cRepsF l = (l.foldl repsStepT (.tip [], [])).2 :=
  reps_fold_rel l _ _ rfl (fun y => by rw [Std.HashSet.contains_empty, memLR_empty])

theorem reps_toT : reps = (invs8.foldl repsStepT (.tip [], [])).2 :=
  (rfl : reps = s7cRepsF invs8).trans (s7cRepsF_eq invs8)

theorem powB_unpackM : ∀ (fuel b n a : ℕ),
    powB fuel (unpackM b) n (unpackM a) = unpackM (powBP fuel b n a)
  | 0, _, _, _ => rfl
  | fuel + 1, b, n, a => by
    rw [powB, powBP, mul8_unpackM]
    split_ifs with h
    · rw [mul8_unpackM, powB_unpackM]
    · rw [powB_unpackM]

theorem inv8_unpackM (m : ℕ) : inv8 (unpackM m) = unpackM (invP m) := by
  rw [inv8, invP, ← oneP_eq, powB_unpackM]

set_option maxRecDepth 100000 in
theorem s7L_lt : ∀ p ∈ D.s7L, p < 2 ^ 64 := by decide +kernel

theorem c7_eq : c7 = unpackM (code64R c7) := by decide

theorem s7H_unpackM {q : ℕ} (hq : q < 2 ^ 64) :
    s7H.contains (unpackM q) = memP (ofListP D.s7L) q := by
  rw [s7H, s7E_eq, hs_contains_map _ s7L_lt, validB_unpackM, Bool.true_and, code64R_unpackM hq]

theorem s7H_mulP (a b : ℕ) : s7H.contains (unpackM (mulP a b)) = memP (ofListP D.s7L) (mulP a b) :=
  s7H_unpackM (mulP_lt a b)

theorem mul8_c7 (m : ℕ) : mul8 (unpackM m) c7 = unpackM (mulP m (code64R c7)) := by
  conv_lhs => rw [c7_eq]
  exact mul8_unpackM _ _

theorem beq_one_unpack (a b : ℕ) : (unpackM (mulP a b) == one8) = (mulP a b == oneP) := by
  rw [← oneP_eq, unpackM_beq (mulP_lt _ _) oneP_lt]

theorem conjB_unpackM (m r : ℕ) (hr : r < 2 ^ 64) :
    conjB (unpackM m, inv8 (unpackM m)) (unpackM r) = conjBP m (invP m) (unpackM r) := by
  simp only [conjB, conjBP, inv8_unpackM, validB_unpackM, Bool.true_and, mul8_c7, mul8_unpackM,
    code64R_unpackM hr, s7H_mulP, beq_one_unpack]

theorem hB_unpackM (r : ℕ) (hr : r < 2 ^ 64) : hB (unpackM r) = hBF (unpackM r) := by
  have hs : s8EI.any (fun p => conjB p (unpackM r)) =
      D.s8L.any fun m => conjBP m (invP m) (unpackM r) := by
    have h' : ∀ m, conjB (unpackM m, inv8 (unpackM m)) (unpackM r) =
        conjBP m (invP m) (unpackM r) := fun m => conjB_unpackM m r hr
    rw [s8EI, s8E_eq, List.map_map, List.any_map, Function.comp_def]
    simp only [Function.comp_def, h']
  simp only [hB, hBF, closedB, nodupB_toP, elemsOf_toF, hs_contains_toLR', contains_toLR, hs,
    mul8_toF]

theorem conjAt_any (r : ℕ) (h : conjAt r = true) :
    (D.s8L.any fun m => conjBP m (invP m) (unpackM r)) = true := by
  rw [conjAt] at h
  cases hm : D.s8L[cjIdx]? with
  | none => rw [hm] at h; exact absurd h Bool.false_ne_true
  | some m =>
    rw [hm, Option.any_some] at h
    exact List.any_eq_true.2 ⟨m, List.mem_of_getElem? hm, h⟩

theorem hBF_of_hBP (r : ℕ) (hr : r < 2 ^ 64) (h : hBP r = true) : hBF (unpackM r) = true := by
  have hc7 : validB c7 = true := by decide
  have hg : [c7, unpackM r].all validB = true := by
    simp only [List.all_cons, List.all_nil, hc7, validB_unpackM, Bool.and_self]
  have hE : elemsF [c7, unpackM r] 5041 = (elemsP [code64R c7, r] 5041).map unpackM := by
    rw [elemsF, if_pos hg, List.map_cons, List.map_cons, List.map_nil, code64R_unpackM hr]
  rw [hBP, hBQ] at h
  generalize elemsP [code64R c7, r] 5041 = L at h hE
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlt, hnd⟩, hone⟩, hif⟩ := h
  have hlt' : ∀ x ∈ L, x < 2 ^ 64 := fun x hx => by
    have h1 := List.all_eq_true.1 hlt x hx
    rw [Nat.blt_eq] at h1
    exact h1
  have hid : (L.map unpackM).map code64R = L := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    exact List.map_congr_left fun x hx => code64R_unpackM (hlt' x hx)
  have hmem : ∀ y, L.contains y = true → memLR (ofListLR (L.map unpackM)) (unpackM y) = true :=
    fun y hy => by
      rw [memLR_ofListLR, List.contains_iff_mem]
      exact List.mem_map_of_mem (List.contains_iff_mem.1 hy)
  rw [hBF, hE]
  simp only [Bool.and_eq_true, List.length_map]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hg⟩, ?_⟩
  · rw [List.all_map]
    exact List.all_eq_true.2 fun x _ => validB_unpackM x
  · rw [hid]
    exact hnd
  · rw [← oneP_eq]
    exact hmem oneP hone
  · split_ifs with hl
    · rw [if_pos hl, Bool.and_eq_true] at hif
      obtain ⟨hcl, hcj⟩ := hif
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [hBC, List.all_eq_true] at hcl
        rw [List.all_map, List.all_eq_true]
        intro x hx
        have hx' := hcl x hx
        rw [Bool.and_eq_true, memP_ofListP, memP_ofListP] at hx'
        simp only [Function.comp_apply, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true, mul8F_eq]
        rw [c7_eq, mul8_unpackM, mul8_unpackM]
        exact ⟨hmem _ hx'.1, hmem _ hx'.2⟩
      · rw [Bool.or_eq_true] at hcj ⊢
        exact hcj.imp id (conjAt_any r)
    · rfl

set_option maxRecDepth 100000

theorem all_any_of_idx {α β : Type} (g : α → β → Bool) :
    ∀ (L : List α) (I : List ℕ) (P : List β), L.length = I.length →
      (L.zip I).all (fun q => (P[q.2]?).any (g q.1)) = true → (L.all fun x => P.any (g x)) = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, hl, _ => absurd hl (by simp)
  | x :: L, i :: I, P, hl, h => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, all_any_of_idx g L I P (by simpa using hl) h.2⟩
    cases hm : P[i]? with
    | none => simp [hm] at h
    | some p =>
      rw [hm, Option.any_some] at h
      exact List.any_eq_true.2 ⟨p, List.mem_of_getElem? hm, h.1⟩

theorem s7s8B_true : s7s8B = true := by
  have h := all_any_of_idx (fun (x : List ℕ) (p : ℕ) => unpackM p == x)
    CFSG.Quasithin.H13.S7Cert.s7G s7cGI D.s8L (by decide) (by decide +kernel)
  rw [s7s8B, s8H, s8E_eq, List.all_eq_true]
  intro g hg
  obtain ⟨p, hp, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 h g hg)
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem]
  exact List.mem_map.2 ⟨p, hp, beq_iff_eq.1 he⟩

theorem filter_of_slices {α : Type} (L N : List α) (p : α → Bool) (c : ℕ) (A : List ℕ) :
    ∀ m k, L.length ≤ (k + m) * c → A.getD (k + m) 0 = N.length →
      (∀ j < m, A.getD (k + j) 0 ≤ A.getD (k + j + 1) 0 ∧
        ((L.drop ((k + j) * c)).take c).filter p =
          (N.drop (A.getD (k + j) 0)).take (A.getD (k + j + 1) 0 - A.getD (k + j) 0)) →
      (L.drop (k * c)).filter p = N.drop (A.getD k 0)
  | 0, k, hL, hA, _ => by
    rw [Nat.add_zero] at hL hA
    rw [List.drop_eq_nil_of_le hL, List.filter_nil, hA, List.drop_length]
  | m + 1, k, hL, hA, h => by
    have e1 : k + (m + 1) = k + 1 + m := by omega
    have ih := filter_of_slices L N p c A m (k + 1) (by rw [← e1]; exact hL) (by rw [← e1]; exact hA)
      (fun j hj => by
        have e2 : k + (j + 1) = k + 1 + j := by omega
        have h' := h (j + 1) (by omega)
        rw [e2] at h'
        exact h')
    obtain ⟨hle, h0⟩ := h 0 (by omega)
    rw [Nat.add_zero] at hle h0
    have e4 : k * c + c = (k + 1) * c := (Nat.succ_mul k c).symm
    rw [← List.take_append_drop c (L.drop (k * c)), List.filter_append, h0, List.drop_drop, e4, ih]
    have e3 : A.getD k 0 + (A.getD (k + 1) 0 - A.getD k 0) = A.getD (k + 1) 0 := by omega
    conv_rhs => rw [← List.take_append_drop (A.getD (k + 1) 0 - A.getD k 0) (N.drop (A.getD k 0))]
    rw [List.drop_drop, e3]

@[expose] def s7cPN (n : ℕ) : Bool := s7cC7P.any fun c => mulP n s7cC7 == mulP c n

@[expose] def s7cPI (x : ℕ) : Bool := mulP x x == oneP && x != oneP

@[expose] noncomputable def s7cChunk (k : ℕ) : Bool :=
  Nat.ble (s7cNCum.getD k 0) (s7cNCum.getD (k + 1) 0) &&
    (((D.s8L.drop (k * 2016)).take 2016).filter s7cPN ==
      ((s7cNP.map Prod.fst).drop (s7cNCum.getD k 0)).take
        (s7cNCum.getD (k + 1) 0 - s7cNCum.getD k 0)) &&
    Nat.ble (s7cInvCum.getD k 0) (s7cInvCum.getD (k + 1) 0) &&
    (((D.s8L.drop (k * 2016)).take 2016).filter s7cPI ==
      (s7cInv.drop (s7cInvCum.getD k 0)).take (s7cInvCum.getD (k + 1) 0 - s7cInvCum.getD k 0))

set_option maxHeartbeats 0 in
#kc_each s7cChunk 0 20

theorem s7cChunk_all : ∀ j < 20, s7cChunk j = true := by
  intro j hj
  interval_cases j
  · exact s7cChunk0
  · exact s7cChunk1
  · exact s7cChunk2
  · exact s7cChunk3
  · exact s7cChunk4
  · exact s7cChunk5
  · exact s7cChunk6
  · exact s7cChunk7
  · exact s7cChunk8
  · exact s7cChunk9
  · exact s7cChunk10
  · exact s7cChunk11
  · exact s7cChunk12
  · exact s7cChunk13
  · exact s7cChunk14
  · exact s7cChunk15
  · exact s7cChunk16
  · exact s7cChunk17
  · exact s7cChunk18
  · exact s7cChunk19

theorem s7cChunk_spec (k : ℕ) (h : s7cChunk k = true) :
    (s7cNCum.getD k 0 ≤ s7cNCum.getD (k + 1) 0 ∧
      ((D.s8L.drop (k * 2016)).take 2016).filter s7cPN =
        ((s7cNP.map Prod.fst).drop (s7cNCum.getD k 0)).take
          (s7cNCum.getD (k + 1) 0 - s7cNCum.getD k 0)) ∧
    (s7cInvCum.getD k 0 ≤ s7cInvCum.getD (k + 1) 0 ∧
      ((D.s8L.drop (k * 2016)).take 2016).filter s7cPI =
        (s7cInv.drop (s7cInvCum.getD k 0)).take (s7cInvCum.getD (k + 1) 0 - s7cInvCum.getD k 0)) := by
  rw [s7cChunk] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h
  exact ⟨⟨h.1.1.1, h.1.1.2⟩, ⟨h.1.2, h.2⟩⟩

theorem iter_unpackM (a b : ℕ) : ∀ j : ℕ,
    (mul8 (unpackM a))^[j] (unpackM b) = unpackM ((mulP a)^[j] b)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iter_unpackM a b j,
      mul8_unpackM]

theorem c7_eqC : c7 = unpackM s7cC7 := by decide

theorem c7P_eqC : c7P = s7cC7P.map unpackM := by
  have h : (List.range 6).map (fun k => (mulP s7cC7)^[k + 1] oneP) = s7cC7P := by decide +kernel
  rw [c7P, c7_eqC, ← oneP_eq, ← h, List.map_map]
  exact List.map_congr_left fun k _ => iter_unpackM _ _ _

theorem beq_unpack_mulP (a b c d : ℕ) :
    (unpackM (mulP a b) == unpackM (mulP c d)) = (mulP a b == mulP c d) :=
  unpackM_beq (mulP_lt _ _) (mulP_lt _ _)

theorem nE_pred (m : ℕ) :
    (c7P.any fun c => mul8 (unpackM m) c7 == mul8 c (unpackM m)) =
      (s7cC7P.any fun c => mulP m s7cC7 == mulP c m) := by
  rw [c7P_eqC, List.any_map, c7_eqC]
  congr 1
  funext c
  simp only [Function.comp_apply, mul8_unpackM, beq_unpack_mulP]

theorem s7c_s8L_len : D.s8L.length ≤ (0 + 20) * 2016 := by decide +kernel

theorem nE_filter : D.s8L.filter (fun n => s7cC7P.any fun c => mulP n s7cC7 == mulP c n) =
    s7cNP.map Prod.fst := by
  have h := filter_of_slices D.s8L (s7cNP.map Prod.fst) s7cPN 2016 s7cNCum 20 0 s7c_s8L_len
    (by decide) (fun j hj => by rw [Nat.zero_add]; exact (s7cChunk_spec j (s7cChunk_all j hj)).1)
  have h0 : s7cNCum.getD 0 0 = 0 := rfl
  rw [Nat.zero_mul, List.drop_zero, h0, List.drop_zero] at h
  exact h

theorem nE_eq : nE = s7cNP.map fun q => (unpackM q.1, unpackM q.2) := by
  have hi : s7cNP.map (fun q => (q.1, invP q.1)) = s7cNP := by decide +kernel
  have hf : (CFSG.Quasithin.H13.S8Cert.s8E.filter fun n => c7P.any fun c => mul8 n c7 == mul8 c n) =
      (s7cNP.map Prod.fst).map unpackM := by
    rw [s8E_eq, List.filter_map, ← nE_filter]
    exact congrArg (List.map unpackM) (List.filter_congr fun m _ => nE_pred m)
  rw [nE, hf]
  conv_rhs => rw [← hi]
  simp only [List.map_map]
  exact List.map_congr_left fun q _ => by simp only [Function.comp_apply, inv8_unpackM]

theorem inv_pred (m : ℕ) (hm : m < 2 ^ 64) :
    (mul8 (unpackM m) (unpackM m) == one8 && unpackM m != one8) =
      (mulP m m == oneP && m != oneP) := by
  simp only [bne, mul8_unpackM, ← oneP_eq, unpackM_beq (mulP_lt _ _) oneP_lt,
    unpackM_beq hm oneP_lt]

theorem invs8_filter : D.s8L.filter (fun x => mulP x x == oneP && x != oneP) = s7cInv := by
  have h := filter_of_slices D.s8L s7cInv s7cPI 2016 s7cInvCum 20 0 s7c_s8L_len
    (by decide) (fun j hj => by rw [Nat.zero_add]; exact (s7cChunk_spec j (s7cChunk_all j hj)).2)
  have h0 : s7cInvCum.getD 0 0 = 0 := rfl
  rw [Nat.zero_mul, List.drop_zero, h0, List.drop_zero] at h
  exact h

theorem invs8_eq : invs8 = s7cInv.map unpackM := by
  rw [invs8, s8E_eq, List.filter_map, ← invs8_filter]
  exact congrArg (List.map unpackM) (List.filter_congr fun m hm => inv_pred m (s8L_lt m hm))

theorem s7c_nB_true : CFSG.Quasithin.H13.S7Conj.nB = true := by
  rw [nB, nE_eq, List.all_map]
  simp only [Function.comp_def, validB_unpackM, Bool.true_and, mul8_unpackM, nE_pred,
    beq_one_unpack]
  decide +kernel

theorem reps_eq : reps = D.repsL.map unpackM := by
  rw [reps_toT, invs8_eq, List.foldl_map]
  simp only [repsStepT_def, orbOf, nE_eq, List.map_map, Function.comp_def, mul8_unpackM]
  decide +kernel

set_option maxRecDepth 100000 in
theorem repsL_lt : ∀ p ∈ D.repsL, p < 2 ^ 64 := by decide +kernel

theorem repsH_mulP (a b : ℕ) : repsH.contains (unpackM (mulP a b)) = memP (ofListP D.repsL) (mulP a b) := by
  rw [repsH, reps_eq, hs_contains_map _ repsL_lt, validB_unpackM, Bool.true_and,
    code64R_unpackM (mulP_lt a b)]

theorem s7c_orbB_true : CFSG.Quasithin.H13.S7Conj.orbB = true := by
  rw [orbB, invs8_eq, nE_eq, List.all_map]
  simp only [Function.comp_def, List.any_map, mul8_unpackM, repsH_mulP]
  exact all_any_of_idx (fun h q => memP (ofListP D.repsL) (mulP (mulP q.1 h) q.2)) s7cInv s7cIdx
    s7cNP (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem repsL_length : D.repsL.length = 28 := by decide +kernel

theorem reps_all_hB : reps.all hB = true := by
  rw [reps_eq, List.all_map, List.all_eq_true]
  intro r hr
  rw [Function.comp_apply, hB_unpackM r (repsL_lt r hr)]
  refine hBF_of_hBP r (repsL_lt r hr) (List.all_eq_true.1 ?_ r hr)
  apply CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 1 28 (by rw [repsL_length])
  intro j hj
  interval_cases j
  · exact hBk0
  · exact hBk1
  · exact hBk2
  · exact hBk3
  · exact hBk4
  · exact hBk5
  · exact hBk6
  · exact hBk7
  · exact hBk8
  · exact hBk9
  · exact hBk10
  · exact hBk11
  · exact hBk12
  · exact hBk13
  · exact hBk14
  · exact hBk15
  · exact hBk16
  · exact hBk17
  · exact hBk18
  · exact hBk19
  · exact hBk20
  · exact hBk21
  · exact hBk22
  · exact hBk23
  · exact hBk24
  · exact hBk25
  · exact hBk26
  · exact hBk27

theorem s7ConjCheck_true : s7ConjCheck = true := by
  rw [s7ConjCheck, s7s8B_true, s7c_nB_true, s7c_orbB_true, reps_all_hB]
  rfl

end CertificateChecks.KernelH13

end
