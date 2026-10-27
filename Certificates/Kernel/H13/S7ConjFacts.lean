module

public import CFSG.Quasithin.H13.L32NS7ConjInputs
public import Certificates.Kernel.H13.S7ConjK
public import Certificates.Kernel.H13.ElemsS8
public import Certificates.Kernel.H13.ElemsS7
import CFSG.Certificates.Kernel.Mat8PSet
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Conj CFSG.KC.Mat8P

@[expose] def repsStepT (st : NT (List ℕ) × List (List ℕ)) (h : List ℕ) :
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

theorem reps_toT : reps = (invs8.foldl repsStepT (.tip [], [])).2 := by
  rw [reps]
  exact reps_fold_rel _ _ _ rfl (fun y => by rw [Std.HashSet.contains_empty, memLR_empty])

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

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem s7s8B_true : s7s8B = true := by
  rw [s7s8B, s8H, s8E_eq]
  simp only [hs_contains_map _ s8L_lt]
  decide +kernel

macro "s7c_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H13.S7Conj.nB, CFSG.Quasithin.H13.S7Conj.orbB,
    CFSG.Quasithin.H13.S7Conj.repsH, CertificateChecks.KernelH13.repsStepT_def,
    CFSG.Quasithin.H13.S7Conj.nE, CFSG.Quasithin.H13.S7Conj.invs8,
    CFSG.Quasithin.H13.S7Conj.orbOf, CFSG.Quasithin.H13.S7Conj.inv8,
    CFSG.Quasithin.H13.S7Conj.c7P, CertificateChecks.KernelH13.s8E_eq,
    CFSG.KC.Mat8P.hs_contains_toLR', CFSG.KC.Mat8P.hs_contains_toLR, CFSG.KC.Mat8P.mul8_toF]
  decide +kernel))

set_option maxHeartbeats 0 in
theorem s7c_nB_true : CFSG.Quasithin.H13.S7Conj.nB = true := by s7c_tac

set_option maxHeartbeats 0 in
theorem reps_eq : reps = D.repsL.map unpackM := by
  rw [reps_toT]
  s7c_tac

set_option maxHeartbeats 0 in
theorem s7c_orbB_true : CFSG.Quasithin.H13.S7Conj.orbB = true := by
  simp only [CFSG.Quasithin.H13.S7Conj.orbB, CFSG.Quasithin.H13.S7Conj.repsH, reps_eq]
  s7c_tac

set_option maxRecDepth 100000 in
theorem repsL_lt : ∀ p ∈ D.repsL, p < 2 ^ 64 := by decide +kernel

set_option maxRecDepth 100000 in
theorem repsL_length : D.repsL.length = 28 := by decide +kernel

theorem reps_all_hB : reps.all hB = true := by
  rw [reps_eq, List.all_map]
  have hf : ∀ r ∈ D.repsL, (hB ∘ unpackM) r = hBF (unpackM r) := fun r hr =>
    hB_unpackM r (repsL_lt r hr)
  rw [all_congr_mem hf]
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
