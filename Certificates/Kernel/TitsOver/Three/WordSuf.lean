module

public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def wordKP (n w m acc : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) acc
    (fun z _ ih => strictN ih (fun T => strictN (CFSG.KS.Mathieu.icode z) (fun c =>
      pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T))) wd

theorem wordK_eq_wordKP (n w m idn : Nat) (S SI : Nat → Nat) (wd : List Int) :
    wordK n w m idn S SI wd = wordKP n w m idn S SI wd := rfl

theorem wordKP_cons (n w m acc : Nat) (S SI : Nat → Nat) (z : Int) (u : List Int) :
    wordKP n w m acc S SI (z :: u) = strictN (wordKP n w m acc S SI u) (fun T =>
      strictN (CFSG.KS.Mathieu.icode z) (fun c =>
      pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl

theorem wordKP_append (n w m acc : Nat) (S SI : Nat → Nat) (u v : List Int) :
    wordKP n w m acc S SI (u ++ v) = wordKP n w m (wordKP n w m acc S SI v) S SI u := by
  induction u with
  | nil => rfl
  | cons z u ih =>
    rw [List.cons_append, wordKP_cons, wordKP_cons, ih]

theorem canonK_letter {n w : Nat} {S SI : Nat → Nat}
    (hS : ∀ k, canonK n w (mask w) (n * w) (S k) = true)
    (hSI : ∀ k, canonK n w (mask w) (n * w) (SI k) = true) (b : Bool) (k l : Nat) :
    canonK n w (mask w) (n * w) (nIf(b, S k, SI l)) = true := by
  cases b
  · exact hSI l
  · exact hS k

theorem canonK_wordKP {n w acc : Nat} {S SI : Nat → Nat}
    (hS : ∀ k, canonK n w (mask w) (n * w) (S k) = true)
    (hSI : ∀ k, canonK n w (mask w) (n * w) (SI k) = true)
    (ha : canonK n w (mask w) (n * w) acc = true) :
    ∀ u, canonK n w (mask w) (n * w) (wordKP n w (mask w) acc S SI u) = true
  | [] => ha
  | z :: u => by
    rw [wordKP_cons, CFSG.KS.PF.strictN_eqP, CFSG.KS.PF.strictN_eqP]
    exact CFSG.KC.BfsPin.canonK_pcomp (canonK_letter hS hSI _ _ _) (canonK_wordKP hS hSI ha u)

theorem wordKP_eq_pcomp {n w acc : Nat} {S SI : Nat → Nat}
    (hS : ∀ k, canonK n w (mask w) (n * w) (S k) = true)
    (hSI : ∀ k, canonK n w (mask w) (n * w) (SI k) = true)
    (ha : canonK n w (mask w) (n * w) acc = true) :
    ∀ u, wordKP n w (mask w) acc S SI u =
      pcomp n w (mask w) (wordKP n w (mask w) (pidn n w) S SI u) acc
  | [] => by
    obtain ⟨hn, hw, -, ha4⟩ := CFSG.KS.PF.canon_facts ha
    have hn32 : n < 2 ^ 32 := by omega
    have hw0 := CFSG.KS.PF.w_pos hw
    obtain ⟨-, -, ha3, -⟩ := CFSG.KS.PF.canon_facts ha
    refine (CFSG.KS.PF.eq_of_fields hw0 ha3 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0)
      fun i hi => ?_)
    change pg w (mask w) acc i = pg w (mask w) (pcomp n w (mask w) (pidn n w) acc) i
    rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pidn hn hw (ha4 i hi)]
  | z :: u => by
    rw [wordKP_cons, wordKP_cons, CFSG.KS.PF.strictN_eqP, CFSG.KS.PF.strictN_eqP,
      CFSG.KS.PF.strictN_eqP, CFSG.KS.PF.strictN_eqP, wordKP_eq_pcomp hS hSI ha u]
    obtain ⟨hn, hw, -, -⟩ := CFSG.KS.PF.canon_facts ha
    have hn32 : n < 2 ^ 32 := by omega
    have hw0 := CFSG.KS.PF.w_pos hw
    obtain ⟨-, -, -, ha4⟩ := CFSG.KS.PF.canon_facts ha
    refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0)
      (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
    simp only [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 (ha4 i hi)]

theorem wordK_conj {n w : Nat} {S SI : Nat → Nat}
    (hS : ∀ k, canonK n w (mask w) (n * w) (S k) = true)
    (hSI : ∀ k, canonK n w (mask w) (n * w) (SI k) = true) (c r v : List Int)
    (hv : canonK n w (mask w) (n * w) (wordK n w (mask w) (pidn n w) S SI v) = true) :
    wordK n w (mask w) (pidn n w) S SI (c ++ r ++ v) =
      pcomp n w (mask w) (wordK n w (mask w) (pidn n w) S SI c)
        (pcomp n w (mask w) (wordK n w (mask w) (pidn n w) S SI r)
          (wordK n w (mask w) (pidn n w) S SI v)) := by
  rw [wordK_eq_wordKP] at hv ⊢
  rw [List.append_assoc, wordKP_append, wordKP_append,
    wordKP_eq_pcomp hS hSI (canonK_wordKP hS hSI hv r) c, wordKP_eq_pcomp hS hSI hv r]
  rfl

theorem allN_of_all {α : Type} [Inhabited α] {l : List α} {p : α → Bool} {n : Nat}
    (hn : n ≤ l.length) (h : l.all p = true) : allN n (fun i => p (l[i]!)) = true :=
  PK.allN_iff.2 fun i hi => by
    have hi' : i < l.length := by omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    exact List.all_eq_true.1 h _ (List.getElem_mem hi')

theorem allN_of_zipIdx {α : Type} [Inhabited α] {l : List α} {f : Nat → α → Bool} {n : Nat}
    (hn : n ≤ l.length) (h : l.zipIdx.all (fun p => f p.2 p.1) = true) :
    allN n (fun i => f i (l[i]!)) = true :=
  PK.allN_iff.2 fun i hi => by
    have hi' : i < l.length := by omega
    have hz : i < l.zipIdx.length := by
      rw [List.length_zipIdx]
      exact hi'
    have hm := List.all_eq_true.1 h _ (List.getElem_mem hz)
    rw [List.getElem_zipIdx] at hm
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    simpa using hm

theorem allN_of_zipIdx_chunks {α : Type} [Inhabited α] {l : List α} {f : Nat → α → Bool}
    {n w m : Nat} (hw : 0 < w) (hn : n ≤ l.length) (hm : n ≤ m * w)
    (h : ∀ c < m, ((l.zipIdx.drop (w * c)).take w).all (fun p => f p.2 p.1) = true) :
    allN n (fun i => f i (l[i]!)) = true :=
  PK.allN_iff.2 fun i hi => by
    have hi' : i < l.length := by omega
    have hc : i / w < m := (Nat.div_lt_iff_lt_mul hw).2 (Nat.lt_of_lt_of_le hi hm)
    have hz : i < l.zipIdx.length := by
      rw [List.length_zipIdx]
      exact hi'
    have he : w * (i / w) + i % w = i := Nat.div_add_mod i w
    have hr : i % w < w := Nat.mod_lt i hw
    have hmem : l.zipIdx[i] ∈ (l.zipIdx.drop (w * (i / w))).take w := by
      rw [List.mem_iff_getElem]
      refine ⟨i % w, ?_, ?_⟩
      · simp only [List.length_take, List.length_drop]
        omega
      · simp only [List.getElem_take, List.getElem_drop, he]
    have hm := List.all_eq_true.1 (h _ hc) _ hmem
    rw [List.getElem_zipIdx] at hm
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    simpa using hm

theorem canonK_of_permOK {n w p q : Nat} (hs : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : canonK n w (mask w) (n * w) p = true := by
  unfold permOK at h
  unfold canonK
  simp only [PK.bAnd_eq, Bool.and_eq_true] at h ⊢
  refine ⟨hs, h.1, PK.allN_iff.2 fun i hi => ?_⟩
  have h3 := PK.allN_iff.1 h.2.2 i hi
  rw [CFSG.KS.PF.strictB_eqP] at h3
  simp only [Bool.and_eq_true] at h3
  exact h3.1

theorem wordK_of_split {n w N : Nat} {S SI R a s K : Nat → Nat} {W : Nat → List Int}
    (hS : ∀ k, canonK n w (mask w) (n * w) (S k) = true)
    (hSI : ∀ k, canonK n w (mask w) (n * w) (SI k) = true)
    (hR : ∀ i < N + 1, canonK n w (mask w) (n * w) (R i) = true) (h0 : R 0 = pidn n w)
    (h : ∀ i < N, a i < i + 1 ∧ s i < i + 1 ∧
      (W i).take (if a i = 0 then 0 else (W (a i - 1)).length) =
        (if a i = 0 then [] else W (a i - 1)) ∧
      ((W i).drop (if a i = 0 then 0 else (W (a i - 1)).length)).drop (K i) =
        (if s i = 0 then [] else W (s i - 1)) ∧
      (if a i = 0 then wordKP n w (mask w) (R (s i)) S SI
          (((W i).drop (if a i = 0 then 0 else (W (a i - 1)).length)).take (K i))
        else pcomp n w (mask w) (R (a i)) (wordKP n w (mask w) (R (s i)) S SI
          (((W i).drop (if a i = 0 then 0 else (W (a i - 1)).length)).take (K i)))) =
        R (i + 1)) :
    ∀ i < N, wordK n w (mask w) (pidn n w) S SI (W i) = R (i + 1) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    obtain ⟨ha, hs, hu, hd, hv⟩ := h i hi
    generalize (if a i = 0 then 0 else (W (a i - 1)).length) = P at hu hd hv
    have hsuf : wordK n w (mask w) (pidn n w) S SI (((W i).drop P).drop (K i)) = R (s i) := by
      rw [hd]
      by_cases e : s i = 0
      · rw [ite_eq_left e, e, h0]
        rfl
      · rw [ite_eq_right e]
        have := ih (s i - 1) (by omega) (by omega)
        rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero e)] at this
    have hX : wordKP n w (mask w) (pidn n w) S SI ((W i).drop P) =
        wordKP n w (mask w) (R (s i)) S SI (((W i).drop P).take (K i)) := by
      conv =>
        lhs
        rw [← List.take_append_drop (K i) ((W i).drop P)]
      rw [wordKP_append,
        ← wordK_eq_wordKP n w (mask w) (pidn n w) S SI (((W i).drop P).drop (K i)), hsuf]
    have hRs := canonK_wordKP hS hSI (hR (s i) (by omega))
      (((W i).drop P).take (K i))
    rw [← List.take_append_drop P (W i), wordK_eq_wordKP, wordKP_append, hX, hu, ← hv]
    by_cases e : a i = 0
    · rw [ite_eq_left e, ite_eq_left e]
      rfl
    · rw [ite_eq_right e, ite_eq_right e, wordKP_eq_pcomp hS hSI hRs,
        ← wordK_eq_wordKP n w (mask w) (pidn n w) S SI (W (a i - 1))]
      have := ih (a i - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero e)] at this
      rw [this]

end CertificateChecks.KernelTitsOver.Three

end
