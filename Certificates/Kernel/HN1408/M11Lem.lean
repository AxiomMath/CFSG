module

public import Certificates.Kernel.HN1408.EnumH
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Check
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def ppK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ acc => pc X acc) e

@[expose] noncomputable def iterN (f : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => f acc) e

theorem pows (X : Nat) : Pows 1408 11 X (ppK X) := ⟨rfl, fun _ => rfl⟩

theorem cn_ppK {X : Nat} (hX : Cn X) (e : Nat) : Cn (ppK X e) := pows_canon (pows X) cId hX e

theorem powT_eq {X : Nat} (hX : Cn X) (e : Nat) :
    powT 1408 e (tabT (unpack 1408 11 X)) = tabT (unpack 1408 11 (ppK X e)) :=
  powT_unpack (pows X) idT_eq cId hX e

theorem pt_lt {X i : Nat} (hX : Cn X) (hi : i < 1408) : pt X i < 1408 :=
  CFSG.KC.L34KSnd.canon_lt hX hi

theorem pt_pc {X Y i : Nat} (hX : Cn X) (hi : i < 1408) : pt (pc X Y) i = pt X (pt Y i) :=
  CFSG.KC.L34KSnd.pg_pcomp' hX hi

theorem pt_id {i : Nat} (hi : i < 1408) : pt idK i = i := CFSG.KC.L34KSnd.pg_pidn' hn hi

theorem iterN_lt {f : Nat → Nat} (hf : ∀ i < 1408, f i < 1408) {x : Nat} (hx : x < 1408) :
    ∀ e, iterN f e x < 1408
  | 0 => hx
  | e + 1 => hf _ (iterN_lt hf hx e)

theorem iterN_congr {f g : Nat → Nat} (hf : ∀ i < 1408, f i < 1408) (hfg : ∀ i < 1408, f i = g i)
    {x : Nat} (hx : x < 1408) : ∀ e, iterN f e x = iterN g e x
  | 0 => rfl
  | e + 1 => by
    change f (iterN f e x) = g (iterN g e x)
    rw [← iterN_congr hf hfg hx e]
    exact hfg _ (iterN_lt hf hx e)

theorem pt_ppK {X : Nat} (hX : Cn X) {x : Nat} (hx : x < 1408) :
    ∀ e, pt (ppK X e) x = iterN (pt X) e x
  | 0 => pt_id hx
  | e + 1 => by
    change pt (pc X (ppK X e)) x = pt X (iterN (pt X) e x)
    rw [pt_pc hX hx, pt_ppK hX hx e]

theorem ordInS_eq {X : Nat} (hX : Cn X) :
    ordInS (idT 1408) (tabT (unpack 1408 11 X)) = (Nat.beq (ppK X 8) idK ||
      Nat.beq (ppK X 6) idK || Nat.beq (ppK X 5) idK || Nat.beq (ppK X 11) idK) := by
  unfold ordInS
  rw [powT_eq hX, powT_eq hX, powT_eq hX, powT_eq hX, idT_eq, tblEq_eq (cn_ppK hX 8) cId,
    tblEq_eq (cn_ppK hX 6) cId, tblEq_eq (cn_ppK hX 5) cId, tblEq_eq (cn_ppK hX 11) cId]

theorem ordInS_of {X e : Nat} (hX : Cn X) (he : e = 8 ∨ e = 6 ∨ e = 5 ∨ e = 11)
    (h : Nat.beq (ppK X e) idK = true) : ordInS (idT 1408) (tabT (unpack 1408 11 X)) = true := by
  rw [ordInS_eq hX]
  rcases he with rfl | rfl | rfl | rfl <;> simp [h]

theorem primeOrderOK_eq {X : Nat} (hX : Cn X) (p : Nat) :
    primeOrderOK p (tabT (unpack 1408 11 X)) = (Nat.beq (ppK X p) idK && !Nat.beq X idK) := by
  unfold primeOrderOK
  rw [powT_eq hX, idT_eq, tblEq_eq (cn_ppK hX p) cId, tblEq_eq hX cId]

@[expose] noncomputable def probeK (Y J : Nat) (p : List Nat) : Nat :=
  p.foldl (fun acc e => pc acc (pc (ppK Y e) J)) idK

@[expose] noncomputable def probePt (Y J : Nat) (p : List Nat) (x : Nat) : Nat :=
  p.foldr (fun e a => iterN (pt Y) e (pt J a)) x

@[expose] noncomputable def movedK (Y J : Nat) (p : List Nat) (e x : Nat) : Bool :=
  bAnd(Nat.blt x 1408, bIf(Nat.beq (iterN (probePt Y J p) e x) x, false, true))

@[expose] noncomputable def probeNeg (Y J : Nat) (p : List Nat) (x8 x6 x5 x11 : Nat) : Bool :=
  bAnd(movedK Y J p 8 x8, bAnd(movedK Y J p 6 x6, bAnd(movedK Y J p 5 x5, movedK Y J p 11 x11)))

theorem powsT_get {ty : Table} {e : Nat} (he : e < 6) : (powsT ty)[e]! = powT 1408 e ty := by
  rw [getElem!_pos (powsT ty) e (by simp [powsT]; omega)]
  match e, he with
  | 0, _ => simp [powsT]
  | 1, _ => simp [powsT]
  | 2, _ => simp [powsT]
  | 3, _ => simp [powsT]
  | 4, _ => simp [powsT]
  | 5, _ => simp [powsT]

theorem cn_fold {Y J : Nat} (hY : Cn Y) (hJ : Cn J) :
    ∀ (p : List Nat) (acc : Nat), Cn acc → Cn (p.foldl (fun a e => pc a (pc (ppK Y e) J)) acc)
  | [], _, h => h
  | e :: p, acc, h => cn_fold hY hJ p _ (canonK_pcomp h (canonK_pcomp (cn_ppK hY e) hJ))

theorem cn_probeK {Y J : Nat} (hY : Cn Y) (hJ : Cn J) (p : List Nat) : Cn (probeK Y J p) :=
  cn_fold hY hJ p idK cId

theorem probe_fold {Y J : Nat} (hY : Cn Y) (hJ : Cn J) :
    ∀ (p : List Nat), (∀ e ∈ p, e < 6) → ∀ acc, Cn acc →
      p.foldl (fun T e => compT 1408 T (compT 1408 (powsT (tabT (unpack 1408 11 Y)))[e]!
        (tabT (unpack 1408 11 J)))) (tabT (unpack 1408 11 acc)) =
        tabT (unpack 1408 11 (p.foldl (fun a e => pc a (pc (ppK Y e) J)) acc))
  | [], _, _, _ => rfl
  | e :: p, hp, acc, hacc => by
    have he := hp e List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons, powsT_get he, powT_eq hY, compT_unpack (cn_ppK hY e) hJ,
      compT_unpack hacc (canonK_pcomp (cn_ppK hY e) hJ)]
    exact probe_fold hY hJ p (fun e' h' => hp e' (List.mem_cons_of_mem _ h')) _
      (canonK_pcomp hacc (canonK_pcomp (cn_ppK hY e) hJ))

theorem probeT_eq {Y J : Nat} (hY : Cn Y) (hJ : Cn J) {p : List Nat} (hp : ∀ e ∈ p, e < 6) :
    probeT (powsT (tabT (unpack 1408 11 Y))) (tabT (unpack 1408 11 J)) p =
      tabT (unpack 1408 11 (probeK Y J p)) := by
  unfold probeT probeK
  rw [idT_eq]
  exact probe_fold hY hJ p hp idK cId

theorem probePt_lt {Y J : Nat} (hY : Cn Y) (hJ : Cn J) {x : Nat} (hx : x < 1408) :
    ∀ p : List Nat, probePt Y J p x < 1408
  | [] => hx
  | e :: p => iterN_lt (fun _ hi => pt_lt hY hi) (pt_lt hJ (probePt_lt hY hJ hx p)) e

theorem pt_fold {Y J : Nat} (hY : Cn Y) (hJ : Cn J) {x : Nat} (hx : x < 1408) :
    ∀ (p : List Nat) (acc : Nat), Cn acc →
      pt (p.foldl (fun a e => pc a (pc (ppK Y e) J)) acc) x = pt acc (probePt Y J p x)
  | [], _, _ => rfl
  | e :: p, acc, hacc => by
    have hl := probePt_lt hY hJ hx p
    rw [List.foldl_cons, pt_fold hY hJ hx p (pc acc (pc (ppK Y e) J))
        (canonK_pcomp hacc (canonK_pcomp (cn_ppK hY e) hJ)),
      pt_pc hacc hl, pt_pc (cn_ppK hY e) hl, pt_ppK hY (pt_lt hJ hl)]
    rfl

theorem pt_probeK {Y J : Nat} (hY : Cn Y) (hJ : Cn J) {x : Nat} (hx : x < 1408) (p : List Nat) :
    pt (probeK Y J p) x = probePt Y J p x := by
  unfold probeK
  rw [pt_fold hY hJ hx p idK cId, pt_id (probePt_lt hY hJ hx p)]

theorem ne_id_of_pt {X x : Nat} (hx : x < 1408) (h : Nat.beq (pt X x) x = false) :
    Nat.beq X idK = false := by
  cases e : Nat.beq X idK
  · rfl
  · rw [Nat.eq_of_beq_eq_true e, pt_id hx, Nat.beq_refl] at h
    cases h

theorem moved_spec {Y J : Nat} (hY : Cn Y) (hJ : Cn J) {p : List Nat} {e x : Nat}
    (h : movedK Y J p e x = true) : Nat.beq (ppK (probeK Y J p) e) idK = false := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hx : x < 1408 := Nat.blt_eq.mp h1
  have hQ := cn_probeK hY hJ p
  refine ne_id_of_pt hx ?_
  rw [pt_ppK hQ hx, iterN_congr (fun _ hi => pt_lt hQ hi) (fun _ hi => pt_probeK hY hJ hi p) hx]
  cases e' : Nat.beq (iterN (probePt Y J p) e x) x
  · rfl
  · rw [e'] at h2
    cases h2

theorem ordInS_probe {Y J : Nat} (hY : Cn Y) (hJ : Cn J) {p : List Nat} (hp : ∀ e ∈ p, e < 6)
    {x8 x6 x5 x11 : Nat} (h : probeNeg Y J p x8 x6 x5 x11 = true) :
    ordInS (idT 1408) (probeT (powsT (tabT (unpack 1408 11 Y))) (tabT (unpack 1408 11 J)) p) =
      false := by
  obtain ⟨a, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨b, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨c, d⟩ := (bAnd_iff _ _).1 h
  rw [probeT_eq hY hJ hp, ordInS_eq (cn_probeK hY hJ p), moved_spec hY hJ a, moved_spec hY hJ b,
    moved_spec hY hJ c, moved_spec hY hJ d]
  rfl

theorem conjEqOK_of {c : List Nat} {CI X Z : Nat} (hc : lettersOK c = true) (hCI : Cn CI)
    (hi : invEqK 1408 11 (mask 11) (1408 * 11) (WK c) CI = true) (hX : Cn X) (hZ : Cn Z)
    (h : Nat.beq (pc (pc (WK c) X) CI) Z = true) :
    conjEqOK c (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 Z)) = true := by
  obtain ⟨e, hC⟩ := tabW_eq hc
  unfold conjEqOK conjTab
  rw [e, invT_unpack (by norm_num) hi, wordOK_of hc, invOK_unpack hC hCI hi, conjT_unpack hC hCI hX,
    tblEq_eq (canonK_pcomp (canonK_pcomp hC hX) hCI) hZ]
  exact h

@[expose] noncomputable def selK (A B AI BI : Nat) (l : Nat × Bool) : Nat :=
  if l.1 = 0 then (if l.2 then A else AI) else if l.1 = 1 then (if l.2 then B else BI) else idK

@[expose] noncomputable def relK (A B AI BI : Nat) (w : List (Nat × Bool)) : Nat :=
  w.foldl (fun acc l => pc acc (selK A B AI BI l)) idK

theorem sel_eq {A B AI BI : Nat} (hA : Cn A) (hB : Cn B) (hAI : Cn AI) (hBI : Cn BI)
    (l : Nat × Bool) :
    (if l.1 = 0 then (if l.2 then tabT (unpack 1408 11 A) else tabT (unpack 1408 11 AI))
      else if l.1 = 1 then (if l.2 then tabT (unpack 1408 11 B) else tabT (unpack 1408 11 BI))
      else tabT (unpack 1408 11 idK)) = tabT (unpack 1408 11 (selK A B AI BI l)) ∧
      Cn (selK A B AI BI l) := by
  obtain ⟨a, b⟩ := l
  unfold selK
  by_cases h0 : (a, b).1 = 0
  · rw [if_pos h0, if_pos h0]
    cases b
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      exact ⟨rfl, hAI⟩
    · rw [if_pos rfl, if_pos rfl]
      exact ⟨rfl, hA⟩
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : (a, b).1 = 1
    · rw [if_pos h1, if_pos h1]
      cases b
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
        exact ⟨rfl, hBI⟩
      · rw [if_pos rfl, if_pos rfl]
        exact ⟨rfl, hB⟩
    · rw [if_neg h1, if_neg h1]
      exact ⟨rfl, cId⟩

theorem relFold {A B AI BI : Nat} (hA : Cn A) (hB : Cn B) (hAI : Cn AI) (hBI : Cn BI) :
    ∀ (w : List (Nat × Bool)) (acc : Nat), Cn acc →
      w.foldl (fun T l => compT 1408 T
        (if l.1 = 0 then (if l.2 then tabT (unpack 1408 11 A) else tabT (unpack 1408 11 AI))
          else if l.1 = 1 then (if l.2 then tabT (unpack 1408 11 B) else tabT (unpack 1408 11 BI))
          else tabT (unpack 1408 11 idK))) (tabT (unpack 1408 11 acc)) =
        tabT (unpack 1408 11 (w.foldl (fun a l => pc a (selK A B AI BI l)) acc)) ∧
      Cn (w.foldl (fun a l => pc a (selK A B AI BI l)) acc)
  | [], _, h => ⟨rfl, h⟩
  | l :: w, acc, hacc => by
    obtain ⟨e, hs⟩ := sel_eq hA hB hAI hBI l
    rw [List.foldl_cons, List.foldl_cons, e, compT_unpack hacc hs]
    exact relFold hA hB hAI hBI w _ (canonK_pcomp hacc hs)

theorem relTab_eq {A B AI BI : Nat} (hA : Cn A) (hB : Cn B) (hAI : Cn AI) (hBI : Cn BI)
    (w : List (Nat × Bool)) :
    relTab (tabT (unpack 1408 11 A)) (tabT (unpack 1408 11 B)) (tabT (unpack 1408 11 AI))
      (tabT (unpack 1408 11 BI)) w = tabT (unpack 1408 11 (relK A B AI BI w)) ∧
      Cn (relK A B AI BI w) := by
  unfold relTab relK
  rw [idT_eq]
  exact relFold hA hB hAI hBI w idK cId

end CFSG.KD.HN1408

end
