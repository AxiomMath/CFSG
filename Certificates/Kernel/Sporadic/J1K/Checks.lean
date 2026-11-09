module

public import Certificates.Kernel.Sporadic.J1K.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.VO CFSG.Sporadic.J1.Native

noncomputable def decJ1V (d c : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (Nat.land c (nat_lit 15)) (ih (Nat.shiftRight c (nat_lit 4)))) d c

noncomputable def dotJ1 (r v : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih v => List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b c _ => Nat.add (Nat.mul a b) (ih c)) v) r v

noncomputable def mvJ1 (p : Nat) (X : List (List Nat)) (v : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun r _ ih => List.cons (Nat.mod (dotJ1 r v) p) ih) X

noncomputable def fnzJ1 (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Bool.rec (motive := fun _ => Nat) a ih (Nat.beq a (nat_lit 0))) v

noncomputable def negJ1 (p : Nat) (v : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => List.cons (Nat.mod (Nat.sub p x) p) ih) v

noncomputable def keyJ1 (p : Nat) (v : List Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (negJ1 p v) v
    (Nat.ble (fnzJ1 v) (Nat.div (Nat.sub p (nat_lit 1)) (nat_lit 2)))

noncomputable def allLtJ1 (p : Nat) (v : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x p, ih)) v

noncomputable def vorbPtJ1 (p d N : Nat) (A B : List (List Nat)) (PT AL BE : Nat → Nat) (i : Nat) :
    Bool :=
  strictB (PT i) fun c => strictB (r32 AL i) fun a => strictB (r32 BE i) fun b =>
    bAnd(Nat.blt c (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 4) d)),
    bAnd(allLtJ1 p (decJ1V d c),
    bAnd(Nat.blt a N, bAnd(Nat.blt b N,
    bAnd(listEqK (keyJ1 p (mvJ1 p A (decJ1V d c))) (decJ1V d (PT a)),
      listEqK (keyJ1 p (mvJ1 p B (decJ1V d c))) (decJ1V d (PT b)))))))

theorem decJ1V_eq (d c : Nat) : decJ1V d c = decV d c := by
  induction d generalizing c with
  | zero => rfl
  | succ d ih =>
    change Nat.land c 15 :: decJ1V d (Nat.shiftRight c 4) = decV (d + 1) c
    rw [ih]
    unfold decV
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    have e : Nat.mul 4 (k + 1) = 4 + Nat.mul 4 k := by
      simp only [Nat.mul_eq]
      omega
    change Nat.land ((c >>> 4) >>> Nat.mul 4 k) 15 = Nat.land (c >>> Nat.mul 4 (k + 1)) 15
    rw [e, Nat.shiftRight_add]

theorem dotJ1_eq (r v : List Nat) : dotJ1 r v = dotL r v := by
  induction r generalizing v with
  | nil => cases v <;> rfl
  | cons a r ih =>
    cases v with
    | nil => rfl
    | cons b c =>
      change a * b + dotJ1 r c = dotL (a :: r) (b :: c)
      rw [ih, dotL]

theorem mvJ1_eq (p : Nat) (X : List (List Nat)) (v : List Nat) : mvJ1 p X v = mvL p X v := by
  induction X with
  | nil => rfl
  | cons r X ih =>
    change dotJ1 r v % p :: mvJ1 p X v = mvL p (r :: X) v
    rw [ih, dotJ1_eq]
    rfl

theorem fnzJ1_eq (v : List Nat) : fnzJ1 v = firstNZ v := by
  induction v with
  | nil => rfl
  | cons a r ih =>
    change Bool.rec (motive := fun _ => Nat) a (fnzJ1 r) (Nat.beq a 0) = firstNZ (a :: r)
    rw [ih, firstNZ]
    by_cases ha : a = 0
    · subst ha
      rfl
    · have hb : Nat.beq a 0 = false := Bool.eq_false_iff.mpr fun h => ha (Nat.eq_of_beq_eq_true h)
      rw [hb]
      simp [ha]

theorem negJ1_eq (p : Nat) (v : List Nat) : negJ1 p v = negL p v := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    change (p - x) % p :: negJ1 p v = negL p (x :: v)
    rw [ih, negL, negL, List.map_cons]

theorem keyJ1_eq (p : Nat) (v : List Nat) : keyJ1 p v = sgnKey p v := by
  unfold keyJ1 sgnKey
  rw [fnzJ1_eq, negJ1_eq]
  cases h : Nat.ble (firstNZ v) (Nat.div (Nat.sub p 1) 2)
  · have h' : ¬ firstNZ v ≤ (p - 1) / 2 := fun hle =>
      Bool.false_ne_true (h.symm.trans (Nat.ble_eq_true_of_le hle))
    simp [h']
  · have h' : firstNZ v ≤ (p - 1) / 2 := Nat.le_of_ble_eq_true h
    simp [h']

theorem allLtJ1_eq (p : Nat) (v : List Nat) : allLtJ1 p v = List.all v (fun x => Nat.blt x p) := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    change Bool.rec (motive := fun _ => Bool) false (allLtJ1 p v) (Nat.blt x p) = _
    rw [ih, List.all_cons]
    cases Nat.blt x p <;> rfl

theorem vorbPtJ1_eq (p d N : Nat) (A B : List (List Nat)) (PT AL BE : Nat → Nat) :
    vorbPtJ1 p d N A B PT AL BE = vorbPtK p d N (sgnKey p) A B PT AL BE := by
  funext i
  unfold vorbPtJ1 vorbPtK
  simp only [decJ1V_eq, mvJ1_eq, keyJ1_eq, allLtJ1_eq]

theorem orbPtJ1_ok : allN (nat_lit 1540) (vorbPtJ1 (nat_lit 11) (nat_lit 7) (nat_lit 1540) (mA ())
    (mB ()) (r32 PT) AL BE) = true := by quickRfl

theorem orbHd_ok : orbHd = true := by quickRfl

theorem orbPt_ok : orbPt = true := by
  unfold orbPt
  rw [← vorbPtJ1_eq]
  exact orbPtJ1_ok

theorem orbSort_ok : orbSort = true := by quickRfl
theorem projSort_ok : projSort = true := by quickRfl
theorem invAB_ok : invAB = true := by quickRfl

noncomputable def GJN (c x : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), r32 AL x, nIf(Nat.beq c (nat_lit 1), r32 AI x,
    nIf(Nat.beq c (nat_lit 2), r32 BE x, r32 BI x)))

def decJ1 : Nat → Int
  | 0 => 1
  | 1 => -1
  | 2 => 2
  | _ => -2

noncomputable def wordJ1 (ws : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => strictN ih (GJN c)) ws

noncomputable def wordsJ1L : List (List Nat) :=
  [[0], [2],
  [3, 3, 1, 3, 1, 3, 3, 0, 2, 2, 2, 2, 0, 0, 3, 0, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 3, 0, 0, 0, 0, 0,
    3, 3],
  [3, 3, 0, 3, 0, 3, 3, 0, 2, 0, 2, 0, 2, 2, 2, 0, 3, 0, 2, 0, 0, 0, 0, 3, 3, 0, 2, 0, 2, 0, 3, 0,
    2, 2, 0, 3, 0, 0, 2, 2],
  [1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 2, 2, 0,
    3, 0, 3, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 3, 0, 3, 3, 0, 2, 0, 2, 2, 0, 0, 0, 2, 0, 3, 0, 3, 0]]

noncomputable def wordsChkJ1 (w : List Nat) (j : Nat) : Bool :=
  allN (nat_lit 1540) fun x => Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (wordJ1 w x)

theorem wordsJ1_ok : allN 5 (fun j => wordsChkJ1 (List.getD wordsJ1L j []) j) = true := by
  quickRfl

theorem GJN_eq (c x : Nat) : GJN c x = GJ (decJ1 c) x := by
  rcases c with _ | _ | _ | c <;> rfl

theorem foldr_GJ_map (ws : List Nat) (x : Nat) : List.foldr GJ x (ws.map decJ1) = wordJ1 ws x := by
  induction ws with
  | nil => rfl
  | cons c ws ih =>
    rw [List.map_cons, List.foldr_cons, ih, ← GJN_eq]
    change GJN c (wordJ1 ws x) = strictN (wordJ1 ws x) (GJN c)
    cases wordJ1 ws x <;> rfl

theorem chainWords_get (j : Nat) : (chainWords ())[j]! = (List.getD wordsJ1L j []).map decJ1 := by
  rcases Nat.lt_or_ge j 5 with h | h
  · rcases j with _ | _ | _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [wordsJ1L] using h)]
    exact getElem!_neg _ _ (by simpa [chainWords] using h)

theorem wordsOK_ok : wordsOK = true := by
  simp only [wordsOK, chainWords_get, foldr_GJ_map]
  exact wordsJ1_ok

theorem invL_ok : invL = true := by quickRfl
theorem tree0_ok : tree0 = true := by quickRfl
theorem tree1_ok : tree1 = true := by quickRfl
theorem sch1_ok : sch1 = true := by quickRfl
theorem term_ok : term = true := by quickRfl
theorem subPt_ok : subPt = true := by quickRfl
theorem subRep_ok : subRep = true := by quickRfl
theorem subTree_ok : CFSG.KC.Enum.allN 21 subTree = true := by quickRfl
theorem imAt_ok : CFSG.KC.Enum.allN 21 imAt = true := by quickRfl
theorem der_ok : der = true := by quickRfl

@[expose] noncomputable def schG0 (s : Nat) : Bool :=
  allN (nat_lit 308) fun d => strictB (Nat.add (Nat.mul s (nat_lit 308)) d) fun k =>
    bAnd(schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 2) (nat_lit 0) (nat_lit 0) k,
      schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 2) (nat_lit 0) (nat_lit 2) k)

end CertificateChecks.KernelSpor.J1K

#kon_slices CertificateChecks.KernelSpor.J1K.schG0 0 5

end
