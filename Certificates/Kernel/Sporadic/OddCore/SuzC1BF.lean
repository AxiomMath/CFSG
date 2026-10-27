module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1BD
public import Certificates.Kernel.Sporadic.OddCore.SuzMGF
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzC1BF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.Sporadic.SuzRecog.C1ModelData CFSG.PSL3Four.Native
open CFSG.ComponentClassification.AS81.SuzB0
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF CertificateChecks.KernelSpor.SuzMGF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "qc" => pcomp 42 6 (mask 6)
local notation "qn" => canonK 42 6 (mask 6) (42 * 6)
local notation "Iq" => pidn 42 6
local notation "T" => SuzC1BT
local notation "W0" => SuzTwG 6
local notation "Rho" => SuzTwG 2
local notation "RhoI" => SuzTwGI 2
local notation "zC" => CFSG.Sporadic.SuzRecog.C1Model.zT

@[expose] noncomputable def q30K : Nat :=
  pc (pc (pc (pc Id (KernelLC.SuzB0Q.F 1)) (KernelLC.SuzB0Q.F 2)) (KernelLC.SuzB0Q.F 3))
    (KernelLC.SuzB0Q.F 4)

@[expose] noncomputable def labK (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => if Nat.beq (labList.getD j 0) x && Nat.blt x 1782 then j else ih) k

@[expose] noncomputable def wq (G : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) Iq (fun k _ ih => qc (G k) ih) w

@[expose] def fixL : List Nat :=
  [39, 129, 143, 199, 218, 229, 244, 314, 356, 403, 423, 482, 500, 503, 508, 562, 600, 614, 632,
    638, 727, 797, 801, 813, 889, 920, 958, 1003, 1095, 1138, 1184, 1282, 1283, 1411, 1447, 1474,
    1529, 1550, 1555, 1713, 1754, 1775]

@[expose] noncomputable def resK (X i : Nat) : Nat := labK 42 (pg 11 (mask 11) X (labList.getD i 0))

theorem kT0 : Nat.beq (T 0) (cWK CFSG.Sporadic.SuzRecog.LocalR.lambda4Word) = true := by quickRfl
theorem kT1 : Nat.beq (T 1) (cWK [6, 9, 2]) = true := by quickRfl
theorem kT3 : Nat.beq (T 3) (pc (pc (cWK [6, 8, 7, 4, 7, 4]) q30K) (SuzInvT1.F 0)) = true := by
  quickRfl
theorem kT4 : Nat.beq (T 4) (pc Suz2306.B0 Suz2306.B1) = true := by quickRfl
theorem kT6 : Nat.beq (T 6) (pc (pc (T 1) (T 4)) (T 2)) = true := by quickRfl
theorem kT8 : Nat.beq (T 8) (pc (pc (pc W0 (T 6)) W0) (T 7)) = true := by quickRfl
theorem kT9 : Nat.beq (T 9) (powK (pc (T 7) (powK (T 8) 7)) 2) = true := by quickRfl
theorem kT10 : Nat.beq (T 10) (pc (powK (pc W0 (pc (pc (T 4) Suz2306.B0) (T 5))) 8) (T 4)) =
    true := by quickRfl
theorem kT11 : Nat.beq (T 11) (pc (pc Rho W0) RhoI) = true := by quickRfl
theorem kT12 : Nat.beq (T 12) (pc (pc Rho (T 11)) RhoI) = true := by quickRfl

theorem kCan : (cn (T 2) && cn (T 5) && cn (T 7) && cn Suz2306.B0 && cn Suz2306.B1 &&
    cn (SuzInvT1.F 0) && qn Iq && idK 42 6 (mask 6) &&
    allN 3 (fun i => qn (SuzC1BR i)) && allN 6 (fun i => qn (SuzC1BG i))) = true := by
  quickRfl

theorem kInv : (ie (T 1) (T 2) && ie (T 4) (T 5) && ie (T 6) (T 7)) = true := by quickRfl

theorem kBindG : (Nat.beq gTabs.size 6 && allN 6 fun k => bindArrK gTabs[k]! 42 6 (SuzC1BG k)) =
    true := by quickRfl

theorem kFix : fixedK 1782 11 (mask 11) W0 fixL = true := by quickRfl

theorem kLab : allN 42 (fun i => decide (labList.getD i 0 < 1782) &&
    (pg 11 (mask 11) W0 (labList.getD i 0) == labList.getD i 0) &&
    (labK 42 (labList.getD i 0) == i)) = true := by quickRfl

theorem kFixLab : fixL.all (fun x => decide (labK 42 x < 42) && labArr[labK 42 x]! == x) = true := by
  quickRfl

theorem kRes : (allN 42 (fun i => Nat.beq (resK (SuzInvT1.F 0) i) (pg 6 (mask 6) (SuzC1BR 0) i)) &&
    allN 42 (fun i => Nat.beq (resK (T 9) i) (pg 6 (mask 6) (SuzC1BR 1) i)) &&
    allN 42 (fun i => Nat.beq (resK (SuzMGG 4) i) (pg 6 (mask 6) (SuzC1BR 2) i))) = true := by
  quickRfl

theorem kLetters : (resT1Word.all (· < 3) && resZWord.all (· < 3) && tauSWord.all (· < 3) &&
    allN 3 fun k => (gensSWords.getD k []).all (· < 2)) = true := by quickRfl

theorem negRes : Bool.not (allN 42 fun i =>
    Nat.beq (resK (SuzInvT1.F 0) i) (pg 6 (mask 6) (Nat.xor (SuzC1BR 0) 1) i)) = true := by
  quickRfl

theorem negFix : Bool.not (fixedK 1782 11 (mask 11) W0 fixL.tail) = true := by quickRfl

theorem pc' {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    P (comp 1782 a b) (pc A B) := p_comp ha hb

theorem pId' : P (idTab 1782) Id := pidn_P

theorem pPow {a : Array Nat} {A : Nat} (ha : P a A) : ∀ k, P (powTab 1782 a k) (powK A k)
  | 0 => pId'
  | k + 1 => pc' ha (pPow ha k)

theorem beqP {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    (a == b) = Nat.beq A B := by
  rw [ha.1, hb.1]
  exact CFSG.KS.PEnum.beq_unpack ha.2 hb.2

theorem sizeP {a : Array Nat} {A : Nat} (ha : P a A) : a.size = 1782 := by
  rw [ha.1]
  simp [unpack]

theorem cWord_P : ∀ w : List Nat, (∀ k ∈ w, k < 10) →
    P (CFSG.Sporadic.SuzRecog.cWord w) (cWK w)
  | [], _ => pId'
  | k :: w, h => by
    unfold CFSG.Sporadic.SuzRecog.cWord cWK
    rw [List.foldr_cons]
    exact p_comp (pC (h k List.mem_cons_self))
      (cWord_P w fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem can : cn (T 2) = true ∧ cn (T 5) = true ∧ cn (T 7) = true ∧ cn Suz2306.B0 = true ∧
    cn Suz2306.B1 = true ∧ cn (SuzInvT1.F 0) = true ∧ qn Iq = true ∧ idK 42 6 (mask 6) = true ∧
    (∀ i < 3, qn (SuzC1BR i) = true) ∧ (∀ i < 6, qn (SuzC1BG i) = true) := by
  have h := kCan
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, allN_spec h.1.2, allN_spec h.2⟩

theorem inv : ie (T 1) (T 2) = true ∧ ie (T 4) (T 5) = true ∧ ie (T 6) (T 7) = true := by
  have h := kInv
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pw0 : P w0T W0 := pW0
theorem prho : P rhoT Rho := pRho
theorem prhoI : P rhoI RhoI := (p_inv (by norm_num) pRho.1).1
theorem pt1 : P tTab (SuzInvT1.F 0) := ⟨SuzInv.run_eq1 (k := 0) (by norm_num), can.2.2.2.2.2.1⟩
theorem ptau : P tauT (SuzMGG 4) := pTauM
theorem pt0 : P (tArr 0) (SuzTP 0) :=
  ⟨(rep_facts (i := 0) (by norm_num)).1, (rep_facts (i := 0) (by norm_num)).2.1⟩
theorem pB0 : P b0Arr Suz2306.B0 := ⟨Suz2306.b0Arr_eq, can.2.2.2.1⟩
theorem pB1 : P b1Arr Suz2306.B1 := ⟨Suz2306.b1Arr_eq, can.2.2.2.2.1⟩

theorem pl4 : P l4T (T 0) := by
  have h := p_eq (cWord_P CFSG.Sporadic.SuzRecog.LocalR.lambda4Word (by decide)) kT0
  exact h
theorem pgc : P gcT (T 1) := by
  have h := p_eq (cWord_P [6, 9, 2] (by decide)) kT1
  exact h
theorem pgcI : P gcI (T 2) := (p_invR pgc inv.1 can.1).1

theorem pq30 : P qProds[30]! q30K := by
  have e : qProds[30]! = compA 1782 (compA 1782 (compA 1782 (compA 1782 (idA 1782) (qArr 1))
      (qArr 2)) (qArr 3)) (qArr 4) := by
    unfold qProds
    rw [getElem!_pos _ 30 (by simp), Array.getElem_ofFn]
    rfl
  rw [e]
  exact p_comp (p_comp (p_comp (p_comp pidn_P (pQ (by norm_num))) (pQ (by norm_num)))
    (pQ (by norm_num))) (pQ (by norm_num))

theorem prhoDec : P rhoDecT (T 3) := by
  have h := p_eq (pc' (pc' (cWord_P [6, 8, 7, 4, 7, 4] (by decide)) pq30) pt1) kT3
  exact h
theorem pbg : P bgT (T 4) := by
  have h := p_eq (pc' pB0 pB1) kT4
  exact h
theorem pbgI : P bgI (T 5) := (p_invR pbg inv.2.1 can.2.1).1
theorem pbw : P bwT (T 6) := by
  have h := p_eq (pc' (pc' pgc pbg) pgcI) kT6
  unfold bwT conjTab
  exact h
theorem pbwI : P bwI (T 7) := (p_invR pbw inv.2.2 can.2.2.1).1
theorem pcw : P cwT (T 8) := by
  have h := p_eq (pc' (pc' (pc' pw0 pbw) pw0) pbwI) kT8
  exact h
theorem pz : P zC (T 9) := by
  have h := p_eq (pPow (pc' pbwI (pPow pcw 7)) 2) kT9
  exact h
theorem ph : P hT (T 10) := by
  have h := p_eq (pc' (pPow (pc' pw0 (pc' (pc' pbg pB0) pbgI)) 8) pbg) kT10
  unfold hT conjTab
  exact h
theorem pr1 : P r1T (T 11) := by
  have h := p_eq (pc' (pc' prho pw0) prhoI) kT11
  unfold r1T conjTab
  exact h
theorem pr2 : P r2T (T 12) := by
  have h := p_eq (pc' (pc' prho pr1) prhoI) kT12
  unfold r2T conjTab
  exact h

theorem permOK_P {a : Array Nat} {i : Nat} (hi : i < 8) (ha : P a (SuzTwG i)) :
    CFSG.Sporadic.SuzOddCore.permOK 1782 a = true := by
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [sizeP ha, (p_inv hi ha.1).2]
  rfl

theorem baseCheck_true : baseCheck = true := by
  unfold baseCheck
  simp only [permOK_P (by norm_num) pw0, permOK_P (by norm_num) prho, sizeP pgcI, sizeP prhoI,
    sizeP pbgI, sizeP pbwI,
    beqP (pc' pgcI pgc) pId', beqP pw0 (pc' (pc' pgc pl4) pgcI), beqP prho prhoDec,
    beqP (pc' prhoI prho) pId', beqP (pc' pw0 pw0) pId', beqP pw0 pId',
    beqP (pc' pw0 pr1) (pc' pr1 pw0), beqP pr1 pw0, beqP pr2 (pc' pw0 pr1),
    beqP (pc' ptau ptau) pId', beqP (pc' ptau pw0) (pc' pw0 ptau),
    beqP (pc' ptau pr1) (pc' pr2 ptau), beqP (pc' ptau prho) (pc' prhoI ptau),
    beqP (pc' pbgI pbg) pId', beqP (pc' pbwI pbw) pId',
    beqP (pc' pz pw0) (pc' pw0 pz), beqP (pc' pz pr1) (pc' pr1 pz),
    beqP (pc' pz prho) (pc' prho pz), beqP (pc' ph pt0) (pc' pw0 ph)]
  quickRfl

@[expose] def Q (a : Array Nat) (A : Nat) : Prop := a = unpack 42 6 A ∧ qn A = true

theorem qc' {a b : Array Nat} {A B : Nat} (ha : Q a A) (hb : Q b B) : Q (comp 42 a b) (qc A B) := by
  rw [ha.1, hb.1]
  exact ⟨compA_unpack ha.2 hb.2, canonK_pcomp ha.2 hb.2⟩

theorem qId : Q (idTab 42) Iq := ⟨(idK_sound can.2.2.2.2.2.2.2.1).symm, can.2.2.2.2.2.2.1⟩

theorem beqQ {a b : Array Nat} {A B : Nat} (ha : Q a A) (hb : Q b B) :
    (a == b) = Nat.beq A B := by
  rw [ha.1, hb.1]
  exact CFSG.KS.PEnum.beq_unpack ha.2 hb.2

theorem wordQ {gens : Array Tab} {G : Nat → Nat} (hg : ∀ k < gens.size, Q gens[k]! (G k)) :
    ∀ w : List Nat, (∀ k ∈ w, k < gens.size) → Q (wordTab 42 gens w) (wq G w)
  | [], _ => qId
  | k :: w, h => by
    unfold wordTab wq
    rw [List.foldr_cons]
    exact qc' (hg k (h k List.mem_cons_self))
      (wordQ hg w fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem qG {k : Nat} (hk : k < 6) : Q gTabs[k]! (SuzC1BG k) :=
  ⟨(binds_of_check kBindG).2 k hk, can.2.2.2.2.2.2.2.2.2 k hk⟩

theorem qS : ∀ k < gensS.size, Q gensS[k]! (SuzC1BG k) := by
  intro k hk
  have hk3 : k < 3 := by simpa [gensS] using hk
  have e : gensS[k]! = gTabs[k]! := by interval_cases k <;> rfl
  rw [e]
  exact qG (by omega)

theorem qR4 : Q (r₄T ()) (qc (SuzC1BG 4) (SuzC1BG 5)) := by
  have e5 : g₅T = gTabs[4]! := rfl
  have e6 : g₆T = gTabs[5]! := rfl
  unfold r₄T
  rw [e5, e6]
  exact qc' (qG (by norm_num)) (qG (by norm_num))

theorem scatter_get : ∀ k, (List.foldl (fun b a => b.setIfInBounds labArr[a]! a)
    (Array.replicate 1782 0) (List.range' 0 k)).size = 1782 ∧ ∀ x,
    (List.foldl (fun b a => b.setIfInBounds labArr[a]! a) (Array.replicate 1782 0)
      (List.range' 0 k))[x]! = labK k x
  | 0 => by
    refine ⟨by simp, fun x => ?_⟩
    by_cases hx : x < 1782
    · rw [getElem!_pos _ x (by simp only [List.range'_zero, List.foldl_nil, Array.size_replicate]; exact hx)]
      simp
      rfl
    · rw [getElem!_neg _ x (by simp only [List.range'_zero, List.foldl_nil, Array.size_replicate]; exact hx)]
      rfl
  | k + 1 => by
    obtain ⟨hs, hv⟩ := scatter_get k
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    refine ⟨by simp [hs], fun x => ?_⟩
    have hl : labArr[k]! = labList.getD k 0 := by
      simp [labArr, List.getD_eq_getElem?_getD]
    have hK : labK (k + 1) x =
        if Nat.beq (labList.getD k 0) x && Nat.blt x 1782 then k else labK k x := rfl
    by_cases hx : x < 1782
    · rw [getElem!_pos _ x (by simp [hs]; exact hx), Array.getElem_setIfInBounds (by rw [hs]; exact hx),
        hK, hl, ← getElem!_pos _ x (by rw [hs]; exact hx), hv x]
      by_cases e : labList.getD k 0 = x
      · have hc : (Nat.beq (labList.getD k 0) x && Nat.blt x 1782) = true := by
          rw [e, Nat.beq_refl, Bool.true_and]
          exact Nat.blt_eq.mpr hx
        rw [ite_eq_left e, ite_eq_left hc]
      · have hc : ¬ (Nat.beq (labList.getD k 0) x && Nat.blt x 1782) = true := by
          rw [beq_false e, Bool.false_and]
          exact Bool.false_ne_true
        rw [ite_eq_right e, ite_eq_right hc]
    · have hb : Nat.blt x 1782 = false := Bool.eq_false_iff.2 fun h => hx (Nat.blt_eq.mp h)
      rw [getElem!_neg _ x (by simpa [hs] using hx), hK, hb, Bool.and_false, ite_eq_right (by decide),
        ← hv x, getElem!_neg _ x (by rw [hs]; exact hx)]

theorem labInv_get (x : Nat) : labInv[x]! = labK 42 x := by
  have e : labInv = List.foldl (fun b a => b.setIfInBounds labArr[a]! a)
      (Array.replicate 1782 0) (List.range' 0 42) := by
    simp [labInv, Id.run]
    rfl
  rw [e]
  exact (scatter_get 42).2 x

theorem unpack_getElem! {n w p i : Nat} (hi : i < n) : (unpack n w p)[i]! = pg w (mask w) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem labArr_get {i : Nat} : labArr[i]! = labList.getD i 0 := by
  simp [labArr, List.getD_eq_getElem?_getD]

theorem resTab_unpack {X R : Nat} {j : Nat} (hj : j < 3)
    (h : allN 42 (fun i => Nat.beq (resK X i) (pg 6 (mask 6) R i)) = true)
    (hR : R = SuzC1BR j) : Q (resTab (unpack 1782 11 X)) R := by
  refine ⟨?_, by rw [hR]; exact can.2.2.2.2.2.2.2.2.1 j hj⟩
  apply Array.ext
  · simp [resTab, unpack]
  · intro i h1 _
    have hi : i < 42 := by simpa [resTab] using h1
    have hb := allN_spec kLab i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    simp only [resTab, Array.getElem_ofFn, Fin.getElem!_fin]
    rw [← getElem!_pos (unpack 42 6 R) i (by rw [CFSG.KS.PEnum.unpack_size]; exact hi),
      unpack_getElem! hi, labArr_get, unpack_getElem! hb.1.1, labInv_get]
    exact Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem all_filter {l : List Nat} {p C : Nat → Bool} :
    l.all (fun x => !p x || C x) = (l.filter p).all C := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.filter_cons, ih]
    cases p a <;> simp

theorem all_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ k ∈ l, p k = q k) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun k hk => h k (List.mem_cons_of_mem _ hk)]

theorem allBelow_of {m : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) : allBelow m f = true := by
  unfold allBelow
  rw [List.all_eq_true]
  exact fun i hi => h i (List.mem_range.1 hi)

theorem resCheck_true : resCheck = true := by
  have hres := kRes
  simp only [Bool.and_eq_true] at hres
  have q0 : Q (resTab tTab) (SuzC1BR 0) := by
    rw [pt1.1]
    exact resTab_unpack (j := 0) (by norm_num) hres.1.1 rfl
  have q1 : Q (resTab zC) (SuzC1BR 1) := by
    rw [pz.1]
    exact resTab_unpack (j := 1) (by norm_num) hres.1.2 rfl
  have q2 : Q (resTab tauT) (SuzC1BR 2) := by
    rw [ptau.1]
    exact resTab_unpack (j := 2) (by norm_num) hres.2 rfl
  have hlet := kLetters
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hlet
  have hS : gensS.size = 3 := rfl
  have q2g : ∀ k < (#[resTab tTab, resTab zC] : Array Tab).size,
      Q (#[resTab tTab, resTab zC] : Array Tab)[k]!
        ((fun j => if j = 0 then SuzC1BR 0 else SuzC1BR 1) k) := by
    intro k hk
    have hk2 : k < 2 := by simpa using hk
    interval_cases k
    · exact q0
    · exact q1
  have hfix : (List.range 1782).filter (fun x => w0T[x]! == x) = fixL := by
    have h := fixedK_sound kFix
    rw [← pw0.1] at h
    unfold CFSG.Certificates.Native.fixedList at h
    exact h
  unfold resCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨rfl, allBelow_of fun i hi => ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have hb := allN_spec kLab i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [labArr_get, pw0.1, unpack_getElem! hb.1.1, labInv_get]
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
  · unfold allBelow
    rw [all_filter, hfix]
    simp only [labInv_get]
    exact kFixLab
  · rw [beqQ q0 (wordQ qS _ fun k hk => by rw [hS]; exact hlet.1.1.1 k hk)]
    quickRfl
  · rw [beqQ q1 (wordQ qS _ fun k hk => by rw [hS]; exact hlet.1.1.2 k hk)]
    quickRfl
  · refine allBelow_of fun k hk => ?_
    rw [beqQ (qS k (by rw [hS]; exact hk))
      (wordQ q2g _ fun j hj => by
        have h := allN_spec hlet.2 k hk
        simp only [List.all_eq_true, decide_eq_true_eq] at h
        simpa using h j hj)]
    interval_cases k <;> quickRfl
  · rw [beqQ q2 (qc' (wordQ qS _ fun k hk => by rw [hS]; exact hlet.1.2 k hk) qR4)]
    quickRfl

end CertificateChecks.KernelSpor.SuzC1BF

end
