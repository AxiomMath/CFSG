module

public import Certificates.Kernel.Sporadic.OddCore.SuzFbC
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.HeFixKFix
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Intervals

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "cn7" => canonK 64 7 (mask 7) (64 * 7)

theorem beqN (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · rw [Bool.eq_false_iff.2 (fun e => h (Nat.eq_of_beq_eq_true e))]
    simpa using h

theorem allLt_congr' {n : Nat} {p r : Nat → Bool} (h : ∀ i < n, p i = r i) :
    CFSG.Monster.B.Co2.Native.allLt n p = CFSG.Monster.B.Co2.Native.allLt n r := by
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, CFSG.Monster.B.Co2.allLt_iff]
  exact ⟨fun H i hi => (h i hi) ▸ H i hi, fun H i hi => (h i hi).symm ▸ H i hi⟩

theorem allLt_allN {n : Nat} {p r : Nat → Bool} (h : ∀ i < n, p i = r i) :
    CFSG.Monster.B.Co2.Native.allLt n p = allN n r := by
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff]
  exact ⟨fun H => PackFld.allN_of_forall fun i hi => (h i hi) ▸ H i hi,
    fun H i hi => (h i hi).symm ▸ allN_spec H i hi⟩

theorem pgl {A : Nat} (hA : canonK 1782 11 (mask 11) (1782 * 11) A = true) {y : Nat}
    (hy : y < 1782) : pgk A y < 1782 :=
  CFSG.KC.HeFixK.pg_lt_of_canonK hA hy

theorem get_P {a : Array Nat} {A : Nat} (ha : P a A) {y : Nat} (hy : y < 1782) :
    a[y]! = pgk A y := by
  rw [ha.1, CFSG.KC.HeFixK.unpack_getElem! hy]

theorem lt_of_P {a : Array Nat} {A : Nat} (ha : P a A) {y : Nat} (hy : y < 1782) :
    a[y]! < 1782 := by
  rw [get_P ha hy]
  exact pgl ha.2 hy

theorem cover' {L N : Nat} {Q : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → Q i) : ∀ i < L * N, Q i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem rec_tabs {n w cnt : Nat} {T PL : Nat → Nat} {i : Nat} (hi : i < cnt) :
    (penumRec n w cnt T PL).tabs[i]! = unpack n w (T i) := by
  rw [penumRec_eq]
  exact ofFn_get (fun i => unpack n w (T i)) hi

theorem rec_par {n w cnt : Nat} {T PL : Nat → Nat} {i : Nat} (hi : i < cnt) :
    (penumRec n w cnt T PL).par[i]! = parOf PL i := by
  rw [penumRec_eq]
  exact ofFn_get (fun i => parOf PL i) hi

theorem rec_lab {n w cnt : Nat} {T PL : Nat → Nat} {i : Nat} (hi : i < cnt) :
    (penumRec n w cnt T PL).lab[i]! = labOf PL i := by
  rw [penumRec_eq]
  exact ofFn_get (fun i => labOf PL i) hi

theorem cntE : SuzFbE.cnt = 25920 := rfl

theorem gOK : GensOK 64 7 10 SuzFbE.G matTabs := by
  refine ⟨(binds_of_check SuzAB.kBind).1, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec kG j hj)]
  exact ⟨SuzAB.facts.1 j hj, SuzAB.facts.2.1 j hj⟩

theorem ptE : ∀ i < SuzFbE.cnt, penumPtK 64 7 (mask 7) (64 * 7) false SuzFbE.G SuzFbE.GI 10
    SuzFbE.cnt SuzFbE.T SuzFbE.PL SuzFbE.POS SuzFbE.SRT SuzFbE.SRI i = true := by
  intro i hi
  have key := cover' (L := 320) (N := 81) (by norm_num) (Q := fun i => i < SuzFbE.cnt →
      penumPtK 64 7 (mask 7) (64 * 7) false SuzFbE.G SuzFbE.GI 10 SuzFbE.cnt SuzFbE.T SuzFbE.PL
        SuzFbE.POS SuzFbE.SRT SuzFbE.SRI i = true)
    (fun s hs i h1 h2 hc => by
      have hsl := slPAll s hs
      unfold slP at hsl
      exact penumSl_spec hsl i h1 h2 hc)
  rw [cntE] at hi
  exact key i (by omega) (by rw [cntE]; exact hi)

theorem mE : matEnum = penumRec 64 7 SuzFbE.cnt SuzFbE.T SuzFbE.PL := by
  unfold matEnum
  exact (penumK_left_sound kSz gOK kHd ptE).1

theorem canT {i : Nat} (hi : i < 25920) : cn7 (SuzFbE.T i) = true :=
  penumPt_canon (ptE i (by rw [cntE]; exact hi))

theorem tab_get {i : Nat} (hi : i < 25920) : matEnum.tabs[i]! = unpack 64 7 (SuzFbE.T i) := by
  rw [mE]
  exact rec_tabs (by rw [cntE]; exact hi)

theorem parLt {i : Nat} (hi : i < 25920) (h0 : i ≠ 0) : parOf SuzFbE.PL i < i := by
  have h := allN_spec kPar i hi
  rw [Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
  exact Nat.blt_eq.mp h

theorem tree_eq : ∀ (f i : Nat), i < 25920 → treeWord matEnum f i = pathW SuzFbE.PL f i
  | 0, _, _ => rfl
  | f + 1, i, hi => by
    by_cases h0 : i = 0
    · subst h0
      rfl
    · have hp := parLt hi h0
      have e1 : treeWord matEnum (f + 1) i =
          matEnum.lab[i]! :: treeWord matEnum f matEnum.par[i]! := by
        rw [treeWord]
        simp [h0]
      have e2 : pathW SuzFbE.PL (f + 1) i =
          Bool.rec (motive := fun _ => List Nat)
            (labOf SuzFbE.PL i :: pathW SuzFbE.PL f (parOf SuzFbE.PL i)) [] (Nat.beq i 0) := rfl
      have e3 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      have hl : matEnum.lab[i]! = labOf SuzFbE.PL i := by
        rw [mE]
        exact rec_lab (by rw [cntE]; exact hi)
      have hpr : matEnum.par[i]! = parOf SuzFbE.PL i := by
        rw [mE]
        exact rec_par (by rw [cntE]; exact hi)
      rw [e1, e2, e3, hl, hpr, tree_eq f _ (by omega)]

theorem fixInv_eq {X : Nat} (hX : cn7 X = true) : fixInv (unpack 64 7 X) = fixInvK X := by
  have hI : cn7 (pidn 64 7) = true := SuzAB.facts.2.2.2.2.1
  have hc : comp 64 (unpack 64 7 X) (unpack 64 7 X) = unpack 64 7 (pcomp 64 7 (mask 7) X X) :=
    compA_unpack hX hX
  have hid : idTab 64 = unpack 64 7 (pidn 64 7) := SuzAB.facts.2.2.2.2.2.symm
  unfold fixInv fixInvK
  rw [CFSG.KC.HeFixK.unpack_getElem! (by norm_num : 1 < 64), hc, hid,
    beq_unpack (canonK_pcomp hX hX) hI, beqN, CFSG.KS.Raw.Orb.bAnd_eq]

theorem memK_iff {L : List Nat} {i : Nat} : memK L i = true ↔ i ∈ L := by
  induction L with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons x L ih =>
    change bIf(Nat.beq x i, true, memK L i) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bIf_eq, List.mem_cons]
    by_cases h : x = i
    · subst h
      simp
    · rw [Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)]
      simp only [Bool.false_eq_true, ↓reduceIte, ih]
      exact ⟨Or.inr, fun h' => h'.resolve_left fun e => h e.symm⟩

theorem invPos_eq : invPos = SuzFbIL := by
  have hq : ∀ i < 25920, fixInv matEnum.tabs[i]! = memK SuzFbIL i := by
    intro i hi
    rw [tab_get hi, fixInv_eq (canT hi)]
    have hs : i / 1620 < 16 := by omega
    have h := invSlAll (i / 1620) hs
    unfold invSl at h
    have h2 := allN_spec h (i % 1620) (Nat.mod_lt _ (by norm_num))
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h2
    have e : Nat.add (Nat.mul 1620 (i / 1620)) (i % 1620) = i := Nat.div_add_mod i 1620
    rw [e, CFSG.KS.Raw.Orb.bIf_eq] at h2
    cases hf : fixInvK (SuzFbE.T i) <;> cases hm : memK SuzFbIL i <;> simp_all
  unfold invPos
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_lt_range.filter _) kSorted
    fun a => ?_
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨ha, hf⟩
    rw [hq a ha] at hf
    exact memK_iff.1 hf
  · intro ha
    have hb := kBound a ha
    exact ⟨hb, by rw [hq a hb]; exact memK_iff.2 ha⟩

theorem IL_eq : SuzFbIL = (List.range 76).map ipos := by
  refine List.ext_getElem (by rw [kLen, List.length_map, List.length_range]) fun n h1 _ => ?_
  rw [List.getElem_map, List.getElem_range]
  unfold ipos
  rw [nget_get]

theorem letters {w : List Nat} (h : lettersK w = true) : ∀ k ∈ w, k < 10 := by
  induction w with
  | nil => exact fun _ hk => absurd hk List.not_mem_nil
  | cons a w ih =>
    change bAnd(Nat.blt a 10, lettersK w) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Nat.blt_eq.mp h1
    · exact ih h2 k hk

theorem word_facts {q : Nat} (hq : q < 76) : ipos q < 25920 ∧ mWK (wq q) = SuzFbE.T (ipos q) ∧
    ∀ k ∈ wq q, k < 10 := by
  have h := allN_spec kWord q hq
  unfold wordOK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  change bAnd(Nat.blt (ipos q) 25920,
    bAnd(Nat.beq (mWK (wq q)) (SuzFbE.T (ipos q)), lettersK (wq q))) = true at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3, letters h4⟩

theorem enumWord_eq {q : Nat} (hq : q < 76) : enumWord (ipos q) = wq q :=
  tree_eq 25920 _ (word_facts hq).1

theorem matWord_eq {w : List Nat} (hw : ∀ k ∈ w, k < 10) :
    matWord w = unpack 64 7 (mWK w) ∧ cn7 (mWK w) = true :=
  wordTabK_eq SuzAB.facts.2.2.2.2.2.symm SuzAB.facts.2.2.2.2.1 w fun j hj =>
    ⟨SuzAB.facts.1 j (hw j hj), SuzAB.facts.2.1 j (hw j hj)⟩

theorem pL {q : Nat} (hq : q < 76) : P (liftTab (ipos q)) (SuzFbL q) := by
  have hs : q / 6 < 13 := by omega
  have h := allBlk_spec (liftSlAll (q / 6) hs) (q % 6) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 6 (q / 6)) (q % 6) = q := Nat.div_add_mod q 6
  rw [e, Nat.blt_eq.mpr hq] at h
  change liftOK q = true at h
  unfold liftOK at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  unfold liftTab
  rw [enumWord_eq hq]
  exact p_eq (cWord_P _ (word_facts hq).2.2) h2

theorem pQE {j : Nat} (hj : j < 128) : P qElts[j]! (KernelLC.SuzB0QE j) := by
  have hs : j / 5 < 26 := by omega
  have h := allBlk_spec (qeSlAll (j / 5) hs) (j % 5) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 5 (j / 5)) (j % 5) = j := Nat.div_add_mod j 5
  rw [e, Nat.blt_eq.mpr hj] at h
  change qeOK j = true at h
  unfold qeOK at h
  exact p_eq (pqE hj) ((bAnd_iff _ _).1 h).2

theorem wFacts : qProdK 1 = W ∧ pc W (SuzInvT1.F 0) = WT := by
  have h := kW
  unfold wOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (qProdK 1) W) (Nat.beq (pc W (SuzInvT1.F 0)) WT)).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem pW : P w0Tab W := by
  have e2 : qProds[1]! = qProd 1 := by
    unfold qProds
    rw [getElem!_pos _ 1 (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
  have hw : P (qProd 1) (qProdK 1) := pqProd 1
  rw [← wFacts.1]
  unfold w0Tab
  rw [e2]
  exact hw

theorem pWT : P w0tTab WT := by
  have hw : P (CFSG.Monster.B.Co2.Native.compA 1782 w0Tab tTab) (pc W (SuzInvT1.F 0)) :=
    p_comp pW pt1
  rw [← wFacts.2]
  unfold w0tTab
  exact hw

theorem commTest_eq {x q : Array Nat} {X Q : Nat} (hx : P x X) (hq : P q Q) :
    commTest x q = Nat.beq (pc (pc X Q) W) (pc W (pc X Q)) := by
  have hy := p_comp hx hq
  rw [← eqA_P (p_comp hy pW) (p_comp pW hy)]
  unfold commTest CFSG.Monster.B.Co2.Native.eqA
  refine allLt_congr' fun y hy' => ?_
  rw [CFSG.Monster.B.Co2.compA_get hy', CFSG.Monster.B.Co2.compA_get (lt_of_P pW hy'),
    CFSG.Monster.B.Co2.compA_get hy', CFSG.Monster.B.Co2.compA_get hy']

theorem sqTest_eq {x q s : Array Nat} {X Q S : Nat} (hx : P x X) (hq : P q Q) (hs : P s S) :
    sqTest x q s = Nat.beq (pc (pc X Q) (pc X Q)) S := by
  have hy := p_comp hx hq
  rw [← eqA_P (p_comp hy hy) hs]
  unfold sqTest CFSG.Monster.B.Co2.Native.eqA
  refine allLt_congr' fun y hy' => ?_
  have hY : ∀ z < 1782, (CFSG.Monster.B.Co2.Native.compA 1782 x q)[z]! = x[q[z]!]! :=
    fun z hz => CFSG.Monster.B.Co2.compA_get hz
  rw [CFSG.Monster.B.Co2.compA_get hy', hY _ (lt_of_P hy hy'), hY _ hy']

theorem invTest_eq {x q : Array Nat} {X Q : Nat} (hx : P x X) (hq : P q Q) :
    invTest x q = Nat.beq (pc (pc X Q) (pc X Q)) Id := by
  have hy := p_comp hx hq
  rw [← eqA_P (p_comp hy hy) pidn_P]
  unfold invTest CFSG.Monster.B.Co2.Native.eqA
  refine allLt_congr' fun y hy' => ?_
  have hY : ∀ z < 1782, (CFSG.Monster.B.Co2.Native.compA 1782 x q)[z]! = x[q[z]!]! :=
    fun z hz => CFSG.Monster.B.Co2.compA_get hz
  rw [CFSG.Monster.B.Co2.compA_get hy', hY _ (lt_of_P hy hy'), hY _ hy',
    CFSG.Monster.B.Co2.idA_get hy']

theorem kind_of_ok {x : Array Nat} {X j e : Nat} (hx : P x X) (hj : j < 128)
    (h : kindOK X j e = true) : kind x j = Nat.land e 3 := by
  have hq := pQE hj
  unfold kindOK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  unfold kind
  by_cases hc : Nat.shiftRight e 2 = 0
  · rw [hc] at h
    change strictB (pc X (KernelLC.SuzB0QE j)) _ = true at h
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [commTest_eq hx hq, h1, sqTest_eq hx hq pW, sqTest_eq hx hq pWT, invTest_eq hx hq,
      Nat.eq_of_beq_eq_true h2]
    unfold kindRes
    cases Nat.beq (pc (pc X _) (pc X _)) W <;> cases Nat.beq (pc (pc X _) (pc X _)) WT <;>
      cases Nat.beq (pc (pc X _) (pc X _)) Id <;> rfl
  · rw [Bool.eq_false_iff.2 fun e' => hc (Nat.eq_of_beq_eq_true e')] at h
    change strictB (Nat.sub (Nat.shiftRight e 2) 1) _ = true at h
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    have hp := Nat.blt_eq.mp h1
    have hct : commTest x qElts[j]! = false := by
      refine Bool.eq_false_iff.2 fun hc' => ?_
      unfold commTest at hc'
      have := CFSG.Monster.B.Co2.allLt_spec hc' hp
      rw [get_P pW hp, get_P hq hp] at this
      rw [get_P hq (pgl pW.2 hp), get_P hx (pgl hq.2 hp)] at this
      rw [get_P hx (pgl hq.2 (pgl pW.2 hp)), get_P pW (pgl hx.2 (pgl hq.2 hp)), beqN] at this
      rw [this] at h4
      exact absurd h4 (by decide)
    rw [hct, Nat.eq_of_beq_eq_true h3]
    rfl

theorem kind_eq {q j : Nat} (hq : q < 76) (hj : j < 128) :
    kind (liftTab (ipos q)) j = Nat.land (kE q j) 3 := by
  have hj8 : j / 8 < 16 := by omega
  have hs : 16 * q + j / 8 < 1216 := by omega
  have h := kindSlAll (16 * q + j / 8) hs
  unfold kindSl at h
  have e1 : Nat.shiftRight (16 * q + j / 8) 4 = q := by
    change (16 * q + j / 8) >>> 4 = q
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (16 * q + j / 8) 15 = j / 8 := by
    change (16 * q + j / 8) &&& (2 ^ 4 - 1) = j / 8
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [CFSG.KS.Raw.Orb.strictB_eq, e1, CFSG.KS.Raw.Orb.strictB_eq, e2] at h
  have h' := allBlk_spec h (j % 8) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (Nat.mul 8 (j / 8)) (j % 8) = j := Nat.div_add_mod j 8
  rw [e3] at h'
  exact kind_of_ok (pL hq) hj h'

theorem countBelow_congr {m : Nat} {f g : Nat → Bool} (h : ∀ j < m, f j = g j) :
    countBelow m f = countBelow m g := by
  unfold countBelow
  rw [List.filter_congr fun j hj => h j (List.mem_range.1 hj)]

theorem conjTest_eq {R G S : Nat} (hG : cn7 G = true) (hS : cn7 S = true) :
    conjTest (unpack 64 7 R) (unpack 64 7 G) (unpack 64 7 S) = conjTK R G S := by
  unfold conjTest conjTK
  refine allLt_allN fun y hy => ?_
  rw [CFSG.KC.HeFixK.unpack_getElem! hy, CFSG.KC.HeFixK.unpack_getElem! hy,
    CFSG.KC.HeFixK.unpack_getElem! (CFSG.KC.HeFixK.pg_lt_of_canonK hG hy),
    CFSG.KC.HeFixK.unpack_getElem! (CFSG.KC.HeFixK.pg_lt_of_canonK hS hy), beqN]

theorem lB_eq : lBTab = unpack 64 7 LB ∧ cn7 LB = true := SuzAB.word_P lBWord

theorem conjOK_eq {q : Nat} (hq : q < 76) : conjOK (ipos q) = !(cw q == 0) := by
  have hi := (word_facts hq).1
  have key : ∀ c < 25920, conjTest matEnum.tabs[ipos q]! matEnum.tabs[c]! lBTab =
      conjTK (SuzFbE.T (ipos q)) (SuzFbE.T c) LB := by
    intro c hc
    rw [tab_get hi, tab_get hc, lB_eq.1]
    exact conjTest_eq (canT hc) lB_eq.2
  unfold conjOK anyBelow
  by_cases h0 : cw q = 0
  · have h := conjNegAll q hq
    unfold conjNeg at h
    rw [h0, Nat.beq_refl] at h
    have h' : allN 25920 (fun c => Bool.not (conjTK (SuzFbE.T (ipos q)) (SuzFbE.T c) LB)) =
      true := h
    rw [h0]
    refine List.any_eq_false.2 fun c hc => ?_
    have hc' := List.mem_range.1 hc
    rw [key c hc']
    have := allN_spec h' c hc'
    simpa using this
  · have h := allN_spec kConjPos q hq
    unfold conjPos at h
    rw [CFSG.KS.Raw.Orb.strictB_eq, Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
    change bAnd(Nat.blt (Nat.sub (cw q) 1) 25920,
      conjTK (SuzFbE.T (ipos q)) (SuzFbE.T (Nat.sub (cw q) 1)) LB) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have hc := Nat.blt_eq.mp h1
    have hne : (cw q == 0) = false := by simpa using h0
    rw [hne]
    refine List.any_eq_true.2 ⟨Nat.sub (cw q) 1, List.mem_range.2 hc, ?_⟩
    rw [key _ hc]
    exact h2

theorem countW_eq : countW = 480 := by
  unfold countW
  rw [invPos_eq, IL_eq, List.map_map]
  have e : ∀ q ∈ List.range 76, ((fun i => let x := liftTab i;
      countBelow 128 fun j => kind x j == 1) ∘ ipos) q =
      countBelow 128 fun j => Nat.land (kE q j) 3 == 1 := by
    intro q hq
    exact countBelow_congr fun j hj => by rw [kind_eq (List.mem_range.1 hq) hj]
  rw [List.map_congr_left e]
  exact beq_iff_eq.1 kCountW

theorem countZ_eq : countZ = 1200 := by
  unfold countZ
  rw [invPos_eq, IL_eq, List.map_map]
  have e : ∀ q ∈ List.range 76, ((fun i => if conjOK i then (let x := liftTab i;
      countBelow 128 fun j => kind x j == 2) else 0) ∘ ipos) q =
      if (!(cw q == 0)) = true then countBelow 128 (fun j => Nat.land (kE q j) 3 == 2)
      else 0 := by
    intro q hq
    have hq' := List.mem_range.1 hq
    rw [Function.comp_apply, conjOK_eq hq', countBelow_congr fun j hj => by rw [kind_eq hq' hj]]
  rw [List.map_congr_left e]
  exact beq_iff_eq.1 kCountZ

theorem words_ok : invPos.all (fun i => matWord (enumWord i) == matEnum.tabs[i]! &&
    (enumWord i).all fun k => decide (k < 10)) = true := by
  rw [invPos_eq, IL_eq, List.all_eq_true]
  intro i hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hi
  have hq' := List.mem_range.1 hq
  obtain ⟨h1, h2, h3⟩ := word_facts hq'
  obtain ⟨hm, hc⟩ := matWord_eq h3
  rw [enumWord_eq hq', hm, tab_get h1, beq_unpack hc (canT h1), h2, Nat.beq_refl,
    Bool.true_and, List.all_eq_true]
  exact fun k hk => decide_eq_true (h3 k hk)

theorem fibreCheck_true : fibreCheck = true := by
  unfold fibreCheck
  rw [words_ok, countW_eq, countZ_eq]
  rfl

end CertificateChecks.KernelSpor.SuzFb

end
