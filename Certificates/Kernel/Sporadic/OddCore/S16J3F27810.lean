module

public import Certificates.Kernel.Sporadic.OddCore.S16J3R27810
public import Certificates.Kernel.Sporadic.OddCore.S16J3Sift27810
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5F
public import Certificates.Kernel.Sporadic.OddCore.J3PGGlue
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.Certificates.Kernel.Spor.JoinSound
public import CFSG.Certificates.Kernel.Spor.MulHInvSound
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.RuInvHash

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PkPow
open CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Co2.Native
open CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.EvenSporadicStandard.Fin76b.Beta
open CertificateChecks.KernelSpor.F27811

local notation "⟪" x "⟫" => tabT (unpack 6156 13 x)

#kc_forall_chunks s16j3qA (fun i => s16j3q i = true) 32 CertificateChecks.KernelSpor.S16J3.s16j3q 1

theorem hn : szOK 6156 13 = true := OddCore.J3W.cn.1

theorem hidc : cK idK = true := OddCore.J3W.cn.2.2.2.2

theorem hid : idT 6156 = ⟪idK⟫ := OddCore.J3W.idT_eq

theorem s16j3hsF_eq (cnt : Nat) (T HS HSI : Nat → Nat) :
    hsortPtKF 6156 13 (mask 13) cnt T HS HSI = hsortPtK 6156 13 (mask 13) cnt T HS HSI :=
  funext (hsortPtKF_eq 6156 13 cnt T HS HSI)

theorem rH : slK S16J3R.cnt (hsortPtK 6156 13 (mask 13) S16J3R.cnt S16J3R.T S16J3R.HS S16J3R.HSI)
    0 S16J3R.cnt = true := by
  rw [← s16j3hsF_eq]
  exact rHF

theorem vH : slK S16J3V.cnt (hsortPtK 6156 13 (mask 13) S16J3V.cnt S16J3V.T S16J3V.HS S16J3V.HSI)
    0 S16J3V.cnt = true := by
  rw [← s16j3hsF_eq]
  exact vHF

theorem wH : slK S16J3W.cnt (hsortPtK 6156 13 (mask 13) S16J3W.cnt S16J3W.T S16J3W.HS S16J3W.HSI)
    0 S16J3W.cnt = true := by
  rw [← s16j3hsF_eq]
  exact wHF

theorem cH : slK S16J3C.cnt (hsortPtK 6156 13 (mask 13) S16J3C.cnt S16J3C.T S16J3C.HS S16J3C.HSI)
    0 S16J3C.cnt = true := by
  rw [← s16j3hsF_eq]
  exact cHF

theorem tabC {k : Nat} (hk : k < 31) : j3CentTbl k = ⟪J3CentP k⟫ := by
  rw [← OddCore.j3CentTbl_eq hk, tabT_natArr]

theorem tsTb {k : Nat} (hk : k < 13) : j3Tb k = ⟪S k⟫ := by
  have h : natArr (j3Tb k) = unpack 6156 13 (TS16J3P k) := by
    have h := CFSG.KS.Join.hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 13)
      TS16J3T.all ts16_join (by norm_num) k hk
    rw [← TS16J3T.eq] at h
    exact h
  rw [← tabT_natArr (j3Tb k), h]
  rfl

theorem not_of_bIf {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem allRec_iff {cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool} :
    (hRec 6156 13 cnt T PL).1.all p = true ↔ ∀ i < cnt, p ⟪T i⟫ = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have := h i (by simpa [hRec] using hi)
    simpa [hRec] using this
  · intro h i hi
    have hi' : i < cnt := by simpa [hRec] using hi
    simpa [hRec] using h i hi'

theorem tabsL {k : Nat} {GI : Nat → Nat} (L : List Nat) (hk : L.length = k)
    (he : ∀ j < k, GI j = L.getD j 0) (hc : ∀ j < k, cK (GI j) = true) :
    TabsOK 6156 13 k GI (L.map fun x => ⟪x⟫).toArray := by
  refine ⟨by simp [hk], fun j hj => ⟨?_, hc j hj⟩⟩
  have hj' : j < L.length := by omega
  rw [he j hj, getElem!_pos _ j (by simpa using hj'), List.getD_eq_getElem _ _ hj']
  simp

theorem rec_eq {k cnt : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat} {gs : List Table}
    (hG : ∀ j < k, G j = idK) (hg : TabsOK 6156 13 k GI gs.toArray)
    (hh : penumHdK idK cnt 40 T PL = true)
    (hE : penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hH : slK cnt (hsortPtK 6156 13 (mask 13) cnt T HS HSI) 0 cnt = true) :
    mulClosureH 6156 gs.toArray 40 = hRec 6156 13 cnt T PL :=
  (mulH_sound hn hG hg hh
    (fun i hi => penumSl_spec (i := i) hE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
    (fun i hi => slK_spec hH i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)).1

theorem canon_of {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hE : penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    ∀ i < cnt, cK (T i) = true := fun i hi =>
  penumPt_canon (penumSl_spec (i := i) hE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)

theorem enum_of {k cnt m : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    {gs : List Table} (hG : ∀ j < k, G j = idK) (hg : TabsOK 6156 13 k GI gs.toArray)
    (hgj : ∀ j < k, iK (GI j) (GJ j) = true ∧ cK (GJ j) = true)
    (hh : penumHdK idK cnt 40 T PL = true)
    (hE : penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hH : slK cnt (hsortPtK 6156 13 (mask 13) cnt T HS HSI) 0 cnt = true)
    (hCl : slK (Nat.mul cnt (k + k))
      (findPtK cnt T (prodQK 6156 13 (mask 13) (k + k) T (bothK k GI GJ)) CL) 0
      (Nat.mul cnt (k + k)) = true)
    (hm : cnt = m) : enumOK 6156 40 m gs = true :=
  enumOK_of hn hG hg hgj hh
    (fun i hi => penumSl_spec (i := i) hE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
    (fun i hi => slK_spec hH i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
    (fun c hc => slK_spec hCl c (Nat.zero_le _) (by rw [Nat.zero_add]; exact hc) hc) hm

theorem mem_at {k cnt i y : Nat} {G GI T PL POS SRT SRI P : Nat → Nat}
    (hE : penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (h : J2Cn.atK cnt T P i y = true) : memT 6156 (hRec 6156 13 cnt T PL).1 ⟪y⟫ = true := by
  unfold J2Cn.atK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hq := Nat.le_of_ble_eq_true h1
  rw [← Nat.eq_of_beq_eq_true h2]
  exact memT_of hq (tblEq_self (canon_of hE _ hq))

theorem gen1 {k : Nat} {G GI GJ f : Nat → Nat}
    (h : allN k (fun j => bAnd(Nat.beq (GI j) (f j), bAnd(Nat.beq (G j) idK,
      bAnd(cK (GI j), bAnd(cK (GJ j), iK (GI j) (GJ j)))))) = true) {j : Nat} (hj : j < k) :
    GI j = f j ∧ G j = idK ∧ cK (GI j) = true ∧ cK (GJ j) = true ∧ iK (GI j) (GJ j) = true := by
  have := allN_spec h j hj
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2⟩

theorem gen2 {k : Nat} {G GI GJ : Nat → Nat}
    (h : allN k (fun j => bAnd(Nat.beq (G j) idK,
      bAnd(cK (GI j), bAnd(cK (GJ j), iK (GI j) (GJ j))))) = true) {j : Nat} (hj : j < k) :
    G j = idK ∧ cK (GI j) = true ∧ cK (GJ j) = true ∧ iK (GI j) (GJ j) = true := by
  have := allN_spec h j hj
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, this.2⟩

theorem conj_eq {a b c d : Nat} (ha : cK a = true) (hb : cK b = true) (hc : cK c = true)
    (hd : cK d = true) (h : Nat.beq (pc (pc a b) c) d = true) :
    tblEq 6156 (compT 6156 (compT 6156 ⟪a⟫ ⟪b⟫) ⟪c⟫) ⟪d⟫ = true := by
  rw [compT_unpack ha hb, compT_unpack (canonK_pcomp ha hb) hc,
    tblEq_unpack (canonK_pcomp (canonK_pcomp ha hb) hc) hd]
  exact h

theorem comm_of {a b : Nat} (ha : cK a = true) (hb : cK b = true) (h : commK a b = true) :
    commTT 6156 ⟪a⟫ ⟪b⟫ = true := by
  rw [commTT_unpack ha hb]
  exact h

theorem sift_of {wd : List Int} {a : Nat} (ha : cK a = true) (h : j3W wd a = true) :
    j3Sift ⟪a⟫ = true := by
  unfold j3Sift
  rw [natArr_tabT ha]
  exact CertificateChecks.KernelSporSch.J3KT.sift_of h

theorem invo_of {a : Nat} (ha : cK a = true) (h : Nat.beq (pc a a) idK = true) :
    invoOK 6156 ⟪a⟫ = true := by
  rw [invoOK_eq' (by norm_num), compT_unpack ha ha, hid, tblEq_unpack (canonK_pcomp ha ha) hidc]
  exact h

theorem invOK_of {a ai : Nat} (ha : cK a = true) (hai : cK ai = true) (h : iK a ai = true) :
    invOK 6156 ⟪a⟫ (invT 6156 ⟪a⟫) = true := by
  rw [invT_unpack (by norm_num) h]
  exact invOK_unpack ha hai h

theorem ne_of {a d : Nat} (ha : cK a = true) (hd : cK d = true)
    (h : bIf(Nat.beq a d, false, true) = true) : (!tblEq 6156 ⟪a⟫ ⟪d⟫) = true := by
  rw [tblEq_unpack ha hd, not_of_bIf h]
  rfl

theorem all4 {p : Table → Bool} {a b c d : Table} (ha : p a = true) (hb : p b = true)
    (hc : p c = true) (hd : p d = true) : [a, b, c, d].all p = true := by
  simp [ha, hb, hc, hd]

theorem quadIn_eq {Y : Nat} (ct : cK tK = true) (cx : cK xK = true) (hY : cK Y = true) :
    quadIn 6156 ⟪tK⟫ ⟪xK⟫ ⟪Y⟫ = quadK Y := by
  unfold quadIn quadK
  rw [hid, tblEq_unpack hY hidc, tblEq_unpack hY ct, tblEq_unpack hY cx, compT_unpack ct cx,
    tblEq_unpack hY (canonK_pcomp ct cx)]
  rfl

theorem cs_eq : cTbls 6156 (j3Tb 0) [j3Tb 7, j3Tb 8, j3Tb 9, j3Tb 10] [true, false, false, true] =
    [compT 6156 (j3Tb 7) (j3Tb 0), j3Tb 8, j3Tb 9, compT 6156 (j3Tb 10) (j3Tb 0)] := by
  simp [cTbls]


theorem j3 : j3S16OK = true := by
  have hb := k_base
  simp only [bAnd_iff] at hb
  obtain ⟨cu, ct, cb, cv, cx, c7, c10, cuI, ctI, cbI, cmi, iu, it, ib, iv, i7, i10, ixx, bR, bV0,
    bV1, bV, bW0, bW1, bW2, bW, bC0, bC1, bC2, bC3, bC, nR, nV, nW, nC, hR, hV, hW, hC⟩ := hb
  have hs := k_sifts
  simp only [bAnd_iff] at hs
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hs
  have hf := k_facts
  simp only [bAnd_iff] at hf
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24⟩ := hf
  have hro := k_rout
  simp only [bAnd_iff] at hro
  obtain ⟨cr, irr, -⟩ := hro
  have cmi0 : cK (S16J3MI 0) = true := allN_spec cmi 0 (by norm_num)
  have cmi1 : cK (S16J3MI 1) = true := allN_spec cmi 1 (by norm_num)
  have cmi2 : cK (S16J3MI 2) = true := allN_spec cmi 2 (by norm_num)
  have rt : ∀ j < 4, S16J3R.GI j = [S 3, S 4, S 5, S 6].getD j 0 := fun j hj => by
    rw [(gen1 bR hj).1]
    interval_cases j <;> rfl
  have rS : ∀ j < 4, cK (S (Nat.add 3 j)) = true ∧ iK (S (Nat.add 3 j)) (S16J3RI j) = true :=
    fun j hj => by
      obtain ⟨e, -, c, -, i⟩ := gen1 bR hj
      rw [e] at c i
      exact ⟨c, i⟩
  have cC : ∀ j < 4, cK (S16J3C.GI j) = true := fun j hj => (gen2 bC hj).2.1
  have e1 : S16J3C.GI 1 = S 8 := Nat.eq_of_beq_eq_true bC1
  have e2 : S16J3C.GI 2 = S 9 := Nat.eq_of_beq_eq_true bC2
  have e0 : S16J3C.GI 0 = pc (S 7) rK := Nat.eq_of_beq_eq_true bC0
  have e3 : S16J3C.GI 3 = pc (S 10) rK := Nat.eq_of_beq_eq_true bC3
  have c8 : cK (S 8) = true := by rw [← e1]; exact cC 1 (by norm_num)
  have c9 : cK (S 9) = true := by rw [← e2]; exact cC 2 (by norm_num)
  have i8 : iK (S 8) (S16J3CI 1) = true := by
    rw [← e1]
    exact (gen2 bC (j := 1) (by norm_num)).2.2.2
  have i9 : iK (S 9) (S16J3CI 2) = true := by
    rw [← e2]
    exact (gen2 bC (j := 2) (by norm_num)).2.2.2
  have ct_eq : ∀ j < 4, S16J3C.GI j = [pc (S 7) rK, S 8, S 9, pc (S 10) rK].getD j 0 :=
    fun j hj => by
      interval_cases j
      · exact e0
      · exact e1
      · exact e2
      · exact e3
  have tR : TabsOK 6156 13 4 S16J3R.GI [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].toArray :=
    tabsL [S 3, S 4, S 5, S 6] rfl rt fun j hj => (gen1 bR hj).2.2.1
  have tV : TabsOK 6156 13 2 S16J3V.GI
      [⟪pcomp 6156 13 (mask 13) vK vK⟫, ⟪pcomp 6156 13 (mask 13) vK xK⟫].toArray :=
    tabsL [pc vK vK, pc vK xK] rfl (fun j hj => by
      interval_cases j
      · exact Nat.eq_of_beq_eq_true bV0
      · exact Nat.eq_of_beq_eq_true bV1) fun j hj => (gen2 bV hj).2.1
  have tW : TabsOK 6156 13 3 S16J3W.GI [⟪vK⟫, ⟪xK⟫, ⟪rK⟫].toArray :=
    tabsL [vK, xK, rK] rfl (fun j hj => by
      interval_cases j
      · exact Nat.eq_of_beq_eq_true bW0
      · exact Nat.eq_of_beq_eq_true bW1
      · exact Nat.eq_of_beq_eq_true bW2) fun j hj => (gen2 bW hj).2.1
  have tC : TabsOK 6156 13 4 S16J3C.GI
      [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
        ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫].toArray :=
    tabsL [pc (S 7) rK, S 8, S 9, pc (S 10) rK] rfl ct_eq cC
  have eR := rec_eq (fun j hj => (gen1 bR hj).2.1) tR hR rE rH
  have eC := rec_eq (fun j hj => (gen2 bC hj).1) tC hC cE cH
  have cRT := canon_of rE
  have cCT := canon_of cE
  have pvv := (gen2 bV (j := 0) (by norm_num))
  have pvx := (gen2 bV (j := 1) (by norm_num))
  rw [Nat.eq_of_beq_eq_true bV0] at pvv
  rw [Nat.eq_of_beq_eq_true bV1] at pvx
  have cvv : cK (pc vK vK) = true := canonK_pcomp cv cv
  have cvx : cK (pc vK xK) = true := canonK_pcomp cv cx
  have c7r : cK (pc (S 7) rK) = true := canonK_pcomp c7 cr
  have c10r : cK (pc (S 10) rK) = true := canonK_pcomp c10 cr
  have hnC : S16J3C.cnt = 32 := Nat.eq_of_beq_eq_true nC
  have hu : j3CentTbl 0 = ⟪uK⟫ := tabC (by norm_num)
  have ht : j3CentTbl 9 = ⟪tK⟫ := tabC (by norm_num)
  have hbt : j3BetaTbl 7 = ⟪bK⟫ := J3BetaA5.beta_tab (by norm_num)
  have hT : ∀ k < 13, j3Tb k = ⟪S k⟫ := fun k hk => tsTb hk
  have h0 : j3Tb 0 = ⟪rK⟫ := hT 0 (by norm_num)
  have h1 : j3Tb 1 = ⟪vK⟫ := hT 1 (by norm_num)
  have h2 : j3Tb 2 = ⟪xK⟫ := hT 2 (by norm_num)
  unfold j3S16OK s16Check
  rw [cs_eq, hu, ht, hbt, h0, h1, h2, hT 3 (by norm_num), hT 4 (by norm_num),
    hT 5 (by norm_num), hT 6 (by norm_num), hT 7 (by norm_num), hT 8 (by norm_num),
    hT 9 (by norm_num), hT 10 (by norm_num),
    compT_unpack c7 cr, compT_unpack c10 cr, compT_unpack cr cu, compT_unpack cv cv,
    compT_unpack cv cx]
  have g1 : permOK 6156 ⟪uK⟫ = true := permOK_unpack cu iu
  have g2 : permOK 6156 ⟪tK⟫ = true := permOK_unpack ct it
  have g3 : permOK 6156 ⟪bK⟫ = true := permOK_unpack cb ib
  have g4 : permOK 6156 ⟪rK⟫ = true := permOK_unpack cr irr
  have g5 : permOK 6156 ⟪vK⟫ = true := permOK_unpack cv iv
  have g6 : permOK 6156 ⟪xK⟫ = true := permOK_unpack cx ixx
  have g7 : [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].all (permOK 6156) = true :=
    all4 (permOK_unpack (rS 0 (by norm_num)).1 (rS 0 (by norm_num)).2)
      (permOK_unpack (rS 1 (by norm_num)).1 (rS 1 (by norm_num)).2)
      (permOK_unpack (rS 2 (by norm_num)).1 (rS 2 (by norm_num)).2)
      (permOK_unpack (rS 3 (by norm_num)).1 (rS 3 (by norm_num)).2)
  have g8 : [⟪S 7⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫].all (permOK 6156) = true :=
    all4 (permOK_unpack c7 i7) (permOK_unpack c8 i8) (permOK_unpack c9 i9) (permOK_unpack c10 i10)
  have g9 : j3Sift ⟪tK⟫ = true := sift_of ct s1
  have g10 : j3Sift ⟪bK⟫ = true := sift_of cb s2
  have g11 : j3Sift ⟪vK⟫ = true := sift_of cv s3
  have g12 : j3Sift ⟪xK⟫ = true := sift_of cx s4
  have g13 : [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].all j3Sift = true :=
    all4 (sift_of (rS 0 (by norm_num)).1 (allN_spec s5 0 (by norm_num)))
      (sift_of (rS 1 (by norm_num)).1 (allN_spec s5 1 (by norm_num)))
      (sift_of (rS 2 (by norm_num)).1 (allN_spec s5 2 (by norm_num)))
      (sift_of (rS 3 (by norm_num)).1 (allN_spec s5 3 (by norm_num)))
  have g14 : [⟪S 7⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫].all j3Sift = true :=
    all4 (sift_of c7 (allN_spec s5 4 (by norm_num))) (sift_of c8 (allN_spec s5 5 (by norm_num)))
      (sift_of c9 (allN_spec s5 6 (by norm_num))) (sift_of c10 (allN_spec s5 7 (by norm_num)))
  have g15 : j3Sift ⟪pcomp 6156 13 (mask 13) rK uK⟫ = true := sift_of (canonK_pcomp cr cu) s6
  have g16 : (!j3Sift ⟪rK⟫) = true := by
    rw [sift_r]
    rfl
  have g17 : invoOK 6156 ⟪rK⟫ = true := invo_of cr f0
  have g18 : tblEq 6156 (compT 6156 (compT 6156 ⟪rK⟫ ⟪tK⟫) ⟪rK⟫) ⟪tK⟫ = true :=
    conj_eq cr ct cr ct f1
  have g19 : invOK 6156 ⟪bK⟫ (invT 6156 ⟪bK⟫) = true := invOK_of cb cbI ib
  have g20 : tblEq 6156 (compT 6156 (compT 6156 ⟪rK⟫ ⟪bK⟫) ⟪rK⟫) (invT 6156 ⟪bK⟫) = true := by
    rw [invT_unpack (by norm_num) ib]
    exact conj_eq cr cb cr cbI f2
  have g21 : commTT 6156 ⟪vK⟫ ⟪tK⟫ = true := comm_of cv ct f3
  have g22 : commTT 6156 ⟪xK⟫ ⟪tK⟫ = true := comm_of cx ct f4
  have pw := powT_unpack (OddCore.J3W.pows vK) hid hidc cv
  have pwc := pows_canon (OddCore.J3W.pows vK) hidc cv
  have g23 : tblEq 6156 (powT 6156 4 ⟪vK⟫) ⟪tK⟫ = true := by
    rw [pw 4, tblEq_unpack (pwc 4) ct]
    exact f5
  have g24 : tblEq 6156 (powT 6156 8 ⟪vK⟫) (idT 6156) = true := by
    rw [pw 8, hid, tblEq_unpack (pwc 8) hidc]
    exact f6
  have g25 : invoOK 6156 ⟪xK⟫ = true := invo_of cx f7
  have g26 : (!tblEq 6156 ⟪xK⟫ (idT 6156)) = true := by
    rw [hid]
    exact ne_of cx hidc f8
  have g27 : (!tblEq 6156 ⟪xK⟫ ⟪tK⟫) = true := ne_of cx ct f9
  have g28 : invOK 6156 ⟪vK⟫ (invT 6156 ⟪vK⟫) = true := invOK_of cv cmi0 iv
  have g29 : tblEq 6156 (compT 6156 (compT 6156 ⟪xK⟫ ⟪vK⟫) ⟪xK⟫) (invT 6156 ⟪vK⟫) = true := by
    rw [invT_unpack (by norm_num) iv]
    exact conj_eq cx cv cx cmi0 f10
  have g30 : tblEq 6156 (compT 6156 (compT 6156 ⟪rK⟫ ⟪vK⟫) ⟪rK⟫) (compT 6156 ⟪vK⟫ ⟪tK⟫) =
      true := by
    rw [compT_unpack cv ct]
    exact conj_eq cr cv cr (canonK_pcomp cv ct) f11
  have g31 : tblEq 6156 (compT 6156 (compT 6156 ⟪rK⟫ ⟪xK⟫) ⟪rK⟫) (compT 6156 ⟪xK⟫ ⟪tK⟫) =
      true := by
    rw [compT_unpack cx ct]
    exact conj_eq cr cx cr (canonK_pcomp cx ct) f12
  have g32 : tblEq 6156 (compT 6156 (compT 6156 ⟪vK⟫ ⟪bK⟫) (invT 6156 ⟪vK⟫))
      (invT 6156 ⟪bK⟫) = true := by
    rw [invT_unpack (by norm_num) iv, invT_unpack (by norm_num) ib]
    exact conj_eq cv cb cmi0 cbI f13
  have g33 : tblEq 6156 (compT 6156 (compT 6156 ⟪xK⟫ ⟪bK⟫) ⟪xK⟫) (invT 6156 ⟪bK⟫) = true := by
    rw [invT_unpack (by norm_num) ib]
    exact conj_eq cx cb cx cbI f14
  have sq : ∀ j < 4, tblEq 6156 (compT 6156 ⟪S (Nat.add 3 j)⟫ ⟪S (Nat.add 3 j)⟫) ⟪tK⟫ = true :=
    fun j hj => by
      have c := (rS j hj).1
      rw [compT_unpack c c, tblEq_unpack (canonK_pcomp c c) ct]
      exact allN_spec f15 j hj
  have g34 : [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].all (fun z => tblEq 6156 (compT 6156 z z) ⟪tK⟫) =
      true :=
    all4 (sq 0 (by norm_num)) (sq 1 (by norm_num)) (sq 2 (by norm_num)) (sq 3 (by norm_num))
  have gjR : ∀ j < 4, iK (S16J3R.GI j) (S16J3RI j) = true ∧ cK (S16J3RI j) = true :=
    fun j hj => ⟨(gen1 bR hj).2.2.2.2, (gen1 bR hj).2.2.2.1⟩
  have g35 : enumOK 6156 40 32 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫] = true :=
    enum_of (fun j hj => (gen1 bR hj).2.1) tR gjR hR rE rH rCl (Nat.eq_of_beq_eq_true nR)
  have g36 : (centCount 6156 40 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫] [⟪rK⟫] == 8) = true := by
    rw [centCount_eq (hi := 1) hn (fun j hj => (gen1 bR hj).2.1) tR hR
      (fun i hi => penumSl_spec (i := i) rE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
      (fun i hi => slK_spec rH i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
      (by rw [Nat.eq_of_beq_eq_true nR]; norm_num)
      (q := fun i => commK (S16J3R.T i) rK) (fun i hi => by
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [commTT_unpack (cRT i hi) cr]
        rfl), Nat.eq_of_beq_eq_true f16]
    rfl
  have g37 : permOK 6156 ⟪pcomp 6156 13 (mask 13) vK vK⟫ = true := permOK_unpack cvv pvv.2.2.2
  have g38 : permOK 6156 ⟪pcomp 6156 13 (mask 13) vK xK⟫ = true := permOK_unpack cvx pvx.2.2.2
  have g39 : enumOK 6156 40 8 [⟪pcomp 6156 13 (mask 13) vK vK⟫,
      ⟪pcomp 6156 13 (mask 13) vK xK⟫] = true :=
    enum_of (fun j hj => (gen2 bV hj).1) tV
      (fun j hj => ⟨(gen2 bV hj).2.2.2, (gen2 bV hj).2.2.1⟩) hV vE vH vCl
      (Nat.eq_of_beq_eq_true nV)
  have g40 : memT 6156 (mulClosureH 6156 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].toArray 40).1
      ⟪pcomp 6156 13 (mask 13) vK vK⟫ = true := by
    rw [eR]
    exact mem_at rE f17
  have g41 : memT 6156 (mulClosureH 6156 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].toArray 40).1
      ⟪pcomp 6156 13 (mask 13) vK xK⟫ = true := by
    rw [eR]
    exact mem_at rE f18
  have g42 : commTT 6156 ⟪pcomp 6156 13 (mask 13) vK vK⟫ ⟪rK⟫ = true := comm_of cvv cr f19
  have g43 : commTT 6156 ⟪pcomp 6156 13 (mask 13) vK xK⟫ ⟪rK⟫ = true := comm_of cvx cr f20
  have g44 : enumOK 6156 40 32 [⟪vK⟫, ⟪xK⟫, ⟪rK⟫] = true :=
    enum_of (fun j hj => (gen2 bW hj).1) tW
      (fun j hj => ⟨(gen2 bW hj).2.2.2, (gen2 bW hj).2.2.1⟩) hW wE wH wCl
      (Nat.eq_of_beq_eq_true nW)
  have g45 : [⟪S 7⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫].all (fun e => commTT 6156 e ⟪tK⟫) = true :=
    all4 (comm_of c7 ct (allN_spec f21 0 (by norm_num)))
      (comm_of c8 ct (allN_spec f21 1 (by norm_num)))
      (comm_of c9 ct (allN_spec f21 2 (by norm_num)))
      (comm_of c10 ct (allN_spec f21 3 (by norm_num)))
  have pC : ∀ j < 4, permOK 6156 ⟪S16J3C.GI j⟫ = true := fun j hj =>
    permOK_unpack (cC j hj) (gen2 bC hj).2.2.2
  have kC : ∀ j < 4, commTT 6156 ⟪S16J3C.GI j⟫ ⟪xK⟫ = true := fun j hj =>
    comm_of (cC j hj) cx (allN_spec f22 j hj)
  have g46 : [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
      ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫].all (permOK 6156) = true := by
    have a0 := pC 0 (by norm_num)
    have a1 := pC 1 (by norm_num)
    have a2 := pC 2 (by norm_num)
    have a3 := pC 3 (by norm_num)
    rw [e0] at a0
    rw [e1] at a1
    rw [e2] at a2
    rw [e3] at a3
    exact all4 a0 a1 a2 a3
  have g47 : enumOK 6156 40 32 [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
      ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫] = true :=
    enum_of (fun j hj => (gen2 bC hj).1) tC
      (fun j hj => ⟨(gen2 bC hj).2.2.2, (gen2 bC hj).2.2.1⟩) hC cE cH cCl hnC
  have g48 : [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
      ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫].all (fun c => commTT 6156 c ⟪xK⟫) = true := by
    have a0 := kC 0 (by norm_num)
    have a1 := kC 1 (by norm_num)
    have a2 := kC 2 (by norm_num)
    have a3 := kC 3 (by norm_num)
    rw [e0] at a0
    rw [e1] at a1
    rw [e2] at a2
    rw [e3] at a3
    exact all4 a0 a1 a2 a3
  have g49 : memT 6156 (mulClosureH 6156 [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
      ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫].toArray 40).1 ⟪tK⟫ = true := by
    rw [eC]
    exact mem_at cE f23
  have g50 : memT 6156 (mulClosureH 6156 [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
      ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫].toArray 40).1 ⟪xK⟫ = true := by
    rw [eC]
    exact mem_at cE f24
  have g51 : quadCheck 6156 40 [⟪pcomp 6156 13 (mask 13) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫,
      ⟪pcomp 6156 13 (mask 13) (S 10) rK⟫] ⟪tK⟫ ⟪xK⟫ = true := by
    unfold quadCheck
    rw [eC, allRec_iff]
    intro i hi
    beta_reduce
    have ci := cCT i hi
    have hq := s16j3qA i (by rw [hnC] at hi; exact hi)
    unfold s16j3q at hq
    simp only [bAnd_iff] at hq
    obtain ⟨cai, iai, qi, hall⟩ := hq
    rw [invT_unpack (by norm_num) iai, compT_unpack ci ci, quadIn_eq ct cx (canonK_pcomp ci ci)]
    simp only [Bool.and_eq_true]
    refine ⟨⟨invOK_unpack ci cai iai, qi⟩, ?_⟩
    rw [allRec_iff]
    intro j hj
    beta_reduce
    have cj := cCT j hj
    have hq' := s16j3qA j (by rw [hnC] at hj; exact hj)
    unfold s16j3q at hq'
    simp only [bAnd_iff] at hq'
    obtain ⟨caj, iaj, -, -⟩ := hq'
    rw [compT_unpack ci cj, invT_unpack (by norm_num) iaj, compT_unpack cai caj,
      compT_unpack (canonK_pcomp ci cj) (canonK_pcomp cai caj),
      quadIn_eq ct cx (canonK_pcomp (canonK_pcomp ci cj) (canonK_pcomp cai caj))]
    exact allN_spec hall j (by rw [← hnC]; exact hj)
  simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38,
    g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, Bool.and_self]

end CertificateChecks.KernelSpor.S16J3

end
