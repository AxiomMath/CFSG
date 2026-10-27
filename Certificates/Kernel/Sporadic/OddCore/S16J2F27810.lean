module

public import Certificates.Kernel.Sporadic.OddCore.S16J2K27810
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S16J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PkPow
open CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Co2.Native
open CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.EvenSporadicStandard.Fin76b.Beta
open CertificateChecks.KernelSpor.J2Cn

local notation "⟪" x "⟫" => tabT (unpack 315 9 x)

theorem bTb : j2BetaTbl 7 = ⟪bK⟫ := by
  have h : natArr (j2BetaTbl 7) = unpack 315 9 (J2BetaT.F 7) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound J2BetaT.all (by norm_num) 7 (by norm_num)
    rw [← J2BetaT.eq] at h
    exact h
  rw [← tabT_natArr (j2BetaTbl 7), h]
  rfl

theorem tsTb {k : Nat} (hk : k < 14) : j2Tb k = ⟪S k⟫ := by
  have h : natArr (j2Tb k) = unpack 315 9 (TS16J2T.F k) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound TS16J2T.all (by norm_num) k hk
    rw [← TS16J2T.eq] at h
    exact h
  rw [← tabT_natArr (j2Tb k), h]
  rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem pows (P : Nat) : Pows 315 9 P (ppw 315 9 P) :=
  ⟨rfl, fun e => strictN_eq (ppw 315 9 P e) (fun q => pcomp 315 9 (mask 9) P q)⟩

theorem not_of_bIf {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem allRec_iff {cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool} :
    (hRec 315 9 cnt T PL).1.all p = true ↔ ∀ i < cnt, p ⟪T i⟫ = true := by
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
    TabsOK 315 9 k GI (L.map fun x => ⟪x⟫).toArray := by
  refine ⟨by simp [hk], fun j hj => ⟨?_, hc j hj⟩⟩
  have hj' : j < L.length := by omega
  rw [he j hj, getElem!_pos _ j (by simpa using hj'), List.getD_eq_getElem _ _ hj']
  simp

theorem rec_eq {k cnt : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat} {gs : List Table}
    (hG : ∀ j < k, G j = J2Cn.idK) (hg : TabsOK 315 9 k GI gs.toArray)
    (hh : penumHdK J2Cn.idK cnt 40 T PL = true)
    (hE : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hH : slK cnt (hsortPtK 315 9 (mask 9) cnt T HS HSI) 0 cnt = true) :
    mulClosureH 315 gs.toArray 40 = hRec 315 9 cnt T PL :=
  (mulH_sound hn hG hg hh
    (fun i hi => penumSl_spec (i := i) hE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
    (fun i hi => slK_spec hH i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)).1

theorem canon_of {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hE : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    ∀ i < cnt, cK (T i) = true := fun i hi =>
  penumPt_canon (penumSl_spec (i := i) hE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)

theorem enum_of {k cnt m : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    {gs : List Table} (hG : ∀ j < k, G j = J2Cn.idK) (hg : TabsOK 315 9 k GI gs.toArray)
    (hgj : ∀ j < k, iK (GI j) (GJ j) = true ∧ cK (GJ j) = true)
    (hh : penumHdK J2Cn.idK cnt 40 T PL = true)
    (hE : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hH : slK cnt (hsortPtK 315 9 (mask 9) cnt T HS HSI) 0 cnt = true)
    (hCl : slK (Nat.mul cnt (k + k))
      (findPtK cnt T (prodQK 315 9 (mask 9) (k + k) T (bothK k GI GJ)) CL) 0
      (Nat.mul cnt (k + k)) = true)
    (hm : cnt = m) : enumOK 315 40 m gs = true :=
  enumOK_of hn hG hg hgj hh
    (fun i hi => penumSl_spec (i := i) hE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
    (fun i hi => slK_spec hH i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
    (fun c hc => slK_spec hCl c (Nat.zero_le _) (by rw [Nat.zero_add]; exact hc) hc) hm

theorem mem_at {k cnt i y : Nat} {G GI T PL POS SRT SRI P : Nat → Nat}
    (hE : penumSlK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (h : atK cnt T P i y = true) : memT 315 (hRec 315 9 cnt T PL).1 ⟪y⟫ = true := by
  unfold atK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hq := Nat.le_of_ble_eq_true h1
  rw [← Nat.eq_of_beq_eq_true h2]
  exact memT_of hq (tblEq_self (canon_of hE _ hq))

theorem gen1 {k : Nat} {G GI GJ f : Nat → Nat}
    (h : allN k (fun j => bAnd(Nat.beq (GI j) (f j), bAnd(Nat.beq (G j) J2Cn.idK,
      bAnd(cK (GI j), bAnd(cK (GJ j), iK (GI j) (GJ j)))))) = true) {j : Nat} (hj : j < k) :
    GI j = f j ∧ G j = J2Cn.idK ∧ cK (GI j) = true ∧ cK (GJ j) = true ∧ iK (GI j) (GJ j) = true := by
  have := allN_spec h j hj
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2⟩

theorem gen2 {k : Nat} {G GI GJ : Nat → Nat}
    (h : allN k (fun j => bAnd(Nat.beq (G j) J2Cn.idK,
      bAnd(cK (GI j), bAnd(cK (GJ j), iK (GI j) (GJ j))))) = true) {j : Nat} (hj : j < k) :
    G j = J2Cn.idK ∧ cK (GI j) = true ∧ cK (GJ j) = true ∧ iK (GI j) (GJ j) = true := by
  have := allN_spec h j hj
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, this.2⟩

theorem conj_eq {a b c d : Nat} (ha : cK a = true) (hb : cK b = true) (hc : cK c = true)
    (hd : cK d = true) (h : Nat.beq (pc (pc a b) c) d = true) :
    tblEq 315 (compT 315 (compT 315 ⟪a⟫ ⟪b⟫) ⟪c⟫) ⟪d⟫ = true := by
  rw [compT_unpack ha hb, compT_unpack (canonK_pcomp ha hb) hc,
    tblEq_unpack (canonK_pcomp (canonK_pcomp ha hb) hc) hd]
  exact h

theorem comm_of {a b : Nat} (ha : cK a = true) (hb : cK b = true) (h : J2Cn.commK a b = true) :
    commTT 315 ⟪a⟫ ⟪b⟫ = true := by
  rw [commTT_unpack ha hb]
  exact h

theorem sift_of {a : Nat} (ha : cK a = true) (h : sK a = true) : j2Sift ⟪a⟫ = true := by
  rw [sift_eq ha]
  exact h

theorem invo_of {a : Nat} (ha : cK a = true) (h : Nat.beq (pc a a) J2Cn.idK = true) :
    invoOK 315 ⟪a⟫ = true := by
  rw [invoOK_eq' (by norm_num), compT_unpack ha ha, hid, tblEq_unpack (canonK_pcomp ha ha) hidc]
  exact h

theorem invOK_of {a ai : Nat} (ha : cK a = true) (hai : cK ai = true) (h : iK a ai = true) :
    invOK 315 ⟪a⟫ (invT 315 ⟪a⟫) = true := by
  rw [invT_unpack (by norm_num) h]
  exact invOK_unpack ha hai h

theorem ne_of {a d : Nat} (ha : cK a = true) (hd : cK d = true)
    (h : bIf(Nat.beq a d, false, true) = true) : (!tblEq 315 ⟪a⟫ ⟪d⟫) = true := by
  rw [tblEq_unpack ha hd, not_of_bIf h]
  rfl

theorem all4 {p : Table → Bool} {a b c d : Table} (ha : p a = true) (hb : p b = true)
    (hc : p c = true) (hd : p d = true) : [a, b, c, d].all p = true := by
  simp [ha, hb, hc, hd]

theorem all5 {p : Table → Bool} {a b c d e : Table} (ha : p a = true) (hb : p b = true)
    (hc : p c = true) (hd : p d = true) (he : p e = true) : [a, b, c, d, e].all p = true := by
  simp [ha, hb, hc, hd, he]

theorem quadIn_eq {Y : Nat} (ct : cK tK = true) (cx : cK xK = true) (hY : cK Y = true) :
    quadIn 315 ⟪tK⟫ ⟪xK⟫ ⟪Y⟫ = quadK Y := by
  unfold quadIn quadK
  rw [hid, tblEq_unpack hY hidc, tblEq_unpack hY ct, tblEq_unpack hY cx, compT_unpack ct cx,
    tblEq_unpack hY (canonK_pcomp ct cx)]
  rfl

theorem cs_eq : cTbls 315 (j2Tb 0) [j2Tb 7, j2Tb 8, j2Tb 9, j2Tb 10, j2Tb 11]
    [true, false, false, false, false] =
    [compT 315 (j2Tb 7) (j2Tb 0), j2Tb 8, j2Tb 9, j2Tb 10, j2Tb 11] := rfl

theorem j2 : j2S16OK = true := by
  have hb := k_base
  simp only [bAnd_iff] at hb
  obtain ⟨cb, c7, cr, cv, cx, cmi, ib, iv, i7, irr, ixx, bR, bV0, bV1, bV, bW0, bW1, bW2, bW,
    bC0, bCs, bC, nR, nV, nW, nC, hR, hV, hW, hC⟩ := hb
  have hf := k_facts
  simp only [bAnd_iff] at hf
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33⟩ := hf
  have ct : cK tK = true := Fc (by norm_num)
  have cu : cK (F 0) = true := Fc (by norm_num)
  have cmi0 : cK (S16J2MI 0) = true := allN_spec cmi 0 (by norm_num)
  have cmi1 : cK (S16J2MI 1) = true := allN_spec cmi 1 (by norm_num)
  have cmi2 : cK (S16J2MI 2) = true := allN_spec cmi 2 (by norm_num)
  have rt : ∀ j < 4, S16J2R.GI j = [S 3, S 4, S 5, S 6].getD j 0 := fun j hj => by
    rw [(gen1 bR hj).1]
    interval_cases j <;> rfl
  have rS : ∀ j < 4, cK (S (Nat.add 3 j)) = true ∧ iK (S (Nat.add 3 j)) (S16J2RI j) = true :=
    fun j hj => by
      obtain ⟨e, -, c, -, i⟩ := gen1 bR hj
      rw [e] at c i
      exact ⟨c, i⟩
  have cC : ∀ j < 5, cK (S16J2C.GI j) = true := fun j hj => (gen2 bC hj).2.1
  have cS : ∀ j < 4, S16J2C.GI (Nat.succ j) = S (Nat.add 8 j) := fun j hj =>
    Nat.eq_of_beq_eq_true (allN_spec bCs j hj)
  have eS : ∀ j < 4, cK (S (Nat.add 8 j)) = true ∧
      iK (S (Nat.add 8 j)) (S16J2CI (Nat.succ j)) = true := fun j hj => by
    have h := gen2 bC (j := Nat.succ j) (by omega)
    rw [cS j hj] at h
    exact ⟨h.2.1, h.2.2.2⟩
  have ct_eq : ∀ j < 5, S16J2C.GI j = [pc (S 7) rK, S 8, S 9, S 10, S 11].getD j 0 :=
    fun j hj => by
      interval_cases j
      · exact Nat.eq_of_beq_eq_true bC0
      · exact cS 0 (by norm_num)
      · exact cS 1 (by norm_num)
      · exact cS 2 (by norm_num)
      · exact cS 3 (by norm_num)
  have tR : TabsOK 315 9 4 S16J2R.GI [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].toArray :=
    tabsL [S 3, S 4, S 5, S 6] rfl rt fun j hj => (gen1 bR hj).2.2.1
  have tV : TabsOK 315 9 2 S16J2V.GI
      [⟪pcomp 315 9 (mask 9) vK vK⟫, ⟪pcomp 315 9 (mask 9) vK xK⟫].toArray :=
    tabsL [pc vK vK, pc vK xK] rfl (fun j hj => by
      interval_cases j
      · exact Nat.eq_of_beq_eq_true bV0
      · exact Nat.eq_of_beq_eq_true bV1) fun j hj => (gen2 bV hj).2.1
  have tW : TabsOK 315 9 3 S16J2W.GI [⟪vK⟫, ⟪xK⟫, ⟪rK⟫].toArray :=
    tabsL [vK, xK, rK] rfl (fun j hj => by
      interval_cases j
      · exact Nat.eq_of_beq_eq_true bW0
      · exact Nat.eq_of_beq_eq_true bW1
      · exact Nat.eq_of_beq_eq_true bW2) fun j hj => (gen2 bW hj).2.1
  have tC : TabsOK 315 9 5 S16J2C.GI
      [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫].toArray :=
    tabsL [pc (S 7) rK, S 8, S 9, S 10, S 11] rfl ct_eq cC
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
  have hnC : S16J2C.cnt = 32 := Nat.eq_of_beq_eq_true nC
  have hu : j2CentTbl 0 = ⟪F 0⟫ := tabF (by norm_num)
  have ht : j2CentTbl 31 = ⟪tK⟫ := tabF (by norm_num)
  have hT : ∀ k < 14, j2Tb k = ⟪S k⟫ := fun k hk => tsTb hk
  have h0 : j2Tb 0 = ⟪rK⟫ := hT 0 (by norm_num)
  have h1 : j2Tb 1 = ⟪vK⟫ := hT 1 (by norm_num)
  have h2 : j2Tb 2 = ⟪xK⟫ := hT 2 (by norm_num)
  unfold j2S16OK s16Check
  rw [cs_eq, hu, ht, bTb, h0, h1, h2, hT 3 (by norm_num), hT 4 (by norm_num),
    hT 5 (by norm_num), hT 6 (by norm_num), hT 7 (by norm_num), hT 8 (by norm_num),
    hT 9 (by norm_num), hT 10 (by norm_num), hT 11 (by norm_num),
    compT_unpack c7 cr, compT_unpack cr cu, compT_unpack cv cv, compT_unpack cv cx]
  have g1 : permOK 315 ⟪F 0⟫ = true := permOK_unpack cu (Finv (by norm_num))
  have g2 : permOK 315 ⟪tK⟫ = true := permOK_unpack ct (Finv (by norm_num))
  have g3 : permOK 315 ⟪bK⟫ = true := permOK_unpack cb ib
  have g4 : permOK 315 ⟪rK⟫ = true := permOK_unpack cr irr
  have g5 : permOK 315 ⟪vK⟫ = true := permOK_unpack cv iv
  have g6 : permOK 315 ⟪xK⟫ = true := permOK_unpack cx ixx
  have g7 : [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].all (permOK 315) = true :=
    all4 (permOK_unpack (rS 0 (by norm_num)).1 (rS 0 (by norm_num)).2)
      (permOK_unpack (rS 1 (by norm_num)).1 (rS 1 (by norm_num)).2)
      (permOK_unpack (rS 2 (by norm_num)).1 (rS 2 (by norm_num)).2)
      (permOK_unpack (rS 3 (by norm_num)).1 (rS 3 (by norm_num)).2)
  have g8 : [⟪S 7⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫].all (permOK 315) = true :=
    all5 (permOK_unpack c7 i7)
      (permOK_unpack (eS 0 (by norm_num)).1 (eS 0 (by norm_num)).2)
      (permOK_unpack (eS 1 (by norm_num)).1 (eS 1 (by norm_num)).2)
      (permOK_unpack (eS 2 (by norm_num)).1 (eS 2 (by norm_num)).2)
      (permOK_unpack (eS 3 (by norm_num)).1 (eS 3 (by norm_num)).2)
  have g9 : j2Sift ⟪tK⟫ = true := sift_of ct f1
  have g10 : j2Sift ⟪bK⟫ = true := sift_of cb f2
  have g11 : j2Sift ⟪vK⟫ = true := sift_of cv f3
  have g12 : j2Sift ⟪xK⟫ = true := sift_of cx f4
  have g13 : [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].all j2Sift = true :=
    all4 (sift_of (rS 0 (by norm_num)).1 (allN_spec f5 0 (by norm_num)))
      (sift_of (rS 1 (by norm_num)).1 (allN_spec f5 1 (by norm_num)))
      (sift_of (rS 2 (by norm_num)).1 (allN_spec f5 2 (by norm_num)))
      (sift_of (rS 3 (by norm_num)).1 (allN_spec f5 3 (by norm_num)))
  have g14 : [⟪S 7⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫].all j2Sift = true :=
    all5 (sift_of c7 (allN_spec f6 0 (by norm_num)))
      (sift_of (eS 0 (by norm_num)).1 (allN_spec f6 1 (by norm_num)))
      (sift_of (eS 1 (by norm_num)).1 (allN_spec f6 2 (by norm_num)))
      (sift_of (eS 2 (by norm_num)).1 (allN_spec f6 3 (by norm_num)))
      (sift_of (eS 3 (by norm_num)).1 (allN_spec f6 4 (by norm_num)))
  have g15 : j2Sift ⟪pcomp 315 9 (mask 9) rK (F 0)⟫ = true := sift_of (canonK_pcomp cr cu) f7
  have g16 : (!j2Sift ⟪rK⟫) = true := by
    rw [sift_eq cr]
    revert f8
    cases sK rK
    · intro _
      rfl
    · intro h
      exact absurd h Bool.false_ne_true
  have g17 : invoOK 315 ⟪rK⟫ = true := invo_of cr f9
  have g18 : tblEq 315 (compT 315 (compT 315 ⟪rK⟫ ⟪tK⟫) ⟪rK⟫) ⟪tK⟫ = true :=
    conj_eq cr ct cr ct f10
  have g19 : invOK 315 ⟪bK⟫ (invT 315 ⟪bK⟫) = true := invOK_of cb cmi0 ib
  have g20 : tblEq 315 (compT 315 (compT 315 ⟪rK⟫ ⟪bK⟫) ⟪rK⟫) (invT 315 ⟪bK⟫) = true := by
    rw [invT_unpack (by norm_num) ib]
    exact conj_eq cr cb cr cmi0 f11
  have g21 : commTT 315 ⟪vK⟫ ⟪tK⟫ = true := comm_of cv ct f12
  have g22 : commTT 315 ⟪xK⟫ ⟪tK⟫ = true := comm_of cx ct f13
  have pw := powT_unpack (pows vK) hid hidc cv
  have pwc := pows_canon (pows vK) hidc cv
  have g23 : tblEq 315 (powT 315 4 ⟪vK⟫) ⟪tK⟫ = true := by
    rw [pw 4, tblEq_unpack (pwc 4) ct]
    exact f14
  have g24 : tblEq 315 (powT 315 8 ⟪vK⟫) (idT 315) = true := by
    rw [pw 8, hid, tblEq_unpack (pwc 8) hidc]
    exact f15
  have g25 : invoOK 315 ⟪xK⟫ = true := invo_of cx f16
  have g26 : (!tblEq 315 ⟪xK⟫ (idT 315)) = true := by
    rw [hid]
    exact ne_of cx hidc f17
  have g27 : (!tblEq 315 ⟪xK⟫ ⟪tK⟫) = true := ne_of cx ct f18
  have g28 : invOK 315 ⟪vK⟫ (invT 315 ⟪vK⟫) = true := invOK_of cv cmi1 iv
  have g29 : tblEq 315 (compT 315 (compT 315 ⟪xK⟫ ⟪vK⟫) ⟪xK⟫) (invT 315 ⟪vK⟫) = true := by
    rw [invT_unpack (by norm_num) iv]
    exact conj_eq cx cv cx cmi1 f19
  have g30 : tblEq 315 (compT 315 (compT 315 ⟪rK⟫ ⟪vK⟫) ⟪rK⟫) (compT 315 ⟪vK⟫ ⟪tK⟫) = true := by
    rw [compT_unpack cv ct]
    exact conj_eq cr cv cr (canonK_pcomp cv ct) f20
  have g31 : tblEq 315 (compT 315 (compT 315 ⟪rK⟫ ⟪xK⟫) ⟪rK⟫) (compT 315 ⟪xK⟫ ⟪tK⟫) = true := by
    rw [compT_unpack cx ct]
    exact conj_eq cr cx cr (canonK_pcomp cx ct) f21
  have g32 : tblEq 315 (compT 315 (compT 315 ⟪vK⟫ ⟪bK⟫) (invT 315 ⟪vK⟫)) (invT 315 ⟪bK⟫) =
      true := by
    rw [invT_unpack (by norm_num) iv, invT_unpack (by norm_num) ib]
    exact conj_eq cv cb cmi1 cmi0 f22
  have g33 : tblEq 315 (compT 315 (compT 315 ⟪xK⟫ ⟪bK⟫) ⟪xK⟫) (invT 315 ⟪bK⟫) = true := by
    rw [invT_unpack (by norm_num) ib]
    exact conj_eq cx cb cx cmi0 f23
  have sq : ∀ j < 4, tblEq 315 (compT 315 ⟪S (Nat.add 3 j)⟫ ⟪S (Nat.add 3 j)⟫) ⟪tK⟫ = true :=
    fun j hj => by
      have c := (rS j hj).1
      rw [compT_unpack c c, tblEq_unpack (canonK_pcomp c c) ct]
      exact allN_spec f24 j hj
  have g34 : [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].all (fun z => tblEq 315 (compT 315 z z) ⟪tK⟫) = true :=
    all4 (sq 0 (by norm_num)) (sq 1 (by norm_num)) (sq 2 (by norm_num)) (sq 3 (by norm_num))
  have gjR : ∀ j < 4, iK (S16J2R.GI j) (S16J2RI j) = true ∧ cK (S16J2RI j) = true :=
    fun j hj => ⟨(gen1 bR hj).2.2.2.2, (gen1 bR hj).2.2.2.1⟩
  have g35 : enumOK 315 40 32 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫] = true :=
    enum_of (fun j hj => (gen1 bR hj).2.1) tR gjR hR rE rH rCl (Nat.eq_of_beq_eq_true nR)
  have g36 : (centCount 315 40 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫] [⟪rK⟫] == 8) = true := by
    rw [centCount_eq (hi := 1) hn (fun j hj => (gen1 bR hj).2.1) tR hR
      (fun i hi => penumSl_spec (i := i) rE (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
      (fun i hi => slK_spec rH i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi) hi)
      (by rw [Nat.eq_of_beq_eq_true nR]; norm_num)
      (q := fun i => J2Cn.commK (S16J2R.T i) rK) (fun i hi => by
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [commTT_unpack (cRT i hi) cr]
        rfl), Nat.eq_of_beq_eq_true f25]
    rfl
  have g37 : permOK 315 ⟪pcomp 315 9 (mask 9) vK vK⟫ = true := permOK_unpack cvv pvv.2.2.2
  have g38 : permOK 315 ⟪pcomp 315 9 (mask 9) vK xK⟫ = true := permOK_unpack cvx pvx.2.2.2
  have g39 : enumOK 315 40 8 [⟪pcomp 315 9 (mask 9) vK vK⟫, ⟪pcomp 315 9 (mask 9) vK xK⟫] =
      true :=
    enum_of (fun j hj => (gen2 bV hj).1) tV
      (fun j hj => ⟨(gen2 bV hj).2.2.2, (gen2 bV hj).2.2.1⟩) hV vE vH vCl
      (Nat.eq_of_beq_eq_true nV)
  have g40 : memT 315 (mulClosureH 315 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].toArray 40).1
      ⟪pcomp 315 9 (mask 9) vK vK⟫ = true := by
    rw [eR]
    exact mem_at rE f26
  have g41 : memT 315 (mulClosureH 315 [⟪S 3⟫, ⟪S 4⟫, ⟪S 5⟫, ⟪S 6⟫].toArray 40).1
      ⟪pcomp 315 9 (mask 9) vK xK⟫ = true := by
    rw [eR]
    exact mem_at rE f27
  have g42 : commTT 315 ⟪pcomp 315 9 (mask 9) vK vK⟫ ⟪rK⟫ = true := comm_of cvv cr f28
  have g43 : commTT 315 ⟪pcomp 315 9 (mask 9) vK xK⟫ ⟪rK⟫ = true := comm_of cvx cr f29
  have g44 : enumOK 315 40 32 [⟪vK⟫, ⟪xK⟫, ⟪rK⟫] = true :=
    enum_of (fun j hj => (gen2 bW hj).1) tW
      (fun j hj => ⟨(gen2 bW hj).2.2.2, (gen2 bW hj).2.2.1⟩) hW wE wH wCl
      (Nat.eq_of_beq_eq_true nW)
  have g45 : [⟪S 7⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫].all (fun e => commTT 315 e ⟪tK⟫) = true :=
    all5 (comm_of c7 ct (allN_spec f30 0 (by norm_num)))
      (comm_of (eS 0 (by norm_num)).1 ct (allN_spec f30 1 (by norm_num)))
      (comm_of (eS 1 (by norm_num)).1 ct (allN_spec f30 2 (by norm_num)))
      (comm_of (eS 2 (by norm_num)).1 ct (allN_spec f30 3 (by norm_num)))
      (comm_of (eS 3 (by norm_num)).1 ct (allN_spec f30 4 (by norm_num)))
  have pC : ∀ j < 5, permOK 315 ⟪S16J2C.GI j⟫ = true := fun j hj =>
    permOK_unpack (cC j hj) (gen2 bC hj).2.2.2
  have kC : ∀ j < 5, commTT 315 ⟪S16J2C.GI j⟫ ⟪xK⟫ = true := fun j hj =>
    comm_of (cC j hj) cx (allN_spec f31 j hj)
  have e0 : S16J2C.GI 0 = pcomp 315 9 (mask 9) (S 7) rK := Nat.eq_of_beq_eq_true bC0
  have g46 : [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫].all (permOK 315) =
      true := by
    have a0 := pC 0 (by norm_num)
    have a1 := pC 1 (by norm_num)
    have a2 := pC 2 (by norm_num)
    have a3 := pC 3 (by norm_num)
    have a4 := pC 4 (by norm_num)
    rw [e0] at a0
    rw [cS 0 (by norm_num)] at a1
    rw [cS 1 (by norm_num)] at a2
    rw [cS 2 (by norm_num)] at a3
    rw [cS 3 (by norm_num)] at a4
    exact all5 a0 a1 a2 a3 a4
  have g47 : enumOK 315 40 32 [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫,
      ⟪S 11⟫] = true :=
    enum_of (fun j hj => (gen2 bC hj).1) tC
      (fun j hj => ⟨(gen2 bC hj).2.2.2, (gen2 bC hj).2.2.1⟩) hC cE cH cCl hnC
  have g48 : [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫].all
      (fun c => commTT 315 c ⟪xK⟫) = true := by
    have a0 := kC 0 (by norm_num)
    have a1 := kC 1 (by norm_num)
    have a2 := kC 2 (by norm_num)
    have a3 := kC 3 (by norm_num)
    have a4 := kC 4 (by norm_num)
    rw [e0] at a0
    rw [cS 0 (by norm_num)] at a1
    rw [cS 1 (by norm_num)] at a2
    rw [cS 2 (by norm_num)] at a3
    rw [cS 3 (by norm_num)] at a4
    exact all5 a0 a1 a2 a3 a4
  have g49 : memT 315 (mulClosureH 315 [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫,
      ⟪S 11⟫].toArray 40).1 ⟪tK⟫ = true := by
    rw [eC]
    exact mem_at cE f32
  have g50 : memT 315 (mulClosureH 315 [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫,
      ⟪S 11⟫].toArray 40).1 ⟪xK⟫ = true := by
    rw [eC]
    exact mem_at cE f33
  have g51 : quadCheck 315 40 [⟪pcomp 315 9 (mask 9) (S 7) rK⟫, ⟪S 8⟫, ⟪S 9⟫, ⟪S 10⟫, ⟪S 11⟫]
      ⟪tK⟫ ⟪xK⟫ = true := by
    unfold quadCheck
    rw [eC, allRec_iff]
    intro i hi
    beta_reduce
    have ci := cCT i hi
    have hq := allN_spec k_quad i (by rw [← hnC]; exact hi)
    simp only [bAnd_iff] at hq
    obtain ⟨cai, iai, qi, hall⟩ := hq
    rw [invT_unpack (by norm_num) iai, compT_unpack ci ci, quadIn_eq ct cx (canonK_pcomp ci ci)]
    simp only [Bool.and_eq_true]
    refine ⟨⟨invOK_unpack ci cai iai, qi⟩, ?_⟩
    rw [allRec_iff]
    intro j hj
    beta_reduce
    have cj := cCT j hj
    have hq' := allN_spec k_quad j (by rw [← hnC]; exact hj)
    simp only [bAnd_iff] at hq'
    obtain ⟨caj, iaj, -, -⟩ := hq'
    rw [compT_unpack ci cj, invT_unpack (by norm_num) iaj, compT_unpack cai caj,
      compT_unpack (canonK_pcomp ci cj) (canonK_pcomp cai caj),
      quadIn_eq ct cx (canonK_pcomp (canonK_pcomp ci cj) (canonK_pcomp cai caj))]
    exact allN_spec hall j (by rw [← hnC]; exact hj)
  simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38,
    g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, Bool.and_self]

end CertificateChecks.KernelSpor.S16J2

end
