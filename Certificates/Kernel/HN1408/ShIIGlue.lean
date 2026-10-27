module

public import Certificates.Kernel.HN1408.ShIIChk3
public import Certificates.Kernel.HN1408.ShIIChk5
public import Certificates.Kernel.HN1408.CayleyCodes
public import Certificates.Kernel.HN1408.TableIGlue
public import Certificates.Kernel.HN1408.TmuGlue
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KC.Blk
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem shRec_of {m cnt : Nat} {ws : List (List Nat)} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (hd : cyHd ws m capS G GI GJ T PL cnt = true)
    (hr : cyRec ws.length G GI GJ T PL POS SRT SRI HS HSI CL cnt = true) :
    enumW capS m ws = true ∧ subgroupList capS ws = (hRec 1408 11 cnt T PL).1 ∧
      (∀ i < cnt, Cn (T i)) ∧ (∀ j < ws.length, GI j = WK (ws.getD j [])) ∧ cnt = m := by
  unfold cyHd at hd
  obtain ⟨hd1, hd2⟩ := cyBA hd
  obtain ⟨hd3, hd4⟩ := cyBA hd2
  have hm : cnt = m := Nat.eq_of_beq_eq_true hd3
  have hg : ∀ j < ws.length, GI j = WK (ws.getD j []) ∧ G j = idK ∧
      canonK 1408 11 (mask 11) (1408 * 11) (GJ j) = true ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j) = true := by
    intro j hj
    obtain ⟨a, h8⟩ := cyBA (allN_spec hd1 j hj)
    obtain ⟨b, h9⟩ := cyBA h8
    obtain ⟨c, d⟩ := cyBA h9
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c, d⟩
  unfold cyRec at hr
  obtain ⟨hp, hr2⟩ := cyBA hr
  obtain ⟨hs, hcl⟩ := cyBA hr2
  have hp' : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI ws.length cnt T PL POS SRT
      SRI i = true := fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi
  obtain ⟨eW, eS⟩ := enumW_of hl (fun j hj => (hg j hj).2.1) (fun j hj => (hg j hj).1)
    (fun j hj => ⟨(hg j hj).2.2.2, (hg j hj).2.2.1⟩) hd4 hp'
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi)
    (fun c hc' => slK_spec hcl c (Nat.zero_le _)
      (by change c < 0 + cnt * (ws.length + ws.length); omega)
      (by change c < cnt * (ws.length + ws.length); omega)) hm
  exact ⟨eW, eS, fun i hi => penumPt_canon (hp' i hi), fun j hj => (hg j hj).1, hm⟩

theorem shOrd_spec {p x : Nat} (hx : Cn x) (h : shOrd p x = true) :
    primeOrderOK p (tabT (unpack 1408 11 x)) = true := by
  unfold shOrd at h
  obtain ⟨h1, h2⟩ := cyBA h
  rw [primeOrderOK_eq hx, h1, tmNot h2]
  rfl

theorem shComm {ws : List (List Nat)} {k : Nat} {GI : Nat → Nat} {X : Nat} (hk : ws.length = k)
    (hg : ∀ j < k, GI j = WK (ws.getD j [])) (hl : ∀ w ∈ ws, lettersOK w = true) (hX : Cn X)
    (h : allN k (fun j => commP (GI j) X) = true) :
    commWordsOK ws (tabT (unpack 1408 11 X)) = true := by
  unfold commWordsOK
  refine allW (f := fun t => commTT 1408 t (tabT (unpack 1408 11 X))) hk hg hl fun j hj => ?_
  rw [commTT_eq (cnW hg hl hk j hj) hX]
  exact allN_spec h j hj

theorem shCommPairs {us vs : List (List Nat)} {ku kv : Nat} {UG VG : Nat → Nat} (hku : us.length = ku)
    (hgu : ∀ j < ku, UG j = WK (us.getD j [])) (hlu : ∀ w ∈ us, lettersOK w = true)
    (hkv : vs.length = kv) (hgv : ∀ j < kv, VG j = WK (vs.getD j []))
    (hlv : ∀ w ∈ vs, lettersOK w = true)
    (h : allN ku (fun i => allN kv fun j => commP (UG i) (VG j)) = true) :
    commPairsOK us vs = true := by
  unfold commPairsOK
  refine allW (f := fun t => vs.all fun v => commTT 1408 t (tabW v)) hku hgu hlu fun i hi => ?_
  refine allW (f := fun t => commTT 1408 (tabT (unpack 1408 11 (UG i))) t) hkv hgv hlv
    fun j hj => ?_
  rw [commTT_eq (cnW hgu hlu hku i hi) (cnW hgv hlv hkv j hj)]
  exact allN_spec (allN_spec h i hi) j hj

theorem shWordsIn {ws : List (List Nat)} {k cnt o : Nat} {GI T PL P : Nat → Nat} (hk : ws.length = k)
    (hg : ∀ j < k, GI j = WK (ws.getD j [])) (hl : ∀ w ∈ ws, lettersOK w = true)
    (hT : ∀ i < cnt, Cn (T i)) (h : shGensIn k GI T cnt P o = true) :
    wordsInOK (hRec 1408 11 cnt T PL).1 ws = true := by
  unfold wordsInOK
  refine allW (f := memT 1408 (hRec 1408 11 cnt T PL).1) hk hg hl fun j hj => ?_
  obtain ⟨a, b⟩ := cyBA (allN_spec h j hj)
  exact tmMem hT (cnW hg hl hk j hj) a b

theorem shTrivInter {vc ac : Nat} {VT VPL AT APL : Nat → Nat} (hV : ∀ i < vc, Cn (VT i))
    (hA : ∀ i < ac, Cn (AT i))
    (h : allN vc (fun i => bIf(Nat.beq (VT i) idK, true, shNotIn (VT i) AT ac)) = true) :
    trivInterOK (idT 1408) (hRec 1408 11 vc VT VPL).1 (hRec 1408 11 ac AT APL).1 = true := by
  unfold trivInterOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < vc := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi', idT_eq, tblEq_eq (hV i hi') cId]
  have h1 := allN_spec h i hi'
  cases e : Nat.beq (VT i) idK
  · rw [e] at h1
    have h2 : shNotIn (VT i) AT ac = true := h1
    rw [tmNotMem hA (hV i hi') h2]
    rfl
  · rfl

theorem shSqOne {vc : Nat} {VT VPL : Nat → Nat} (hV : ∀ i < vc, Cn (VT i))
    (h : allN vc (fun i => Nat.beq (pc (VT i) (VT i)) idK) = true) :
    sqOneOK (idT 1408) (hRec 1408 11 vc VT VPL).1 = true := by
  unfold sqOneOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < vc := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi', compT_unpack (hV i hi') (hV i hi'), idT_eq,
    tblEq_eq (canonK_pcomp (hV i hi') (hV i hi')) cId]
  exact allN_spec h i hi'

theorem shPowOne {nc e : Nat} {NT NPL : Nat → Nat} (hN : ∀ i < nc, Cn (NT i))
    (h : allN nc (fun i => Nat.beq (ppK (NT i) e) idK) = true) :
    powOneOK e (idT 1408) (hRec 1408 11 nc NT NPL).1 = true := by
  unfold powOneOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < nc := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi', powT_eq (hN i hi'), idT_eq,
    tblEq_eq (cn_ppK (hN i hi') e) cId]
  exact allN_spec h i hi'

theorem shNormK_spec {C CI : Nat} {NG NT : Nat → Nat} {nc : Nat} {P : Nat → Nat} {o : Nat}
    (h : shNormK C CI NG NT nc P o = true) :
    Cn CI ∧ invEqK 1408 11 (mask 11) (1408 * 11) C CI = true ∧ ∀ n < 3,
      Nat.blt (r32 P (o + 2 * n)) nc = true ∧
      Nat.beq (NT (r32 P (o + 2 * n))) (pc (pc C (NG n)) CI) = true ∧
      Nat.blt (r32 P (o + 2 * n + 1)) nc = true ∧
      Nat.beq (NT (r32 P (o + 2 * n + 1))) (pc (pc CI (NG n)) C) = true := by
  unfold shNormK at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h3⟩ := cyBA h
  refine ⟨h1, h2, fun n hn => ?_⟩
  obtain ⟨a, h⟩ := cyBA (allN_spec h3 n hn)
  obtain ⟨b, h⟩ := cyBA h
  obtain ⟨c, d⟩ := cyBA h
  exact ⟨a, b, c, d⟩

theorem shNormGens {cs ns : List (List Nat)} {kc nc : Nat} {NG NT NPL CW CI P : Nat → Nat}
    (hkc : cs.length = kc) (hcw : ∀ j < kc, CW j = WK (cs.getD j []))
    (hlc : ∀ w ∈ cs, lettersOK w = true) (hkn : ns.length = 3)
    (hgn : ∀ j < 3, NG j = WK (ns.getD j [])) (hln : ∀ w ∈ ns, lettersOK w = true)
    (hT : ∀ i < nc, Cn (NT i))
    (h : allN kc (fun c => shNormK (CW c) (CI c) NG NT nc P (6 * c)) = true) :
    normGensOK (hRec 1408 11 nc NT NPL).1 cs ns = true := by
  unfold normGensOK
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hj' : j < kc := hkc ▸ hj
  obtain ⟨e, hC⟩ := tabW_eq (hlc _ hc)
  obtain ⟨hCI, hinv, hn3⟩ := shNormK_spec (allN_spec h j hj')
  rw [hcw j hj', List.getD_eq_getElem _ _ hj] at hinv hn3
  simp only []
  rw [e, invT_unpack (by norm_num) hinv, invOK_unpack hC hCI hinv, Bool.true_and]
  refine allW (f := fun t => memT 1408 (hRec 1408 11 nc NT NPL).1
      (conjT 1408 (tabT (unpack 1408 11 (WK cs[j]))) (tabT (unpack 1408 11 (CI j))) t) &&
    memT 1408 (hRec 1408 11 nc NT NPL).1
      (conjT 1408 (tabT (unpack 1408 11 (CI j))) (tabT (unpack 1408 11 (WK cs[j]))) t))
    hkn hgn hln fun n hn => ?_
  have hN := cnW hgn hln hkn n hn
  obtain ⟨a, b, c', d⟩ := hn3 n hn
  rw [conjT_unpack hC hCI hN, conjT_unpack hCI hC hN, Bool.and_eq_true]
  exact ⟨tmMem hT (canonK_pcomp (canonK_pcomp hC hN) hCI) a b,
    tmMem hT (canonK_pcomp (canonK_pcomp hCI hN) hC) c' d⟩

theorem shCommEq {U V A UI VI : Nat} (hU : Cn U) (hV : Cn V) (hA : Cn A) (hUI : Cn UI)
    (hiU : invEqK 1408 11 (mask 11) (1408 * 11) U UI = true) (hVI : Cn VI)
    (hiV : invEqK 1408 11 (mask 11) (1408 * 11) V VI = true)
    (h : Nat.beq (pc (pc (pc U V) UI) VI) A = true) :
    commutatorEqOK (tabT (unpack 1408 11 U)) (tabT (unpack 1408 11 V))
      (tabT (unpack 1408 11 A)) = true := by
  unfold commutatorEqOK
  rw [invT_unpack (by norm_num) hiU, invT_unpack (by norm_num) hiV, invOK_unpack hU hUI hiU,
    invOK_unpack hV hVI hiV, compT_unpack hU hV, compT_unpack (canonK_pcomp hU hV) hUI,
    compT_unpack (canonK_pcomp (canonK_pcomp hU hV) hUI) hVI,
    tblEq_eq (canonK_pcomp (canonK_pcomp (canonK_pcomp hU hV) hUI) hVI) hA]
  exact h

theorem sh3K_spec {r : Nat} {YG YT NG NT VG VT AG AT PY PN : Nat → Nat} {yc nc vc ac : Nat}
    (h : sh3K r YG YT yc NG NT nc VG VT vc AG AT ac PY PN = true) :
    shOrd 3 r = true ∧ allN 3 (fun j => commP (YG j) r) = true ∧ shNotIn r YT yc = true ∧
      shGensIn 3 NG YT yc PY 0 = true ∧ shGensIn 2 VG NT nc PN 0 = true ∧
      shGensIn 2 AG NT nc PN 2 = true ∧
      allN 2 (fun i => allN 3 fun j => commP (VG i) (NG j)) = true ∧
      allN vc (fun i => bIf(Nat.beq (VT i) idK, true, shNotIn (VT i) AT ac)) = true ∧
      allN vc (fun i => Nat.beq (pc (VT i) (VT i)) idK) = true := by
  unfold sh3K at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h⟩ := cyBA h
  obtain ⟨h3, h⟩ := cyBA h
  obtain ⟨h4, h⟩ := cyBA h
  obtain ⟨h5, h⟩ := cyBA h
  obtain ⟨h6, h⟩ := cyBA h
  obtain ⟨h7, h⟩ := cyBA h
  obtain ⟨h8, h9⟩ := cyBA h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem sh5AK_spec {r nc : Nat} {NG NT SG CW CI P : Nat → Nat}
    (h : sh5AK r NG NT nc SG CW CI P = true) :
    allN 3 (fun j => commP (NG j) r) = true ∧ allN 3 (fun j => commP (SG j) r) = true ∧
      allN nc (fun i => Nat.beq (ppK (NT i) 5) idK) = true ∧
      allN 4 (fun c => shNormK (CW c) (CI c) NG NT nc P (6 * c)) = true ∧
      commP (NG 0) (NG 2) = false := by
  unfold sh5AK at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h⟩ := cyBA h
  obtain ⟨h3, h⟩ := cyBA h
  obtain ⟨h4, h5⟩ := cyBA h
  exact ⟨h1, h2, h3, h4, tmNot h5⟩

theorem sh5CK_spec {r yc a u v UI VI B : Nat} {YG YT P : Nat → Nat}
    (h : sh5CK r YG YT yc P a u v UI VI B = true) :
    shOrd 5 r = true ∧ allN 2 (fun j => commP (YG j) r) = true ∧ shNotIn r YT yc = true ∧
      (Nat.blt (r32 P 0) yc = true ∧ Nat.beq (YT (r32 P 0)) a = true) ∧
      (Nat.blt (r32 P 1) yc = true ∧ Nat.beq (YT (r32 P 1)) u = true) ∧
      (Nat.blt (r32 P 2) yc = true ∧ Nat.beq (YT (r32 P 2)) v = true) ∧
      blkTrivK 1408 11 4 B a = true ∧ Cn UI ∧
      invEqK 1408 11 (mask 11) (1408 * 11) u UI = true ∧ Cn VI ∧
      invEqK 1408 11 (mask 11) (1408 * 11) v VI = true ∧
      Nat.beq (pc (pc (pc u v) UI) VI) a = true := by
  unfold sh5CK at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h⟩ := cyBA h
  obtain ⟨h3, h⟩ := cyBA h
  obtain ⟨h4, h⟩ := cyBA h
  obtain ⟨h5, h⟩ := cyBA h
  obtain ⟨h6, h⟩ := cyBA h
  obtain ⟨h7, h⟩ := cyBA h
  obtain ⟨h8, h⟩ := cyBA h
  obtain ⟨h9, h⟩ := cyBA h
  obtain ⟨h10, h⟩ := cyBA h
  obtain ⟨h11, h⟩ := cyBA h
  obtain ⟨h12, h⟩ := cyBA h
  obtain ⟨h13, h⟩ := cyBA h
  obtain ⟨h14, h15⟩ := cyBA h
  exact ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, h10, h11, h12, h13, h14, h15⟩

theorem sh7K_spec {r w a : Nat} {CG : Nat → Nat} (h : sh7K r w a CG = true) :
    shOrd 7 r = true ∧ shOrd 2 w = true ∧ commP w r = true ∧
      allN 2 (fun j => commP (CG j) w) = true ∧ Nat.beq w a = false := by
  unfold sh7K at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h⟩ := cyBA h
  obtain ⟨h3, h⟩ := cyBA h
  obtain ⟨h4, h5⟩ := cyBA h
  exact ⟨h1, h2, h3, h4, tmNot h5⟩

theorem shLab_of {k m cnt : Nat} {L : List Table} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (h : bAnd(headL k L m G GI GJ T PL cnt, shLRec k G GI GJ T PL POS SRT SRI HS HSI CL cnt) = true) :
    headL k L m G GI GJ T PL cnt = true ∧ enumOK k 100000 m L = true := by
  obtain ⟨hh, hr⟩ := cyBA h
  unfold shLRec at hr
  obtain ⟨hp, hr2⟩ := cyBA hr
  obtain ⟨hs, hc⟩ := cyBA hr2
  exact ⟨hh, img_of hh (fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi)
    (fun c hc' => slK_spec hc c (Nat.zero_le _) (by change c < 0 + cnt * 4; omega)
      (by change c < cnt * 4; omega))⟩

theorem shBlkData {d : BlkData} {B k m cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (hb : d.blk = unpack 1408 4 B) (hk : d.k = k) (hlen : d.gens.length = 2)
    (hw : ∀ w ∈ d.gens, lettersOK w = true) (h : headL k d.labs m G GI GJ T PL cnt = true)
    (hB : shBlkK B k d.gens GI = true) : blkDataOK d = true := by
  obtain ⟨hl, hg, -⟩ := headL_spec h
  unfold shBlkK at hB
  obtain ⟨h1, h2⟩ := cyBA hB
  obtain ⟨h3, h4⟩ := cyBA h2
  unfold blkDataOK
  rw [hb, hk, gensOK_true, blkLe_of h1, CFSG.KC.L34KSnd.size_unpack, blkSurjOK_of h3, hlen, hl]
  simp only [Bool.true_and, beq_self_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun w hw' => wordOK_of (hw w hw'), fun L hL => ?_⟩, fun q hq => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
    have hj' : j < 2 := by rw [hl] at hj; exact hj
    rw [← List.getD_eq_getElem _ #[] hj, (hg j hj').1]
    exact permOK_unpack (hg j hj').2.2.1 (hg j hj').2.2.2.2
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hj' : j < 2 := by simp [hl, hlen] at hj; omega
    rw [List.getElem_zip]
    have hw' : d.gens[j]'(by rw [hlen]; exact hj') ∈ d.gens := List.getElem_mem _
    obtain ⟨e, c⟩ := tabW_eq (hw _ hw')
    rw [e, ← List.getD_eq_getElem _ #[] (by rw [hl]; exact hj'), (hg j hj').1]
    have hm := allN_spec h4 j hj'
    rw [← List.getD_eq_getElem _ [] (by rw [hlen]; exact hj')] at c ⊢
    exact blkMapOK_of c (hg j hj').2.2.1 hm

theorem shBlkA : blkDataA3.blk = unpack 1408 4 (ShIIB 0) := blk_eq ShIIBA.eq shkBA
theorem shBlkY : blkDataY5.blk = unpack 1408 4 (ShIIB 1) := blk_eq ShIIBY.eq shkBY

theorem shlY3 : ∀ w ∈ y3Words, lettersOK w = true := by decide
theorem shlN3 : ∀ w ∈ n3Words, lettersOK w = true := by decide
theorem shlV3 : ∀ w ∈ v3Words, lettersOK w = true := by decide
theorem shlA3 : ∀ w ∈ a3Words, lettersOK w = true := by decide
theorem shlN5 : ∀ w ∈ n5Words, lettersOK w = true := by decide
theorem shlS5 : ∀ w ∈ s5Words, lettersOK w = true := by decide
theorem shlB5 : ∀ w ∈ b5Words, lettersOK w = true := by decide
theorem shlY5 : ∀ w ∈ y5Words, lettersOK w = true := by decide
theorem shlC5 : ∀ w ∈ fix5A.cent, lettersOK w = true := by decide
theorem shlC7 : ∀ w ∈ fix7.cent, lettersOK w = true := by decide

theorem shape3OK_true : shape3OK = true := by
  obtain ⟨eY, sY, cY, gY, -⟩ := shRec_of shlY3 shkHY3 shkRY3
  obtain ⟨eN, sN, cN, gN, -⟩ := shRec_of shlN3 shkHN3 shkRN3
  obtain ⟨eV, sV, cV, gV, -⟩ := shRec_of shlV3 shkHV3 shkRV3
  obtain ⟨eA, sA, cA, gA, -⟩ := shRec_of shlA3 shkHA3 shkRA3
  have r := tabW_eq (wd := fix3.rep) (by decide)
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := sh3K_spec shk3
  have c1 : primeOrderOK 3 (tabW fix3.rep) = true := by rw [r.1]; exact shOrd_spec r.2 o1
  have c2 : commWordsOK y3Words (tabW fix3.rep) = true := by
    rw [r.1]; exact shComm (k := 3) rfl gY shlY3 r.2 o2
  have c3 : memT 1408 (subgroupList capS y3Words) (tabW fix3.rep) = false := by
    rw [sY, r.1]; exact tmNotMem cY r.2 o3
  have c4 : wordsInOK (subgroupList capS y3Words) n3Words = true := by
    rw [sY]; exact shWordsIn (k := 3) rfl gN shlN3 cY o4
  have c5 : wordsInOK (subgroupList capS n3Words) v3Words = true := by
    rw [sN]; exact shWordsIn (k := 2) rfl gV shlV3 cN o5
  have c6 : wordsInOK (subgroupList capS n3Words) a3Words = true := by
    rw [sN]; exact shWordsIn (k := 2) rfl gA shlA3 cN o6
  have c7 : commPairsOK v3Words n3Words = true :=
    shCommPairs (ku := 2) (kv := 3) rfl gV shlV3 rfl gN shlN3 o7
  have c8 : trivInterOK (idT 1408) (subgroupList capS v3Words) (subgroupList capS a3Words) =
      true := by
    rw [sV, sA]; exact shTrivInter cV cA o8
  have c9 : sqOneOK (idT 1408) (subgroupList capS v3Words) = true := by
    rw [sV]; exact shSqOne cV o9
  have hLA := shLab_of shkLA
  have c10 : blkDataOK blkDataA3 = true := shBlkData shBlkA rfl rfl shlA3 hLA.1 shkDA
  have c11 : blkImageOK blkDataA3 60 = true := hLA.2
  unfold shape3OK
  simp only [wordOK_of (w := fix3.rep) (by decide), c1, eY, eN, eV, eA, c2, c3, c4, c5, c6, c7, c8,
    c9, c10, c11, Bool.not_false, Bool.and_self]

theorem shape5AOK_true : shape5AOK = true := by
  obtain ⟨eN, sN, cN, gN, -⟩ := shRec_of shlN5 shkHN5 shkRN5
  obtain ⟨-, -, -, gS, -⟩ := shRec_of shlS5 shkHS5 shkRS5
  have r := tabW_eq (wd := fix5A.rep) (by decide)
  obtain ⟨a1, a2, a3, a4, a5⟩ := sh5AK_spec shk5A
  have c1 : fix5A.cent.all wordOK = true := by decide
  have c2 : commWordsOK n5Words (tabW fix5A.rep) = true := by
    rw [r.1]; exact shComm (k := 3) rfl gN shlN5 r.2 a1
  have c3 : commWordsOK s5Words (tabW fix5A.rep) = true := by
    rw [r.1]; exact shComm (k := 3) rfl gS shlS5 r.2 a2
  have c4 : powOneOK 5 (idT 1408) (subgroupList capS n5Words) = true := by
    rw [sN]; exact shPowOne cN a3
  have c5 : normGensOK (subgroupList capS n5Words) fix5A.cent n5Words = true := by
    rw [sN]; exact shNormGens (kc := 4) rfl (fun _ _ => rfl) shlC5 rfl gN shlN5 cN a4
  have c6 : commTT 1408 (tabW (n5Words.getD 0 [])) (tabW (n5Words.getD 2 [])) = false := by
    have l0 := lettersOK_getD shlN5 0
    have l2 := lettersOK_getD shlN5 2
    rw [(tabW_eq l0).1, (tabW_eq l2).1, commTT_eq (cn_WK l0) (cn_WK l2), ← gN 0 (by decide),
      ← gN 2 (by decide)]
    exact a5
  have c7 : cayleyOK capS 16 s5Words imgS5 = true :=
    cayleyOK_of s5Code shlS5 shkHS5 shkRS5 rfl (by decide +kernel) (by decide +kernel) shkCS5
  unfold shape5AOK
  simp only [wordOK_of (w := fix5A.rep) (by decide), c1, eN, c2, c3, c4, c5, c6, c7,
    Bool.not_false, Bool.and_self]

theorem shape5BOK_true : shape5BOK = true := by
  obtain ⟨-, -, -, gB, -⟩ := shRec_of shlB5 shkHB5 shkRB5
  have r := tabW_eq (wd := fix5B.rep) (by decide)
  have c1 : commWordsOK b5Words (tabW fix5B.rep) = true := by
    rw [r.1]; exact shComm (k := 2) rfl gB shlB5 r.2 shk5B
  have c2 : cayleyOK capS 100 b5Words imgB5 = true :=
    cayleyOK_of b5Code shlB5 shkHB5 shkRB5 rfl (by decide +kernel) (by decide +kernel) shkCB5
  unfold shape5BOK
  simp only [wordOK_of (w := fix5B.rep) (by decide), c1, c2, Bool.and_self]

theorem shape5COK_true : shape5COK = true := by
  obtain ⟨eY, sY, cY, gY, -⟩ := shRec_of shlY5 shkHY5 shkRY5
  have r := tabW_eq (wd := fix5C.rep) (by decide)
  have a := tabW_eq (wd := wordA) (by decide)
  have u := tabW_eq (wd := u5Word) (by decide)
  have v := tabW_eq (wd := v5Word) (by decide)
  obtain ⟨o1, o2, o3, ⟨o4, o5⟩, ⟨o6, o7⟩, ⟨o8, o9⟩, o10, o11, o12, o13, o14, o15⟩ :=
    sh5CK_spec shk5C
  have c1 : primeOrderOK 5 (tabW fix5C.rep) = true := by rw [r.1]; exact shOrd_spec r.2 o1
  have c2 : commWordsOK y5Words (tabW fix5C.rep) = true := by
    rw [r.1]; exact shComm (k := 2) rfl gY shlY5 r.2 o2
  have c3 : memT 1408 (subgroupList capS y5Words) (tabW fix5C.rep) = false := by
    rw [sY, r.1]; exact tmNotMem cY r.2 o3
  have c4 : memT 1408 (subgroupList capS y5Words) (tabW wordA) = true := by
    rw [sY, a.1]; exact tmMem cY a.2 o4 o5
  have c5 : memT 1408 (subgroupList capS y5Words) (tabW u5Word) = true := by
    rw [sY, u.1]; exact tmMem cY u.2 o6 o7
  have c6 : memT 1408 (subgroupList capS y5Words) (tabW v5Word) = true := by
    rw [sY, v.1]; exact tmMem cY v.2 o8 o9
  have hLY := shLab_of shkLY
  have c7 : blkDataOK blkDataY5 = true := shBlkData shBlkY rfl rfl shlY5 hLY.1 shkDY
  have c8 : blkImageOK blkDataY5 120 = true := hLY.2
  have c9 : blkTrivOK blkDataY5.blk (tabW wordA) = true := by
    rw [shBlkY, a.1, blkTrivOK_eq a.2]; exact o10
  have c10 : commutatorEqOK (tabW u5Word) (tabW v5Word) (tabW wordA) = true := by
    rw [u.1, v.1, a.1]; exact shCommEq u.2 v.2 a.2 o11 o12 o13 o14 o15
  unfold shape5COK
  simp only [wordOK_of (w := fix5C.rep) (by decide), wordOK_of (w := u5Word) (by decide),
    wordOK_of (w := v5Word) (by decide), c1, eY, c2, c3, c4, c5, c6, c7, c8, c9, c10,
    Bool.not_false, Bool.and_self]

theorem shape7OK_true : shape7OK = true := by
  have r := tabW_eq (wd := fix7.rep) (by decide)
  have w := tabW_eq (wd := w7Word) (by decide)
  have a := tabW_eq (wd := wordA) (by decide)
  obtain ⟨q1, q2, q3, q4, q5⟩ := sh7K_spec shk7
  have c0 : fix7.cent.all wordOK = true := by decide
  have c1 : primeOrderOK 7 (tabW fix7.rep) = true := by rw [r.1]; exact shOrd_spec r.2 q1
  have c2 : primeOrderOK 2 (tabW w7Word) = true := by rw [w.1]; exact shOrd_spec w.2 q2
  have c3 : commWordsOK [w7Word] (tabW fix7.rep) = true := by
    simp only [commWordsOK, List.all_cons, List.all_nil, Bool.and_true]
    rw [w.1, r.1, commTT_eq w.2 r.2]
    exact q3
  have c4 : commWordsOK fix7.cent (tabW w7Word) = true := by
    rw [w.1]; exact shComm (k := 2) rfl (fun _ _ => rfl) shlC7 w.2 q4
  have c5 : tblEq 1408 (tabW w7Word) (tabW wordA) = false := by
    rw [w.1, a.1, tblEq_eq w.2 a.2]; exact q5
  unfold shape7OK
  simp only [gensOK_true, wordOK_of (w := fix7.rep) (by decide), wordOK_of (w := w7Word) (by decide),
    c0, c1, c2, c3, c4, c5, Bool.not_false, Bool.and_self]

theorem shapesIIOK_true : shapesIIOK = true := by
  unfold shapesIIOK
  simp only [shape3OK_true, shape5AOK_true, shape5BOK_true, shape5COK_true, shape7OK_true,
    Bool.and_self]

end CFSG.KD.HN1408

end
