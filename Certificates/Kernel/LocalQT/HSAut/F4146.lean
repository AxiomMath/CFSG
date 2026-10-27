module

public import Certificates.Kernel.LocalQT.HSAut.R4146
public import Certificates.Kernel.LocalQT.HSAut.C4146E0
public import Certificates.Kernel.LocalQT.HSAut.C4146E1
public import Certificates.Kernel.LocalQT.HSAut.C4146E2
public import Certificates.Kernel.LocalQT.HSAut.C4146E3
public import Certificates.Kernel.LocalQT.HSAut.C4146E4
public import Certificates.Kernel.LocalQT.HSAut.C4146E5
public import Certificates.Kernel.LocalQT.HSAut.C4146E6
public import Certificates.Kernel.LocalQT.HSAut.C4146E7
public import Certificates.Kernel.LocalQT.HSAut.C4146E8
public import Certificates.Kernel.LocalQT.HSAut.C4146E9
public import Certificates.Kernel.LocalQT.HSAut.C4146E10
public import Certificates.Kernel.LocalQT.HSAut.C4146E11
public import Certificates.Kernel.SporSch.PairHS.Check2219
public import Certificates.Kernel.LocalQT.SV.C4126TB
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutNodesCheckInputs
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawSiftK
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.HN.A CFSG.KD.LQT.HN.ckA 960

namespace CFSG.KD.LQT.HN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KS.MulH
open CFSG.KD.LQT.C4126 CertificateChecks.KernelSporSch CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.QuasithinUnique.Id2519.UHS CFSG.PSL3Four.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.Sporadic.Th.Native (compT)

abbrev Cn (p : Nat) : Prop := canonK 3850 12 (mask 12) (3850 * 12) p = true

theorem hn : szOK 3850 12 = true := by decide

theorem cIdn : Cn idn := PHSCheck.idParts.1

theorem cPc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem comp_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 3850 (unpack 3850 12 p) (unpack 3850 12 q) = unpack 3850 12 (pc p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem beq_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 3850 12 p == unpack 3850 12 q) = Nat.beq p q :=
  beq_unpack hp hq

theorem idTab_eq : idTab 3850 = unpack 3850 12 idn := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Raw.Orb.szOK_facts hn
  apply Array.ext
  · simp [idTab, unpack]
  · intro i hi _
    have hi' : i < 3850 := by simpa [idTab] using hi
    rw [← getElem!_pos _ i hi,
      ← getElem!_pos (unpack 3850 12 idn) i (by simpa [unpack] using hi'),
      CFSG.KS.Raw.Orb.unpack_get hi', idn, CFSG.KS.PF.pg_pidn h1 h2 hi', getElem!_pos _ i hi]
    simp [idTab]

theorem wfoldR_nil (L : Nat → Nat) : wfoldR L [] = idn := rfl

theorem wfoldR_cons (L : Nat → Nat) (l : Nat) (ls : List Nat) :
    wfoldR L (l :: ls) = pc (L l) (wfoldR L ls) :=
  CFSG.KS.Raw.Orb.strictN_eq _ _

theorem foldr_unpack {L : Nat → Nat} {A : Nat → Array Nat} : ∀ (ls : List Nat),
    (∀ l ∈ ls, A l = unpack 3850 12 (L l) ∧ Cn (L l)) →
    (ls.map A).foldr (comp 3850) (idTab 3850) = unpack 3850 12 (wfoldR L ls) ∧ Cn (wfoldR L ls)
  | [], _ => ⟨idTab_eq, cIdn⟩
  | l :: ls, h => by
    obtain ⟨ih1, ih2⟩ := foldr_unpack ls fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    rw [List.map_cons, List.foldr_cons, ih1, h1, wfoldR_cons, comp_pc h2 ih2]
    exact ⟨rfl, cPc h2 ih2⟩

theorem cX {j : Nat} (hj : j < 5) : Cn (X j) := allN_spec canon_ok j hj

theorem canons : Cn (HC.F 0) ∧ Cn (HC.F 6) ∧ Cn (HC.F 7) ∧ Cn (HS.F 0) ∧ Cn (HS.F 1) ∧
    Cn (HSI 1) := by
  simpa only [bAnd_iff] using canon_ok'

theorem hsStrongArrs_size : hsStrongArrs.size = 8 := by simp [hsStrongArrs]

theorem rawInvs_get {j : Nat} (hj : j < 8) :
    (rawInvs 3850 hsStrongArrs)[j]! = invCand 3850 hsStrongArrs[j]! := by
  rw [rawInvs, getElem!_pos (hsStrongArrs.map (invCand 3850)) j (by simp [hsStrongArrs_size, hj]),
    getElem!_pos hsStrongArrs j (by rw [hsStrongArrs_size]; exact hj), Array.getElem_map]

theorem letter_arr {l : Nat} (hl : l < 3) : letterArr l = unpack 3850 12 (la l) ∧ Cn (la l) := by
  obtain ⟨-, -, -, h0, h1, hi⟩ := canons
  interval_cases l
  · refine ⟨?_, h0⟩
    have e : letterArr 0 = hsStrongArrs[0]! := by simp [letterArr, PairHS.gens]
    rw [e, hsStrong_get (by norm_num)]
    rfl
  · refine ⟨?_, h1⟩
    have e : letterArr 1 = hsStrongArrs[1]! := by simp [letterArr, PairHS.gens]
    rw [e, hsStrong_get (by norm_num)]
    rfl
  · refine ⟨?_, hi⟩
    have e : letterArr 2 = (rawInvs 3850 hsStrongArrs)[1]! := by
      simp [letterArr, PairHS.gensInv]
    rw [e, rawInvs_get (by norm_num), hsStrong_get (by norm_num),
      (invEqK_sound (allN_spec hs_perms 1 (by norm_num))).1]
    rfl

theorem wordTab_eq {ls : List Nat} (hls : ∀ l ∈ ls, l < 3) :
    wordTab ls = unpack 3850 12 (wfoldR la ls) ∧ Cn (wfoldR la ls) :=
  foldr_unpack ls fun l hl => letter_arr (hls l hl)

theorem g_eq : gTab = unpack 3850 12 (X 0) := by
  rw [Nat.eq_of_beq_eq_true x0_ok]
  exact (wordTab_eq (ls := gLetters) (by decide)).1

theorem y1_eq : y1Tab = unpack 3850 12 (X 2) := by
  rw [Nat.eq_of_beq_eq_true x2_ok]
  exact (wordTab_eq (ls := y1Letters) (by decide)).1

theorem y2_eq : y2Tab = unpack 3850 12 (X 3) := by
  rw [Nat.eq_of_beq_eq_true x3_ok]
  exact (wordTab_eq (ls := y2Letters) (by decide)).1

theorem c_eq : cTab = unpack 3850 12 (X 4) := by
  rw [Nat.eq_of_beq_eq_true x4_ok]
  exact (wordTab_eq (ls := cLetters) (by decide)).1

theorem gi_eq : giTab = unpack 3850 12 (X 1) := by
  have e : giTab = invCand 3850 gTab := rfl
  rw [e, g_eq]
  exact (invEqK_sound x1_ok).1

theorem e_eq : eTab = unpack 3850 12 (wfoldR ly eLetters) ∧ Cn (wfoldR ly eLetters) := by
  refine foldr_unpack (A := fun l => if l = 0 then y1Tab else y2Tab) eLetters fun l hl => ?_
  have hl' : l = 0 ∨ l = 1 := by simp [eLetters] at hl; omega
  rcases hl' with rfl | rfl
  · have e : ly 0 = X 2 := by unfold ly; rw [CFSG.KS.Raw.Orb.nIf_eq]; rfl
    rw [e]
    exact ⟨by simp [y1_eq], cX (by norm_num)⟩
  · have e : ly 1 = X 3 := by unfold ly; rw [CFSG.KS.Raw.Orb.nIf_eq]; rfl
    rw [e]
    exact ⟨by simp [y2_eq], cX (by norm_num)⟩

theorem comp_inv_id {t r : Array Nat} (h : isInvA 3850 t r = true) :
    comp 3850 r t = idTab 3850 := by
  apply Array.ext (by simp [comp, idTab])
  intro i h1 _
  have hi : i < 3850 := by simpa [comp] using h1
  simp only [comp, idTab, Array.getElem_ofFn]
  exact (CFSG.Monster.B.Co2.isInvA_spec h hi).2

theorem cent_size {k : Nat} (hk : k < 43) : (hsCentTbl k).size = 3850 := by
  have := congrArg Array.size (hsCentTbl_eq hk)
  simpa [natArr, unpack_size] using this

theorem cent_perm {k : Nat} (hk : k < 43) (hc : Cn (HC.F k)) :
    CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl k) = true := by
  rw [← tabT_natArr (hsCentTbl k), hsCentTbl_eq hk]
  exact permOK_unpack hc (allN_spec hc_perms k hk)

theorem r1_parts : Cn (R1.F 0) ∧ invEqK 3850 12 (mask 12) (3850 * 12) (R1.F 0) (R1.F 0) = true ∧
    Nat.beq (pc (R1.F 0) (X 2)) (pc (X 2) (R1.F 0)) = true ∧
    Nat.beq (pc (R1.F 0) (X 3)) (pc (X 3) (R1.F 0)) = true := by
  simpa only [bAnd_iff] using r1_ok

theorem r1_bind : natArr r1T = unpack 3850 12 (R1.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound R1.all (by norm_num) 0 (by norm_num)
  rw [← R1.eq, Nat.mul_zero] at h
  exact h

theorem r1_size : r1T.size = 3850 := by
  have := congrArg Array.size r1_bind
  simpa [natArr, unpack_size] using this

theorem r1_perm : CFSG.Sporadic.SmallOddCore.permOK 3850 r1T = true := by
  rw [← tabT_natArr r1T, r1_bind]
  exact permOK_unpack r1_parts.1 r1_parts.2.1

theorem u_bind : natArr hsOuterTbl = unpack 3850 12 (HC.F 0) := hsCentTbl_eq (by norm_num)

theorem ru_bind : natArr (compT 3850 r1T hsOuterTbl) = unpack 3850 12 (pc (R1.F 0) (HC.F 0)) := by
  rw [← tabT_natArr r1T, ← tabT_natArr hsOuterTbl, r1_bind, u_bind,
    compT_unpack r1_parts.1 canons.1]
  exact natArr_tabT (cPc r1_parts.1 canons.1)

theorem rep_pc {p q : Nat} {σ τ : Equiv.Perm (Fin 3850)}
    (hp : CFSG.Monster.B.Co2.Rep 3850 (unpack 3850 12 p) σ)
    (hq : CFSG.Monster.B.Co2.Rep 3850 (unpack 3850 12 q) τ) :
    CFSG.Monster.B.Co2.Rep 3850 (unpack 3850 12 (pc p q)) (σ * τ) := by
  intro x
  have hqx := hq x
  rw [CFSG.KS.Raw.Orb.unpack_get x.2] at hqx
  have hpx := hp (τ x)
  rw [CFSG.KS.Raw.Orb.unpack_get (τ x).2] at hpx
  rw [CFSG.KS.Raw.Orb.unpack_get x.2, Equiv.Perm.mul_apply]
  change pg 12 (mask 12) (pcomp 3850 12 (mask 12) p q) x = _
  rw [CFSG.KS.PF.pg_pcomp (by norm_num) x.2, hqx, hpx]

theorem gen_eq : Orb.Gen 3850 hsStrongArrs 2 = hsP := by
  unfold Orb.Gen hsP
  rw [PHSCheck.range_two (fun j => permOfArr 3850 hsStrongArrs[j]!)]
  rfl

section Chain


theorem chain : rawChainOK 3850 (hsStrongArrs.extract 0 2) hsStrongArrs PairHS.baseArr hsWords 4 =
    true := PHSCheck.facts.1.1

theorem head : rawHeadOK 3850 (hsStrongArrs.extract 0 2) hsStrongArrs PairHS.baseArr hsWords =
    true := by
  have h := chain
  unfold rawChainOK at h
  unfold rawHeadOK
  simp only [Bool.and_eq_true] at h ⊢
  exact h.1.1

theorem hd : Orb.Hd 3850 hsStrongArrs PairHS.baseArr 2 hsWords :=
  Orb.hd_of_head (by rw [hsStrongArrs_size]; norm_num) head

theorem rep_ls8 {l : Nat} (hl : l < 16) : ∃ g ∈ hsP,
    CFSG.Monster.B.Co2.Rep 3850 (unpack 3850 12 (ls8 l)) g := by
  unfold ls8 letterK
  rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.blt_dec]
  by_cases h8 : l < 8
  · simp only [h8, decide_true, ↓reduceIte]
    refine ⟨_, gen_eq ▸ Orb.S_mem_Gen hd l (by rw [hsStrongArrs_size]; exact h8), ?_⟩
    rw [← PHSCheck.arr_eq l h8]
    exact Orb.rep_S hd (by rw [hsStrongArrs_size]; exact h8)
  · simp only [h8, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hj : Nat.sub l 8 < 8 := by change l - 8 < 8; omega
    refine ⟨_, inv_mem (gen_eq ▸ Orb.S_mem_Gen hd (Nat.sub l 8)
      (by rw [hsStrongArrs_size]; exact hj)), ?_⟩
    rw [← PHSCheck.inv_eq _ hj]
    exact Orb.rep_Si hd (by rw [hsStrongArrs_size]; exact hj)

theorem rep_word : ∀ (ws : List Nat), (∀ l ∈ ws, l < 16) → ∃ g ∈ hsP,
    CFSG.Monster.B.Co2.Rep 3850 (unpack 3850 12 (wfoldR ls8 ws)) g
  | [], _ => ⟨1, hsP.one_mem, by
      rw [wfoldR_nil, ← idTab_eq]
      exact CFSG.Monster.B.Co2.rep_idA⟩
  | l :: ws, h => by
    obtain ⟨g, hg, hgr⟩ := rep_word ws fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    obtain ⟨s, hs, hsr⟩ := rep_ls8 (h l List.mem_cons_self)
    rw [wfoldR_cons]
    exact ⟨s * g, hsP.mul_mem hs hg, rep_pc hsr hgr⟩

theorem rep_r1 : CFSG.Monster.B.Co2.Rep 3850 (unpack 3850 12 (R1.F 0))
    (permOfArr 3850 (unpack 3850 12 (R1.F 0))) :=
  (CFSG.Monster.B.Co2.rep_permOfArr (invEqK_sound r1_parts.2.1).2).1


theorem sift_iff {T : CFSG.Sporadic.Th.Native.Table} {G : Equiv.Perm (Fin 3850)}
    (hG : CFSG.Monster.B.Co2.Rep 3850 (natArr T) G) : hsSift T = true ↔ G ∈ hsP := by
  rw [hsP_eq_original]
  exact CFSG.Certificates.siftA_iff_mem_originalSubgroup hsChainArrays (by norm_num) chain hG

theorem sift_ru : hsSift (compT 3850 r1T hsOuterTbl) = true := by
  obtain ⟨g, hg, hr⟩ := rep_word wRU (by decide)
  rw [← Nat.eq_of_beq_eq_true ru_ok, ← ru_bind] at hr
  exact (sift_iff hr).2 hg

theorem sift_r1 : hsSift r1T = false := by
  cases hs : hsSift r1T
  · rfl
  · exfalso
    have hr : CFSG.Monster.B.Co2.Rep 3850 (natArr r1T)
        (permOfArr 3850 (unpack 3850 12 (R1.F 0))) := by
      rw [r1_bind]
      exact rep_r1
    have hm := (sift_iff hr).1 hs
    obtain ⟨w, hw, hwr⟩ := rep_word wT (by decide)
    have ht := rep_pc hwr rep_r1
    obtain ⟨hfix, hmove⟩ : allN 4 (fun b => Nat.beq (img (pc (wfoldR ls8 wT) (R1.F 0)) b) b) =
        true ∧ (Nat.beq (img (pc (wfoldR ls8 wT) (R1.F 0)) 5) 5).not = true := by
      simpa only [bAnd_iff] using t_ok
    have h1 : w * permOfArr 3850 (unpack 3850 12 (R1.F 0)) = 1 := by
      refine Orb.fix_one hd PHSCheck.card_le ⟨gen_eq ▸ hsP.mul_mem hw hm, fun t htl hb => ?_⟩
      have htl' : t < 4 := htl
      have hbt : PairHS.baseArr[t]! = t := by interval_cases t <;> rfl
      apply Fin.ext
      rw [← ht.apply hb, CFSG.KS.Raw.Orb.unpack_get hb]
      have := Nat.eq_of_beq_eq_true (allN_spec hfix t htl')
      change pg 12 (mask 12) (pc (wfoldR ls8 wT) (R1.F 0)) PairHS.baseArr[t]! = PairHS.baseArr[t]!
      rw [hbt]
      exact this
    have h5 := ht.apply (i := 5) (by norm_num)
    rw [h1, CFSG.KS.Raw.Orb.unpack_get (by norm_num)] at h5
    have h55 : img (pc (wfoldR ls8 wT) (R1.F 0)) 5 = 5 := h5
    rw [h55, Nat.beq_refl] at hmove
    exact absurd hmove (by decide)

end Chain

theorem a_parts : A.G 0 = HC.F 6 ∧ A.G 1 = HC.F 7 ∧ penumHdK idn A.cnt 7680 A.T A.PL = true ∧
    A.cnt = 7680 := by
  obtain ⟨h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using a_ok :
    Nat.beq (A.G 0) (HC.F 6) = true ∧ Nat.beq (A.G 1) (HC.F 7) = true ∧
      penumHdK idn A.cnt 7680 A.T A.PL = true ∧ Nat.beq A.cnt 7680 = true)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, Nat.eq_of_beq_eq_true h4⟩

theorem gens_ok : GensOK 3850 12 2 A.G gensA0 := by
  obtain ⟨-, c6, c7, -⟩ := canons
  refine ⟨by simp [gensA0], fun j hj => ?_⟩
  interval_cases j
  · have e : gensA0[0]! = natArr (hsCentTbl 6) := by simp [gensA0]
    rw [e, hsCentTbl_eq (by norm_num), a_parts.1]
    exact ⟨rfl, c6⟩
  · have e : gensA0[1]! = natArr (hsCentTbl 7) := by simp [gensA0]
    rw [e, hsCentTbl_eq (by norm_num), a_parts.2.1]
    exact ⟨rfl, c7⟩

theorem nSl_spec {T PL POS SRT SRI : Nat → Nat} {G GI Y1 Y2 C cnt lo len : Nat}
    {AG AI : Nat → Nat}
    (h : nSlK AG AI T PL POS SRT SRI G GI Y1 Y2 C cnt lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → nPtK AG AI T PL POS SRT SRI G GI Y1 Y2 C cnt i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_app'] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem pt : ∀ i < A.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false A.G A.G 2 A.cnt A.T A.PL
      A.POS A.SRT A.SRI i = true ∧ scanK (X 0) (X 1) (X 2) (X 3) (X 4) (A.T i) = true := by
  intro i hi
  have hi' : i < 7680 := a_parts.2.2.2 ▸ hi
  have hs : i / 8 < 960 := by omega
  have hc : nSlK A.G A.G A.T A.PL A.POS A.SRT A.SRI (X 0) (X 1) (X 2) (X 3) (X 4) A.cnt
      (Nat.mul (i / 8) 8) 8 = true := A.all (i / 8) hs
  have h := nSl_spec hc i (by change i / 8 * 8 ≤ i; omega) (by change i < i / 8 * 8 + 8; omega) hi
  exact (bAnd_iff _ _).1 h

theorem enum_eq : enumA0 = penumRec 3850 12 A.cnt A.T A.PL ∧
    enumOK 3850 gensA0 (penumRec 3850 12 A.cnt A.T A.PL) = true :=
  penumK_left_sound hn gens_ok a_parts.2.2.1 fun i hi => (pt i hi).1

theorem tabs_get {k : Nat} (hk : k < A.cnt) :
    (penumRec 3850 12 A.cnt A.T A.PL).tabs[k]! = unpack 3850 12 (A.T k) := by
  rw [getElem!_pos _ k (by simp [penumRec, hk])]
  simp [penumRec]

theorem img_pc {p q i : Nat} (hi : i < 3850) : img (pc p q) i = img p (img q i) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hi

theorem img_lt {p i : Nat} (hp : Cn p) (hi : i < 3850) : img p i < 3850 :=
  (CFSG.KS.PF.canon_facts hp).2.2.2 i hi

theorem img_S {G X GI q : Nat} (hGI : Cn GI) (hq : q < 3850) :
    img (pc (pc G X) GI) q = sAt G X GI q := by
  rw [img_pc hq, img_pc (img_lt hGI hq)]
  rfl

theorem wit_ne {G GI Y X p : Nat} (hY : Cn Y) (hGI : Cn GI)
    (hp : p < 3850) (h : witK G GI Y X p = true) : Nat.beq (pc (pc (pc G X) GI) Y)
      (pc Y (pc (pc G X) GI)) = false := by
  unfold witK at h
  cases hb : Nat.beq (pc (pc (pc G X) GI) Y) (pc Y (pc (pc G X) GI))
  · rfl
  · exfalso
    have e2 : img (pc (pc (pc G X) GI) Y) p = img (pc Y (pc (pc G X) GI)) p :=
      congrArg (fun z => img z p) (Nat.eq_of_beq_eq_true hb)
    have e3 : sAt G X GI (img Y p) = img Y (sAt G X GI p) := by
      rw [← img_S hGI (img_lt hY hp), ← img_S hGI hp, ← img_pc hp, ← img_pc hp]
      exact e2
    rw [e3, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem scan_of {G GI Y1 Y2 C X : Nat} (hGI : Cn GI) (hY1 : Cn Y1) (hY2 : Cn Y2)
    (h : scanK G GI Y1 Y2 C X = true) :
    (!(Nat.beq (pc (pc (pc G X) GI) Y1) (pc Y1 (pc (pc G X) GI)) &&
        Nat.beq (pc (pc (pc G X) GI) Y2) (pc Y2 (pc (pc G X) GI))) ||
      Nat.beq (pc (pc G X) GI) idn || Nat.beq (pc (pc G X) GI) C) = true := by
  unfold scanK at h
  cases h1 : witK G GI Y1 X 0
  · cases h2 : witK G GI Y1 X 1
    · cases h3 : witK G GI Y2 X 0
      · cases h4 : witK G GI Y2 X 1
        · rw [h1, h2, h3, h4] at h
          change strictB (pc (pc G X) GI) (fun S => bIf(Nat.beq S idn, true, Nat.beq S C)) = true
            at h
          rw [strictB_app'] at h
          cases h5 : Nat.beq (pc (pc G X) GI) idn
          · rw [h5] at h
            change Nat.beq (pc (pc G X) GI) C = true at h
            simp [h]
          · simp
        · simp [wit_ne hY2 hGI (by norm_num) h4]
      · simp [wit_ne hY2 hGI (by norm_num) h3]
    · simp [wit_ne hY1 hGI (by norm_num) h2]
  · simp [wit_ne hY1 hGI (by norm_num) h1]

theorem scanRow_of {k : Nat} (hk : k < A.cnt) : scanRow k = true := by
  have hT := penumPt_canon (pt k hk).1
  have c0 := cX (j := 0) (by norm_num)
  have c1 := cX (j := 1) (by norm_num)
  have c2 := cX (j := 2) (by norm_num)
  have c3 := cX (j := 3) (by norm_num)
  have c4 := cX (j := 4) (by norm_num)
  have hS := cPc (cPc c0 hT) c1
  unfold scanRow scanTab conjTab
  rw [enum_eq.1, tabs_get hk, g_eq, gi_eq, y1_eq, y2_eq, c_eq, comp_pc c0 hT, comp_pc (cPc c0 hT) c1,
    comp_pc hS c2, comp_pc c2 hS, comp_pc hS c3, comp_pc c3 hS, beq_pc (cPc hS c2) (cPc c2 hS),
    beq_pc (cPc hS c3) (cPc c3 hS), idTab_eq, beq_pc hS cIdn, beq_pc hS c4]
  exact scan_of c1 c2 c3 (pt k hk).2

theorem sizes_ok : chkSizes = true := by
  obtain ⟨c0, c6, c7, -⟩ := canons
  unfold chkSizes
  simp only [Bool.and_eq_true, allBelow, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨⟨fun l hl => ?_, fun l hl => ?_⟩, ?_⟩, r1_perm⟩, r1_size⟩
  · rw [(letter_arr hl).1, unpack_size]
  · interval_cases l
    · exact ⟨cent_perm (by norm_num) c6, cent_size (by norm_num)⟩
    · exact ⟨cent_perm (by norm_num) c7, cent_size (by norm_num)⟩
  · exact cent_perm (k := 0) (by norm_num) c0

theorem enum_ok : chkEnum = true := by
  unfold chkEnum
  rw [enum_eq.1, enum_eq.2]
  simp [penumRec, a_parts.2.2.2]

theorem conj_ok' : chkConj = true := by
  have c0 := cX (j := 0) (by norm_num)
  have ca := canons.2.2.2.1
  unfold chkConj
  have ea : a0Tab = unpack 3850 12 (HS.F 0) := (letter_arr (l := 0) (by norm_num)).1
  rw [g_eq, ea, e_eq.1, gi_eq, comp_pc c0 ca, comp_pc e_eq.2 c0, beq_pc (cPc c0 ca) (cPc e_eq.2 c0),
    comp_inv_id (invEqK_sound x1_ok).2, conj_ok]
  simp [unpack_size]

theorem scan_ok : chkScan = true := by
  unfold chkScan
  rw [enum_eq.1]
  simp only [allBelow, List.all_eq_true, List.mem_range]
  intro k hk
  have hk' : k < A.cnt := by simpa [penumRec] using hk
  exact scanRow_of hk'

theorem r1_check : chkR1 = true := by
  obtain ⟨cr, hinv, h2, h3⟩ := r1_parts
  have c2 := cX (j := 2) (by norm_num)
  have c3 := cX (j := 3) (by norm_num)
  unfold chkR1
  have er : r1Tab = unpack 3850 12 (R1.F 0) := r1_bind
  rw [er, comp_inv_id (invEqK_sound hinv).2, y1_eq, y2_eq, comp_pc cr c2, comp_pc c2 cr,
    comp_pc cr c3, comp_pc c3 cr, beq_pc (cPc cr c2) (cPc c2 cr), beq_pc (cPc cr c3) (cPc c3 cr),
    h2, h3, sift_r1, sift_ru]
  simp

theorem nodes_check :
    nodesCheck = true := by
  unfold nodesCheck
  rw [sizes_ok, enum_ok, conj_ok', scan_ok, r1_check]
  rfl

end CFSG.KD.LQT.HN

end
