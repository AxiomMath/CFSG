module

public import Certificates.Kernel.HS3850.C23005E0
public import Certificates.Kernel.HS3850.C23005E1
public import Certificates.Kernel.HS3850.C23005E2
public import Certificates.Kernel.HS3850.C23005E3
public import Certificates.Kernel.HS3850.C23005Z0
public import Certificates.Kernel.HS3850.C23005Z1
public import Certificates.Kernel.HS3850.Kit
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import Certificates.Data.GSThmBCatalog5CovHS
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH
public import Certificates.Kernel.LocalQT.HSAut.F4146

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.HS3850.EC CFSG.KD.HS3850.ckC 60
#kqb_all CFSG.KD.HS3850.ECZ CFSG.KD.HS3850.ckZ 60

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.GSThmB.CovHS
open CFSG.KD.LQT.HO (Cn cIdn foldr_unp)

theorem hd_parts : EC.cnt = 1920 ∧ EQ.cnt = 16 ∧ penumHdK idn EC.cnt 1920 EC.T EC.PL = true ∧
    penumHdK idn EQ.cnt 16 EQ.T EQ.PL = true ∧
    allN 4 (fun l => bAnd(Nat.beq (EC.G l) (lc4 l),
      bAnd(canonK 3850 12 (mask 12) (3850 * 12) (lc4i l), Nat.beq (pc (lc4 l) (lc4i l)) idn))) =
        true ∧
    EQ.G 0 = wfoldR lc4 [0, 1, 0, 3, 0, 2, 1, 3] ∧ EQ.G 1 = wfoldR lc4 [0, 3, 0, 2, 1, 3, 0, 1] ∧
    EQ.G 2 = wfoldR lc4 [1, 1, 0, 2, 3, 0, 1, 3] ∧ EQ.G 3 = wfoldR lc4 [0, 1, 3, 1, 1, 0, 2, 3] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (by simpa only [bAnd_iff] using hd_ok :
    Nat.beq EC.cnt 1920 = true ∧ Nat.beq EQ.cnt 16 = true ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, h4, h5,
    Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8,
    Nat.eq_of_beq_eq_true h9⟩

theorem c4_parts {l : Nat} (hl : l < 4) : EC.G l = lc4 l ∧ Cn (lc4 l) ∧ Cn (lc4i l) ∧
    pc (lc4 l) (lc4i l) = idn := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using allN_spec hd_parts.2.2.2.2.1 l hl :
    Nat.beq (EC.G l) (lc4 l) = true ∧ _ ∧ Nat.beq (pc (lc4 l) (lc4i l)) idn = true)
  exact ⟨Nat.eq_of_beq_eq_true h1, (cent_parts (k := 35 + l) (by omega)).2, h2,
    Nat.eq_of_beq_eq_true h3⟩

theorem c4Tabs_get {l : Nat} (hl : l < 4) : c4Tabs[l]! = unpack 3850 12 (lc4 l) := by
  have e : c4Tabs[l]! = natArr (hsCentTbl (l + 35)) := by
    unfold c4Tabs
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  rw [e, Nat.add_comm]
  exact (cent_parts (by omega)).1

theorem c4Word {ls : List Nat} (hls : ∀ l ∈ ls, l < 4) :
    wordTabS 3850 c4Tabs ls = unpack 3850 12 (wfoldR lc4 ls) ∧ Cn (wfoldR lc4 ls) :=
  wordTabS_unp ls fun l hl => ⟨c4Tabs_get (hls l hl), (c4_parts (hls l hl)).2.1⟩

theorem gensC : GensOK 3850 12 4 EC.G c4Tabs := by
  refine ⟨by simp [c4Tabs], fun j hj => ?_⟩
  rw [(c4_parts hj).1, c4Tabs_get hj]
  exact ⟨rfl, (c4_parts hj).2.1⟩

theorem qGens_get {j : Nat} (hj : j < 4) :
    qGens[j]! = wordTabS 3850 c4Tabs (qWords.getD j []) := by
  unfold qGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem eqG_eq {j : Nat} (hj : j < 4) : EQ.G j = wfoldR lc4 (qWords.getD j []) := by
  obtain ⟨-, -, -, -, -, e0, e1, e2, e3⟩ := hd_parts
  interval_cases j
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem qWords_lt {j : Nat} : ∀ l ∈ qWords.getD j [], l < 4 := by
  rcases j with _ | _ | _ | _ | j <;> simp [qWords]

theorem gensQ : GensOK 3850 12 4 EQ.G qGens := by
  refine ⟨by simp [qGens], fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := c4Word (qWords_lt (j := j))
  rw [qGens_get hj, h1, eqG_eq hj]
  exact ⟨rfl, h2⟩

theorem ptC : ∀ i < EC.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false EC.G EC.GI 4 EC.cnt EC.T
    EC.PL EC.POS EC.SRT EC.SRI i = true := by
  intro i hi
  have hi' : i < 1920 := hd_parts.1 ▸ hi
  have hs : i / 32 < 60 := by omega
  exact penumSl_spec (EC.all (i / 32) hs) i (by change i / 32 * 32 ≤ i; omega)
    (by change i < i / 32 * 32 + 32; omega) hi

theorem ptQ : ∀ i < EQ.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false EQ.G EQ.GI 4 EQ.cnt EQ.T
    EQ.PL EQ.POS EQ.SRT EQ.SRI i = true := by
  intro i hi
  exact penumSl_spec eq_ok i (Nat.zero_le _) (by rw [hd_parts.2.1] at hi; omega) hi

theorem encC : enumBFS 3850 c4Tabs 1920 = penumRec 3850 12 EC.cnt EC.T EC.PL ∧
    enumOK 3850 c4Tabs (penumRec 3850 12 EC.cnt EC.T EC.PL) = true :=
  penumK_left_sound (by decide) gensC hd_parts.2.2.1 ptC

theorem encQ : enumBFS 3850 qGens 16 = penumRec 3850 12 EQ.cnt EQ.T EQ.PL ∧
    enumOK 3850 qGens (penumRec 3850 12 EQ.cnt EQ.T EQ.PL) = true :=
  penumK_left_sound (by decide) gensQ hd_parts.2.2.2.1 ptQ

theorem canonC {i : Nat} (hi : i < EC.cnt) : Cn (EC.T i) := penumPt_canon (ptC i hi)

theorem invs : (∀ k < 4, c4Invs[k]! = unpack 3850 12 (lc4i k)) ∧ invsOK 3850 c4Tabs c4Invs = true :=
  CFSG.KC.L34KSnd.invsOK_of_pcomp (by simp [c4Tabs]) (fun k hk => c4Tabs_get hk)
    fun k hk => ⟨(c4_parts hk).2.1, (c4_parts hk).2.2.1, (c4_parts hk).2.2.2⟩

theorem inQ_found {X : Nat} (h : inQ X = true) :
    found (indexOf (penumRec 3850 12 EQ.cnt EQ.T EQ.PL).tabs) (penumRec 3850 12 EQ.cnt EQ.T EQ.PL).tabs
      (unpack 3850 12 X) = true := by
  unfold inQ at h
  have hq : ∃ q < 16, EQ.T q = X := by
    by_contra hn
    have : allN 16 (fun q => (Nat.beq (EQ.T q) X).not) = true :=
      CFSG.KS.Raw.Orb.allN_iff.2 fun q hq => by
        cases hb : Nat.beq (EQ.T q) X
        · rfl
        · exact absurd ⟨q, hq, Nat.eq_of_beq_eq_true hb⟩ hn
    rw [this] at h
    exact Bool.false_ne_true h
  obtain ⟨q, hq, e⟩ := hq
  exact CFSG.KC.L34KSnd.found_pts (by rw [hd_parts.2.1]; exact hq) e

theorem qG_parts {i : Nat} (hi : i < 4) : qGens[i]! = unpack 3850 12 (EQ.G i) ∧ Cn (EQ.G i) :=
  gensQ.2 i hi

theorem normal_ok : normalOK 3850 (penumRec 3850 12 EQ.cnt EQ.T EQ.PL).tabs c4Tabs c4Invs qGens =
    true := by
  unfold normalOK
  rw [invs.2, Bool.true_and, CFSG.KS.BfsReplay.allBelow_iff]
  intro j hj
  have hj' : j < 4 := by simpa [c4Tabs] using hj
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  have hi' : i < 4 := by simpa [qGens] using hi
  obtain ⟨-, cg, cgi, -⟩ := c4_parts hj'
  obtain ⟨hq, cq⟩ := qG_parts hi'
  obtain ⟨h1, h2⟩ := (by simpa only [bAnd_iff] using allN_spec (allN_spec norm_ok j hj') i hi' :
    inQ (pc (pc (lc4 j) (EQ.G i)) (lc4i j)) = true ∧ inQ (pc (pc (lc4i j) (EQ.G i)) (lc4 j)) = true)
  unfold conjTab
  rw [c4Tabs_get hj', invs.1 j hj', hq, comp_pc' cg cq, comp_pc' (cn_pc cg cq) cgi,
    comp_pc' cgi cq, comp_pc' (cn_pc cgi cq) cg, inQ_found h1, inQ_found h2]
  rfl

theorem commAll_eq {x : Nat} (hx : Cn x) :
    commAll 3850 qGens (unpack 3850 12 x) = commQ x := by
  unfold commAll commQ
  rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
  have hs : qGens.size = 4 := by simp [qGens]
  rw [hs]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  obtain ⟨hq, cq⟩ := qG_parts hj
  rw [hq, comp_pc' hx cq, comp_pc' cq hx, beq_pc' (cn_pc hx cq) (cn_pc cq hx)]

theorem commQ_eq {i : Nat} (hi : i < 1920) : commQ (EC.T i) = centIdx.elem i := by
  have hs : i / 32 < 60 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (ECZ.all (i / 32) hs) (i % 32) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul (i / 32) 32) (i % 32) = i := by
    change i / 32 * 32 + i % 32 = i
    omega
  rw [CFSG.KS.PEnum.strictB_app', e] at h
  have hb : Nat.blt i 1920 = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  exact beq_iff_eq.1 h

theorem cent_count :
    ((penumRec 3850 12 EC.cnt EC.T EC.PL).tabs.toList.filter (commAll 3850 qGens)).length = 16 := by
  have e := CFSG.KS.PEnum.filter_ofFn EC.cnt (fun i => unpack 3850 12 (EC.T i)) (commAll 3850 qGens)
  have hc : ((List.range EC.cnt).filter fun i => commAll 3850 qGens (unpack 3850 12 (EC.T i))) =
      (List.range EC.cnt).filter fun i => centIdx.elem i := by
    apply List.filter_congr
    intro i hi
    rw [commAll_eq (canonC (List.mem_range.1 hi)),
      commQ_eq (hd_parts.1 ▸ List.mem_range.1 hi)]
  unfold penumRec
  dsimp only
  rw [← Array.toList_filter, e, List.toList_toArray, List.length_map, hc,
    ← CFSG.KC.Misc.RuInv.P.foldN_count, hd_parts.1]
  exact Nat.eq_of_beq_eq_true cent_ok

theorem outerCheck_true : outerCheck = true := by
  unfold outerCheck
  have hsz := encC
  have hq := encQ
  unfold qEnum c4Enum
  rw [hsz.1, hq.1, hsz.2, hq.2, normal_ok, cent_count]
  have hs1 : (penumRec 3850 12 EC.cnt EC.T EC.PL).tabs.size = 1920 := by
    simp [penumRec, hd_parts.1]
  have hs2 : (penumRec 3850 12 EQ.cnt EQ.T EQ.PL).tabs.size = 16 := by
    simp [penumRec, hd_parts.2.1]
  rw [hs1, hs2]
  have hp : allBelow 4 (fun k => CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl (k + 35)) &&
      (natArr (hsCentTbl (k + 35))).size == 3850) = true := by
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    rw [Bool.and_eq_true]
    refine ⟨CFSG.KD.LQT.HN.cent_perm (by omega) (cent_parts (by omega)).2, ?_⟩
    rw [(cent_parts (k := k + 35) (by omega)).1]
    simp [CFSG.KS.PEnum.unpack_size]
  rw [hp]
  decide

end CFSG.KD.HS3850

end
