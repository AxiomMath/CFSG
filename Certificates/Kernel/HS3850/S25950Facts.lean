module

public import Certificates.Kernel.HS3850.S25950S
public import Certificates.Kernel.HS3850.Q25551Facts
public import Certificates.Kernel.HS3850.CoverFacts

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.HS3850.ES CFSG.KD.HS3850.ckS 240

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KC.PkPow
open CFSG.KD.LQT.C4126 CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open CFSG.KD.LQT.HO (Cn cIdn)
open CFSG.KD.LQT.HN (ls8)
open CFSG.KS.MulH
open CFSG.Sporadic.Th.Native (ap)

theorem ok25950_parts : Nat.beq sW2 (HC.F 5) = true ∧ Nat.beq (pc sX sX) idn = true ∧
    Nat.beq (pc sX sW) (pc sW3 sX) = true ∧ Nat.beq (fx (HC.F 5)) 170 = true ∧
    Nat.beq (fx (HC.F 12)) 30 = true ∧ Nat.beq (fx sX) 170 = true ∧
    Nat.beq (fx (pc sX (HC.F 5))) 170 = true ∧
    Nat.beq (fx (pc sX sW)) 30 = true ∧ Nat.beq (fx cvX) 170 = true ∧
    Nat.beq (fx (wfoldR ls8 (s6CWord.map Int.toNat))) 30 = true := by
  have h := ok25950
  simp only [bAnd_iff] at h
  exact h

theorem wTab : s6WTab = unpack 3850 12 sW ∧ Cn sW := by
  unfold s6WTab
  exact c1Word (by decide)

theorem w2Tab : s6W2Tab = unpack 3850 12 sW2 ∧ Cn sW2 := by
  obtain ⟨e, c⟩ := wTab
  unfold s6W2Tab
  rw [e, comp_pc' c c]
  exact ⟨rfl, cn_pc c c⟩

theorem w3Tab : s6W3Tab = unpack 3850 12 sW3 ∧ Cn sW3 := by
  obtain ⟨e, c⟩ := w2Tab
  unfold s6W3Tab
  rw [e, wTab.1, comp_pc' c wTab.2]
  exact ⟨rfl, cn_pc c wTab.2⟩

theorem xTab : s6XTab = unpack 3850 12 sX ∧ Cn sX := by
  unfold s6XTab
  exact c1Word (by decide)

theorem isW_eq {Y : Nat} (hY : Cn Y) : s6IsW (unpack 3850 12 Y) = isWK Y := by
  unfold s6IsW isWK
  rw [idTab_idn, wTab.1, w2Tab.1, w3Tab.1, beq_pc' hY cIdn, beq_pc' hY wTab.2,
    beq_pc' hY w2Tab.2, beq_pc' hY w3Tab.2]

theorem strong_of {W G0 G1 X : Nat} (hW : Cn W) (h0 : Cn G0) (h1 : Cn G1) (hX : Cn X)
    (h : sF W G0 G1 X = true) :
    ((!(cmK X G0 && cmK X G1) || isWK X) &&
      (!(cmK (pc W X) G0 && cmK (pc W X) G1) || isWK (pc W X))) = true := by
  unfold sF at h
  rw [CFSG.KS.PEnum.strictB_app'] at h
  obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 h
  rw [Bool.and_eq_true]
  exact ⟨half_of _ _ _ _ _ (cmK_of_ptc hX h0) (cmK_of_ptc hX h1) ha,
    half_of _ _ _ _ _ (cmK_of_ptc2 hW hX h0) (cmK_of_ptc2 hW hX h1) hb⟩

theorem ptS_of {i : Nat} (hi : i < 7680) : ptS i = true := by
  have hs : i / 32 < 240 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (ES.all (i / 32) hs) (i % 32) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul (i / 32) 32) (i % 32) = i := by
    change i / 32 * 32 + i % 32 = i
    omega
  rw [CFSG.KS.PEnum.strictB_app', e] at h
  have hb : Nat.blt i 7680 = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  exact h

theorem strong_true : s6Strong = true := by
  obtain ⟨ha, ca⟩ := tabA_eq
  obtain ⟨hb, cb⟩ := tabB_eq
  have hgs : hsOdd1Tabs = #[unpack 3850 12 q1A, unpack 3850 12 q1B] := by
    unfold hsOdd1Tabs
    rw [ha, hb]
  have hW : Cn (FT.F 0) := ok_parts.1
  unfold s6Strong s6StrongCheck
  rw [c1Enum_eq, facts_eq (k := 0) (by norm_num)]
  unfold penumRec
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < CFSG.KD.LQT.HN.A.cnt := by simpa using hi
  simp only [Array.getElem_ofFn]
  have hX := canonA hi'
  have hq := ptS_of (cnt_A ▸ hi')
  unfold ptS at hq
  rw [CFSG.KS.PEnum.strictB_app'] at hq
  rw [all_two hgs, all_two hgs, commPt_eq hX ca, commPt_eq hX cb, commPt2_eq hW hX ca,
    commPt2_eq hW hX cb, isW_eq hX, comp_pc' hW hX, isW_eq (cn_pc hW hX)]
  exact strong_of hW ca cb hX hq

theorem wsq_true : s6WSq = true := by
  unfold s6WSq
  rw [w2Tab.1, (cent_parts (k := 5) (by norm_num)).1,
    beq_pc' w2Tab.2 (cent_parts (k := 5) (by norm_num)).2]
  exact ok25950_parts.1

theorem xrel_true : s6XRel = true := by
  obtain ⟨ex, cx⟩ := xTab
  obtain ⟨ew, cw⟩ := wTab
  obtain ⟨ew3, cw3⟩ := w3Tab
  unfold s6XRel
  rw [ex, ew, ew3, comp_pc' cx cx, idTab_idn, beq_pc' (cn_pc cx cx) cIdn, comp_pc' cx cw,
    comp_pc' cw3 cx, beq_pc' (cn_pc cx cw) (cn_pc cw3 cx), ok25950_parts.2.1,
    ok25950_parts.2.2.1]
  rfl

theorem fixTab_eq (p : Nat) : fixTab 3850 (unpack 3850 12 p) = fx p := by
  unfold fixTab
  exact countP_nfix 3850 12 p

theorem fixTbl_eq {p : Nat} (hp : Cn p) : fixTbl 3850 (tabT (unpack 3850 12 p)) = fx p := by
  rw [← fixTab_eq]
  unfold fixTbl fixTab
  apply List.countP_congr
  intro i _
  rw [CFSG.KS.MulH.ap_tabT _ (CFSG.KS.MulH.unpack_lt hp)]

theorem fix_true : s6Fix = true := by
  obtain ⟨ex, cx⟩ := xTab
  obtain ⟨ew, cw⟩ := wTab
  obtain ⟨e5, c5⟩ := cent_parts (k := 5) (by norm_num)
  obtain ⟨e12, -⟩ := cent_parts (k := 12) (by norm_num)
  obtain ⟨-, -, -, f1, f2, f3, f4, f5, f6, f7⟩ := ok25950_parts
  obtain ⟨ec, cc⟩ := wordT_ls8 s6CWord (by decide)
  have hs : (unpack 3850 12 (HC.F 12)).size = 3850 := by simp [unpack]
  unfold s6Fix s6FixOK s6FixCoverOK
  rw [cperm (k := 12) (by norm_num), e12, hs, e5, ex, comp_pc' cx c5, ew, comp_pc' cx cw,
    fixTab_eq, fixTab_eq, fixTab_eq, fixTab_eq, fixTab_eq, x_tab, fixTbl_eq a_parts.1, ec,
    fixTbl_eq cc]
  rw [Nat.eq_of_beq_eq_true f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3,
    Nat.eq_of_beq_eq_true f4, Nat.eq_of_beq_eq_true f5, Nat.eq_of_beq_eq_true f6,
    Nat.eq_of_beq_eq_true f7]
  rfl

end CFSG.KD.HS3850

end
