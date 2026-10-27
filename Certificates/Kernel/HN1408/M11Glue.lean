module

public import Certificates.Kernel.HN1408.M11Chk
public import Certificates.Kernel.HN1408.M11RP
public import Certificates.Kernel.HN1408.M11RH0
public import Certificates.Kernel.HN1408.M11RH1
public import Certificates.Kernel.HN1408.M11RA1
public import Certificates.Kernel.HN1408.M11RA2
public import Certificates.Kernel.HN1408.M11O
public import Certificates.Kernel.HN1408.M11CZ
public import Certificates.Kernel.HN1408.M11CAZ
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.PEnumRSound
import CFSG.Certificates.Kernel.Spor.PEnumBSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

#kc_forall_chunks peR_all (fun s => peR s = true) 8 CFSG.KD.HN1408.peR 1
#kc_forall_chunks hvR_all (fun s => hvR s = true) 16 CFSG.KD.HN1408.hvR 1
#kc_forall_chunks hsR_all (fun s => hsR s = true) 2 CFSG.KD.HN1408.hsR 1
#kc_forall_chunks clA_all (fun s => clA s = true) 16 CFSG.KD.HN1408.clA 1
#kc_forall_chunks oA_all (fun s => oA s = true) 8 CFSG.KD.HN1408.oA 1

theorem mkA {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := (bAnd_iff _ _).1 h

theorem mkIf {c a b : Bool} (h : bIf(c, a, b) = true) :
    (c = true ∧ a = true) ∨ (c = false ∧ b = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem mkNot {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem mkAndNot {a b : Bool} (h : bAnd(a, bIf(b, false, true)) = true) : (a && !b) = true := by
  obtain ⟨h1, h2⟩ := mkA h
  rw [h1, mkNot h2]
  rfl

theorem pc_id_left {Y : Nat} (hY : Cn Y) : pc idK Y = Y :=
  CFSG.KC.L34KSnd.eq_of_pg (canonK_pcomp cId hY) hY fun i hi => by
    change pt (pc idK Y) i = pt Y i
    rw [pt_pc cId hi, pt_id (pt_lt hY hi)]

theorem pc_id_right {Y : Nat} (hY : Cn Y) : pc Y idK = Y :=
  CFSG.KC.L34KSnd.eq_of_pg (canonK_pcomp hY cId) hY fun i hi => by
    change pt (pc Y idK) i = pt Y i
    rw [pt_pc hY hi, pt_id hi]

theorem ppK_add {X : Nat} (hX : Cn X) : ∀ a b, ppK X (a + b) = pc (ppK X a) (ppK X b)
  | 0, b => by
    rw [Nat.zero_add]
    exact (pc_id_left (cn_ppK hX b)).symm
  | a + 1, b => by
    rw [Nat.add_right_comm]
    change pc X (ppK X (a + b)) = pc (pc X (ppK X a)) (ppK X b)
    rw [ppK_add hX a b]
    exact (CFSG.KC.L34KSnd.pcomp_assoc' hX (cn_ppK hX a) (cn_ppK hX b)).symm

theorem ppK_two {X : Nat} (hX : Cn X) : ppK X 2 = pc X X := by
  have h1 : ppK X 1 = X := pc_id_right hX
  have h := ppK_add hX 1 1
  rw [h1] at h
  exact h

theorem ppK_four {X : Nat} (hX : Cn X) : ppK X 4 = pc (pc X X) (pc X X) := by
  have h := ppK_add hX 2 2
  rw [ppK_two hX] at h
  exact h

theorem ppK_eight {X : Nat} (hX : Cn X) :
    ppK X 8 = pc (pc (pc X X) (pc X X)) (pc (pc X X) (pc X X)) := by
  have h := ppK_add hX 4 4
  rw [ppK_four hX] at h
  exact h

theorem ppK_six {X : Nat} (hX : Cn X) : ppK X 6 = pc (pc X (pc X X)) (pc X (pc X X)) := by
  have h3 : ppK X 3 = pc X (pc X X) := by
    change pc X (ppK X 2) = _
    rw [ppK_two hX]
  have h := ppK_add hX 3 3
  rw [h3] at h
  exact h

theorem ppK_five {X : Nat} (hX : Cn X) : ppK X 5 = pc X (pc (pc X X) (pc X X)) := by
  change pc X (ppK X 4) = _
  rw [ppK_four hX]

theorem ppK_eleven {X : Nat} (hX : Cn X) :
    ppK X 11 = pc X (pc (pc (pc (pc X X) (pc X X)) (pc (pc X X) (pc X X))) (pc X X)) := by
  have h := ppK_add hX 8 2
  rw [ppK_eight hX, ppK_two hX] at h
  change pc X (ppK X 10) = _
  rw [h]

theorem ordK_spec {X e : Nat} (hX : Cn X) (h : ordK X e = true) :
    ordInS (idT 1408) (tabT (unpack 1408 11 X)) = true := by
  unfold ordK at h
  simp only [strictB_app] at h
  rcases mkIf h with ⟨he, h⟩ | ⟨-, h⟩
  · have e8 := Nat.eq_of_beq_eq_true he
    subst e8
    exact ordInS_of hX (Or.inl rfl) (by rw [ppK_eight hX]; exact h)
  rcases mkIf h with ⟨he, h⟩ | ⟨-, h⟩
  · have e6 := Nat.eq_of_beq_eq_true he
    subst e6
    exact ordInS_of hX (Or.inr (Or.inl rfl)) (by rw [ppK_six hX]; exact h)
  rcases mkIf h with ⟨he, h⟩ | ⟨-, h⟩
  · have e5 := Nat.eq_of_beq_eq_true he
    subst e5
    exact ordInS_of hX (Or.inr (Or.inr (Or.inl rfl))) (by rw [ppK_five hX]; exact h)
  rcases mkIf h with ⟨he, h⟩ | ⟨-, h⟩
  · have e11 := Nat.eq_of_beq_eq_true he
    subst e11
    exact ordInS_of hX (Or.inr (Or.inr (Or.inr rfl))) (by rw [ppK_eleven hX]; exact h)
  · exact absurd h Bool.false_ne_true

theorem headM_spec {ws : List (List Nat)} {k m cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (h : headM ws k m G GI GJ T PL cnt = true) :
    ws.length = k ∧ (∀ j < k, GI j = WK (ws.getD j []) ∧ G j = idK ∧
      canonK 1408 11 (mask 11) (1408 * 11) (GJ j) = true ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j) = true) ∧ cnt = m ∧
      penumHdK idK cnt 1000000 T PL = true := by
  unfold headM at h
  obtain ⟨h1, h2⟩ := mkA h
  obtain ⟨h3, h4⟩ := mkA h2
  obtain ⟨h5, h6⟩ := mkA h4
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_, Nat.eq_of_beq_eq_true h5, h6⟩
  obtain ⟨a, h8⟩ := mkA (allN_spec h3 j hj)
  obtain ⟨b, h9⟩ := mkA h8
  obtain ⟨c, d⟩ := mkA h9
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c, d⟩

abbrev RecM (ws : List (List Nat)) (m cnt : Nat) (T PL : Nat → Nat) : Prop :=
  enumW invCap m ws = true ∧ subgroupList invCap ws = (hRec 1408 11 cnt T PL).1 ∧ ∀ i < cnt, Cn (T i)

theorem recM_of {ws : List (List Nat)} {k m cnt : Nat}
    {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (h : headM ws k m G GI GJ T PL cnt = true)
    (hp : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 1408 11 (mask 11) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 1408 11 (mask 11) (k + k) T (bothK k GI GJ)) CL c = true) :
    RecM ws m cnt T PL := by
  obtain ⟨hk, hg, hm, hh⟩ := headM_spec h
  subst hk
  obtain ⟨e1, e2⟩ := enumW_of (cap := invCap) hl (fun j hj => (hg j hj).2.1) (fun j hj => (hg j hj).1)
    (fun j hj => ⟨(hg j hj).2.2.2, (hg j hj).2.2.1⟩) hh hp hs hcl hm
  exact ⟨e1, e2, fun i hi => penumPt_canon (hp i hi)⟩

theorem cntA : MR1.cnt = 7920 := (headM_spec kHA).2.2.1

theorem recA : RecM [y0Word, vWord] 7920 MR1.cnt MR1.T MR1.PL := by
  obtain ⟨-, hg, -, hh⟩ := headM_spec kHA
  have hGI : ∀ j < 2, canonK 1408 11 (mask 11) (1408 * 11) (MR1.GI j) = true := by
    intro j hj
    rw [(hg j hj).1]
    match j, hj with
    | 0, _ => exact (tabW_eq (by decide) :
        tabW y0Word = tabT (unpack 1408 11 (WK y0Word)) ∧ Cn (WK y0Word)).2
    | 1, _ => exact (tabW_eq (by decide) :
        tabW vWord = tabT (unpack 1408 11 (WK vWord)) ∧ Cn (WK vWord)).2
  have hv : ∀ i < MR1.cnt, CFSG.KS.PEnumB.hvK 1408 11 (mask 11) MR1.T MR1V i = true := by
    intro i hi
    rw [← CFSG.KS.PEnumR.hvF_eq (n := 1408) (by decide)]
    exact slAll (L := 495) (K := 16) (by rw [cntA]) (fun s hs => hvR_all s hs) i hi
  exact recM_of (by decide) kHA
    (CFSG.KS.PEnumR.penumPtK_of_R (by decide) hGI (fun j hj => (hg j hj).2.1) hh
      (slAll (L := 990) (K := 8) (by rw [cntA]) fun s hs => peR_all s hs))
    (CFSG.KS.PEnumB.hsortPtK_of_V hv
      (slAll (L := 3960) (K := 2) (by rw [cntA]) fun s hs => hsR_all s hs))
    (slAll (L := 1980) (K := 16) (by rw [cntA]) fun s hs => clA_all s hs)

theorem wY : tabW y0Word = tabT (unpack 1408 11 (WK y0Word)) ∧ Cn (WK y0Word) := tabW_eq (by decide)
theorem wV : tabW vWord = tabT (unpack 1408 11 (WK vWord)) ∧ Cn (WK vWord) := tabW_eq (by decide)
theorem wI : tabW i0Word = tabT (unpack 1408 11 (WK i0Word)) ∧ Cn (WK i0Word) := tabW_eq (by decide)
theorem wN : tabW n1Word = tabT (unpack 1408 11 (WK n1Word)) ∧ Cn (WK n1Word) := tabW_eq (by decide)
theorem wR : tabW rho0Word = tabT (unpack 1408 11 (WK rho0Word)) ∧ Cn (WK rho0Word) :=
  tabW_eq (by decide)
theorem wF : tabW fix5B.rep = tabT (unpack 1408 11 (WK fix5B.rep)) ∧ Cn (WK fix5B.rep) :=
  tabW_eq (by decide)

theorem inv_of {j : Nat} (hj : j < 7) : Cn (MInv j) ∧
    invEqK 1408 11 (mask 11) (1408 * 11) (WK (invWs.getD j [])) (MInv j) = true :=
  mkA (allN_spec kInv j hj)

theorem inv_w {w : List Nat} {j : Nat} (hj : j < 7) (hw : invWs.getD j [] = w) :
    invEqK 1408 11 (mask 11) (1408 * 11) (WK w) (MInv j) = true := by
  rw [← hw]
  exact (inv_of hj).2

theorem invY : invT 1408 (tabW y0Word) = tabT (unpack 1408 11 (MInv 0)) := by
  rw [wY.1]
  exact invT_unpack (by norm_num) (inv_w (j := 0) (by decide) rfl)

theorem invV : invT 1408 (tabW vWord) = tabT (unpack 1408 11 (MInv 1)) := by
  rw [wV.1]
  exact invT_unpack (by norm_num) (inv_w (j := 1) (by decide) rfl)

theorem invN : invT 1408 (tabW n1Word) = tabT (unpack 1408 11 (MInv 2)) := by
  rw [wN.1]
  exact invT_unpack (by norm_num) (inv_w (j := 2) (by decide) rfl)

theorem memW {w : List Nat} {j : Nat} (hj : j < 5)
    (hw : [i0Word, rho0Word, ck2Word, ck3Word, ck4Word].getD j [] = w) (hl : lettersOK w = true) :
    memT 1408 (subgroupList invCap [y0Word, vWord]) (tabW w) = true := by
  obtain ⟨a, b⟩ := mkA (allN_spec kW j hj)
  rw [recA.2.1, (tabW_eq hl).1]
  refine memT_of (Nat.blt_eq.mp a) ?_
  rw [tblEq_eq (tabW_eq hl).2 (recA.2.2 _ (Nat.blt_eq.mp a)), Nat.eq_of_beq_eq_true b, hw]
  exact Nat.beq_refl _

theorem mkY : primeOrderOK 11 (tabW y0Word) = true := by
  rw [wY.1, primeOrderOK_eq wY.2]
  exact mkAndNot kY

theorem mkV : primeOrderOK 11 (tabW vWord) = true := by
  rw [wV.1, primeOrderOK_eq wV.2]
  exact mkAndNot kV

theorem mkYV : commTT 1408 (tabW y0Word) (tabW vWord) = false := by
  rw [wY.1, wV.1, commTT_eq wY.2 wV.2]
  exact mkNot kYV

theorem mkIY : invOK 1408 (tabW y0Word) (invT 1408 (tabW y0Word)) = true := by
  rw [invY, wY.1]
  exact invOK_unpack wY.2 (inv_of (j := 0) (by decide)).1 (inv_w (j := 0) (by decide) rfl)

theorem mkIV : invOK 1408 (tabW vWord) (invT 1408 (tabW vWord)) = true := by
  rw [invV, wV.1]
  exact invOK_unpack wV.2 (inv_of (j := 1) (by decide)).1 (inv_w (j := 1) (by decide) rfl)

theorem mkRel : m11Relators.all (fun w => tblEq 1408 (relTab (tabW y0Word) (tabW vWord)
    (invT 1408 (tabW y0Word)) (invT 1408 (tabW vWord)) w) (idT 1408)) = true := by
  rw [invY, invV, wY.1, wV.1, List.all_eq_true]
  intro w hw
  obtain ⟨r, hr, hrw⟩ := List.getElem_of_mem hw
  have hr' : r < 2 := hr
  obtain ⟨e, hc⟩ := relTab_eq wY.2 wV.2 (inv_of (j := 0) (by decide)).1
    (inv_of (j := 1) (by decide)).1 w
  rw [e, idT_eq, tblEq_eq hc cId]
  have h := allN_spec kRel r hr'
  rw [List.getD_eq_getElem _ [] hr, hrw] at h
  exact h

theorem mkOrd : ordAllOK (idT 1408) (subgroupList invCap [y0Word, vWord]) = true := by
  rw [recA.2.1]
  unfold ordAllOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < MR1.cnt := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi']
  have h := slAll (L := 990) (K := 8) (by rw [cntA]) (fun s hs => oA_all s hs) i hi'
  simp only [strictB_app] at h
  exact ordK_spec (recA.2.2 i hi') h

theorem mkI : primeOrderOK 2 (tabW i0Word) = true := by
  rw [wI.1, primeOrderOK_eq wI.2]
  exact mkAndNot kI0

theorem mkWin : wordsInOK (subgroupList invCap [y0Word, vWord]) [i0Word] = true := by
  unfold wordsInOK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact memW (j := 0) (by decide) rfl (by decide)

theorem probes_lt : ∀ k < 6, ∀ e ∈ m11Probes.getD k [], e < 6 := by decide

theorem mkJ_spec {J W : Nat} (hJ : Cn J) (h : jK (WK n1Word) (MInv 2) (WK y0Word) J W = true) :
    m11JOK (idT 1408) (tabW n1Word) (invT 1408 (tabW n1Word)) (powsT (tabW y0Word))
      (subgroupList invCap [y0Word, vWord]) (tabT (unpack 1408 11 J)) = true := by
  unfold jK at h
  simp only [strictB_app] at h
  unfold m11JOK
  rcases mkIf h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨a, b⟩ := mkA h
    have hm : memT 1408 (subgroupList invCap [y0Word, vWord]) (tabT (unpack 1408 11 J)) = true := by
      rw [recA.2.1]
      refine memT_of (Nat.blt_eq.mp a) ?_
      rw [tblEq_eq hJ (recA.2.2 _ (Nat.blt_eq.mp a)), Nat.eq_of_beq_eq_true b]
      exact Nat.beq_refl _
    rw [hm]
    simp
  rcases mkIf h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨a, b⟩ := mkA h
    have hI := (inv_of (j := 2) (by decide)).1
    have hC : Cn (pc (pc (WK n1Word) J) (MInv 2)) := canonK_pcomp (canonK_pcomp wN.2 hJ) hI
    have hm : memT 1408 (subgroupList invCap [y0Word, vWord])
        (conjT 1408 (tabW n1Word) (invT 1408 (tabW n1Word)) (tabT (unpack 1408 11 J))) = true := by
      have epc : pcomp 1408 11 (mask 11) (pcomp 1408 11 (mask 11) (WK n1Word) J) (MInv 2) =
          pc (pc (WK n1Word) J) (MInv 2) := rfl
      rw [invN, wN.1, conjT_unpack wN.2 hI hJ, epc, recA.2.1]
      refine memT_of (Nat.blt_eq.mp a) ?_
      rw [tblEq_eq hC (recA.2.2 _ (Nat.blt_eq.mp a)), Nat.eq_of_beq_eq_true b]
      exact Nat.beq_refl _
    rw [hm]
    simp
  obtain ⟨a, b⟩ := mkA h
  have hk : f16 W 1 < 6 := Nat.blt_eq.mp a
  have hp : m11Probes.any (fun p => !ordInS (idT 1408)
      (probeT (powsT (tabW y0Word)) (tabT (unpack 1408 11 J)) p)) = true := by
    rw [List.any_eq_true]
    refine ⟨m11Probes.getD (f16 W 1) [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem _
    · rw [wY.1, ordInS_probe wY.2 hJ (probes_lt _ hk) b]
      rfl
  rw [hp]
  simp

theorem mkN1 : conjEqOK n1Word (tabW y0Word) (powT 1408 7 (tabW y0Word)) = true := by
  rw [wY.1, powT_eq wY.2]
  exact conjEqOK_of (by decide) (inv_of (j := 2) (by decide)).1 (inv_w (j := 2) (by decide) rfl)
    wY.2 (cn_ppK wY.2 7) kN1

theorem mkFive : m11FiveOK (subgroupList invCap [y0Word, vWord]) = true := by
  unfold m11FiveOK
  simp only []
  have hP : primeOrderOK 5 (tabW rho0Word) = true := by
    rw [wR.1, primeOrderOK_eq wR.2]
    exact mkAndNot kR
  have hW : wordsInOK (subgroupList invCap [y0Word, vWord])
      [rho0Word, ck2Word, ck3Word, ck4Word] = true := by
    unfold wordsInOK
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨memW (j := 1) (by decide) rfl (by decide), memW (j := 2) (by decide) rfl (by decide),
      memW (j := 3) (by decide) rfl (by decide), memW (j := 4) (by decide) rfl (by decide)⟩
  have hC2 : conjEqOK ck2Word (tabW rho0Word) (powT 1408 2 (tabW rho0Word)) = true := by
    rw [wR.1, powT_eq wR.2]
    exact conjEqOK_of (by decide) (inv_of (j := 3) (by decide)).1 (inv_w (j := 3) (by decide) rfl)
      wR.2 (cn_ppK wR.2 2) (allN_spec kC 0 (by decide))
  have hC3 : conjEqOK ck3Word (tabW rho0Word) (powT 1408 3 (tabW rho0Word)) = true := by
    rw [wR.1, powT_eq wR.2]
    exact conjEqOK_of (by decide) (inv_of (j := 4) (by decide)).1 (inv_w (j := 4) (by decide) rfl)
      wR.2 (cn_ppK wR.2 3) (allN_spec kC 1 (by decide))
  have hC4 : conjEqOK ck4Word (tabW rho0Word) (powT 1408 4 (tabW rho0Word)) = true := by
    rw [wR.1, powT_eq wR.2]
    exact conjEqOK_of (by decide) (inv_of (j := 5) (by decide)).1 (inv_w (j := 5) (by decide) rfl)
      wR.2 (cn_ppK wR.2 4) (allN_spec kC 2 (by decide))
  have hCB : conjEqOK cBWord (tabW rho0Word) (tabW fix5B.rep) = true := by
    rw [wR.1, wF.1]
    exact conjEqOK_of (by decide) (inv_of (j := 6) (by decide)).1 (inv_w (j := 6) (by decide) rfl)
      wR.2 wF.2 kCB
  rw [wordOK_of (by decide), hP, hW, hC2, hC3, hC4, hCB]
  rfl

end CFSG.KD.HN1408

end
