module

public import Certificates.Kernel.HN1408.TfChk
public import Certificates.Kernel.HN1408.A8Glue
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.Native

theorem tf_hkg : ∀ w ∈ classz₁.centGens, lettersOK w = true := by decide

theorem tf_hkr : ∀ w ∈ classz₁.centGens.map List.reverse, lettersOK w = true := by decide

theorem tf_len : classz₁.centGens.length = 2 := rfl

theorem tfHd {r : Nat} (h : tfOne r = true) :
    ∀ j < classz₁.centGens.length, fOf TfO.G TfO.ts r j = WK (classz₁.centGens.getD j []) ∧
      Cn (fOf TfO.GI TfO.ts r j) ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (fOf TfO.G TfO.ts r j) (fOf TfO.GI TfO.ts r j) = true := by
  unfold tfOne at h
  simp only [strictB_app, bAnd_iff] at h
  intro j hj
  have := allN_spec h.1 j (by rw [tf_len] at hj; exact hj)
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, this.2.1, this.2.2⟩

theorem tfOrb_of {r : Nat} (hr : tfOne r = true) :
    orbGenOK tfCap classz₁.centGens 16 (tabT (unpack 1408 11 (TI4.T (r + 1)))) = true := by
  have hOG := tfHd hr
  unfold tfOne at hr
  simp only [strictB_app, bAnd_iff] at hr
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have tO : TabsOK 1408 11 classz₁.centGens.length (fOf TfO.G TfO.ts r) (p0Tabs classz₁.centGens) :=
    tabsW_tabs tf_hkg fun j hj => (hOG j hj).1
  have tOI : TabsOK 1408 11 classz₁.centGens.length (fOf TfO.GI TfO.ts r)
      (p0Invs classz₁.centGens) :=
    TabsOK_inv tO fun j hj => ⟨(hOG j hj).2.2, (hOG j hj).2.1⟩
  rw [Nat.eq_of_beq_eq_true h2] at h3
  have hOp : ∀ i < TfO.cnt r, penumPtK 1408 11 (mask 11) (1408 * 11) true (fOf TfO.G TfO.ts r)
      (fOf TfO.GI TfO.ts r) classz₁.centGens.length (TfO.cnt r) (fOf TfO.T TfO.ts r)
      (fOf TfO.PL TfO.rr r) (fOf TfO.POS TfO.pr r) (fOf TfO.SRT TfO.rr r) (fOf TfO.SRI TfO.rr r) i =
        true :=
    fun i hi => penumSl_spec h4 i (Nat.zero_le _) (by omega) hi
  obtain ⟨eO, tOk, dO⟩ := conjH_sound (X := TI4.T (r + 1))
    (x := tabT (unpack 1408 11 (TI4.T (r + 1)))) hn tO tOI rfl h3 hOp
    (fun i hi => slK_spec h5 i (Nat.zero_le _) (by omega) hi)
  have cT : ∀ i < TfO.cnt r, Cn (fOf TfO.T TfO.ts r i) := fun i hi => penumPt_canon (hOp i hi)
  have eGI : ∀ j < TfO.cnt r, fOf TfS.GI TfS.ts r j = fOf TfO.T TfO.ts r j ∧
      fOf TfS.G TfS.ts r j = idK := by
    intro j hj
    have := allN_spec h6 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.2, Nat.eq_of_beq_eq_true this.1⟩
  have tS : TabsOK 1408 11 (TfO.cnt r) (fOf TfS.GI TfS.ts r)
      (hRec 1408 11 (TfO.cnt r) (fOf TfO.T TfO.ts r) (fOf TfO.PL TfO.rr r)).1 := by
    refine ⟨hRec_size _ _ _ _ _, fun j hj => ?_⟩
    rw [hRec_get hj, (eGI j hj).1]
    exact ⟨rfl, cT j hj⟩
  obtain ⟨eS, tSk, dS⟩ := mulH_sound hn (fun j hj => (eGI j hj).2) tS h8
    (fun i hi => penumSl_spec h9 i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec h10 i (Nat.zero_le _) (by omega) hi)
  rw [show tfCap = 100 from rfl]
  dsimp only [orbGenOK]
  rw [eO, eS, tOk, tSk, dS, hRec_size, Nat.eq_of_beq_eq_true h7]
  simp

theorem twoFourOK_true : twoFourOK = true := by
  have hOG := tfHd (allN_spec tfkOne 0 (by omega))
  have cO : ∀ j < classz₁.centGens.length, Cn (fOf TfO.G TfO.ts 0 j) := fun j hj => by
    rw [(hOG j hj).1]
    exact cn_WK (lettersOK_getD tf_hkg j)
  have aW : classz₁.centGens.all wordOK = true := by
    rw [List.all_eq_true]
    exact fun w hw => wordOK_of (tf_hkg w hw)
  have aI : classz₁.centGens.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) = true :=
    allW (f := fun t => invOK 1408 t (invT 1408 t)) rfl (fun j hj => (hOG j hj).1) tf_hkg
      fun j hj => by
        change invOK 1408 _ (invT 1408 _) = true
        rw [invT_unpack (by norm_num) (hOG j hj).2.2]
        exact invOK_unpack (cO j hj) (hOG j hj).2.1 (hOG j hj).2.2
  have aS : (tfComm.map (fun p => p.2.2) == sSpec3) = true := by decide
  have aC : tfComm.all (fun p => commutatorEqOK (tabW (specWord classz₁.centGens p.1))
      (tabW (specWord classz₁.centGens p.2.1)) (tabW (specWord classz₁.centGens p.2.2))) = true := by
    rw [List.all_eq_true]
    intro p hp
    have h := List.all_eq_true.1 tfkComm p hp
    unfold tfCommK at h
    simp only [strictB_app, bAnd_iff] at h
    rw [(tabW_eq (lettersOK_specWord tf_hkg p.1)).1, (tabW_eq (lettersOK_specWord tf_hkg p.2.1)).1,
      (tabW_eq (lettersOK_specWord tf_hkg p.2.2)).1, WK_specWord tf_hkg, WK_specWord tf_hkg,
      WK_specWord tf_hkg]
    exact commEq_of (cn_specK tf_hkg _) (cn_specK tf_hkg _) (cn_specK tf_hkr _)
      (cn_specK tf_hkr _) (cn_specK tf_hkg _) h.1 h.2.1 h.2.2
  obtain ⟨-, f2, hT4⟩ := r4
  obtain ⟨-, -, hc4, hh4⟩ := kH4spec
  have e0 : TI4.T 0 = idK := by
    unfold penumHdK at hh4
    simp only [bAnd_iff] at hh4
    exact Nat.eq_of_beq_eq_true hh4.2.2.1
  have aN : (hRec 1408 11 TI4.cnt TI4.T TI4.PL).1.all (fun t => tblEq 1408 t (idT 1408) ||
      orbGenOK tfCap classz₁.centGens 16 t) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < TI4.cnt := by simpa [hRec] using hi
    rw [← getElem!_pos _ i hi, hRec_get hi']
    match i, hi' with
    | 0, _ =>
      rw [idT_eq, e0, tblEq_self cId]
      rfl
    | r + 1, hr =>
      rw [tfOrb_of (allN_spec tfkOne r (by omega)), Bool.or_true]
  unfold twoFourOK
  simp only []
  rw [gensOK_true, aW, aI, aS, aC, f2, aN]
  rfl

end CFSG.KD.HN1408

end
