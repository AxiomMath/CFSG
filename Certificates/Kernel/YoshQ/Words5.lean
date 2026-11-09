module

public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Kernel.YoshQ.Gens
public import Certificates.Data.Kernel.YoshQ.Param
public import CFSG.Certificates.Kernel.YoshQ.ParamSound
public import CFSG.Certificates.Kernel.YoshQ.TwinSound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.KC.Enum CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.Sporadic.Th.Native

set_option maxHeartbeats 0

theorem wordsTrivial_tabN {n w k : Nat} (d : Dims n w) {GS : List Nat} (hk : k ≤ GS.length)
    (ws : List (List (Fin k × Bool))) :
    wordsTrivial n (fun i : Fin k => ((GS.map (tabN n w)).toArray)[i.val]!)
        (fun i : Fin k => (((GS.map (tabN n w)).toArray).map (invT n))[i.val]!) ws =
      ws.all fun wd => eqN n w (modelTN n w k GS wd) (pidn n w) := by
  unfold wordsTrivial
  congr 1
  funext wd
  have h : evalT n (fun i : Fin k => ((GS.map (tabN n w)).toArray)[i.val]!)
      (fun i : Fin k => (((GS.map (tabN n w)).toArray).map (invT n))[i.val]!) wd =
      modelT n k ((GS.map (tabN n w)).toArray) wd := rfl
  rw [h, modelT_tabN d hk, idT_tabN' d, tblEq_tabN' d]

theorem dims24 : Dims 24 5 := ⟨by decide, by decide, by decide, by decide⟩

theorem eT_tabN (wd : List (Fin 6 × Bool)) : eT wd = tabN 16 5 (modelTN 16 5 6 EG.GS wd) := by
  have h : eT wd = modelT 16 6 eGens wd := rfl
  rw [h, (gensOK_spec g_eg.1).1]
  exact modelT_tabN dims16 (by decide) wd

theorem w_wMem : wMemCheck = true := by decide +kernel

theorem w_relNQ00 : relNQCheck 0 0 = true := by
  unfold relNQCheck qInvs
  rw [(gensOK_spec g_q00.1).1, wordsTrivial_tabN dims24 (by decide)]
  decide +kernel

theorem w_relNQ01 : relNQCheck 0 1 = true := by
  unfold relNQCheck qInvs
  rw [(gensOK_spec g_q01.1).1, wordsTrivial_tabN dims24 (by decide)]
  decide +kernel

theorem w_relNQ10 : relNQCheck 1 0 = true := by
  unfold relNQCheck qInvs
  rw [(gensOK_spec g_q10.1).1, wordsTrivial_tabN dims24 (by decide)]
  decide +kernel

theorem w_relNQ11 : relNQCheck 1 1 = true := by
  unfold relNQCheck qInvs
  rw [(gensOK_spec g_q11.1).1, wordsTrivial_tabN dims24 (by decide)]
  decide +kernel

theorem w_fix00 : compFixV 0 0 = true := by
  unfold compFixV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_fix01 : compFixV 0 1 = true := by
  unfold compFixV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_fix10 : compFixV 1 0 = true := by
  unfold compFixV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_fix11 : compFixV 1 1 = true := by
  unfold compFixV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_inner00 : compInnerV 0 0 = true := by
  unfold compInnerV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_inner01 : compInnerV 0 1 = true := by
  unfold compInnerV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_inner10 : compInnerV 1 0 = true := by
  unfold compInnerV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_inner11 : compInnerV 1 1 = true := by
  unfold compInnerV
  simp only [eT_tabN, tblEq_tabN' dims16]
  decide +kernel

theorem w_sigma0 : sigmaQCheck 0 = true := by
  unfold sigmaQCheck qInvs
  rw [(gensOK_spec g_q00.1).1, wordsTrivial_tabN dims24 (by decide)]
  decide +kernel

theorem w_sigma1 : sigmaQCheck 1 = true := by
  unfold sigmaQCheck qInvs
  rw [(gensOK_spec g_q11.1).1, wordsTrivial_tabN dims24 (by decide)]
  decide +kernel

theorem dims14 : Dims 14 5 := ⟨by decide, by decide, by decide, by decide⟩

@[expose] def w5BG : List Nat :=
  [458117738797769787424, 493782837125169872993, 493713099673370101795, 493679254436685382720,
    493815406928340225095]

@[expose] def w5BGI : List Nat :=
  [458117738797769787424, 493639952431031815170, 493713099673370101795, 493819955511134618688,
    493607087687099024488]

@[expose] noncomputable def w5T (wd : List (Fin 5 × Bool)) : Nat :=
  evalN 14 5 (fun i : Fin 5 => w5BG.getD i.val 0) (fun i : Fin 5 => w5BGI.getD i.val 0) wd

theorem baseT_tabN : ∀ i : Fin 5, baseT i = tabN 14 5 (w5BG.getD i.val 0) := by decide +kernel

theorem baseTi_tabN : ∀ i : Fin 5, baseTi i = tabN 14 5 (w5BGI.getD i.val 0) := by
  decide +kernel

theorem tblW_tabN (wd : List (Fin 5 × Bool)) : tblW wd = tabN 14 5 (w5T wd) :=
  evalT_tabN dims14 baseT_tabN baseTi_tabN wd

theorem w_cvN : ((List.range 384).all fun k =>
    !(eqN 14 5 (pmN 14 5 (Y.RL.getD k 0) (w5T wJ)) (pmN 14 5 (w5T wJ) (Y.RL.getD k 0)) &&
      eqN 14 5 (pmN 14 5 (Y.RL.getD k 0) (w5T (wA1 ++ wB1)))
        (pmN 14 5 (w5T (wA1 ++ wB1)) (Y.RL.getD k 0)) &&
      eqN 14 5 (pmN 14 5 (Y.RL.getD k 0) (w5T (wA2 ++ wB2)))
        (pmN 14 5 (w5T (wA2 ++ wB2)) (Y.RL.getD k 0)) &&
      eqN 14 5 (pmN 14 5 (Y.RL.getD k 0) (w5T wE)) (pmN 14 5 (w5T wE) (Y.RL.getD k 0))) ||
      (List.range 16).any fun m => eqN 14 5 (Y.RL.getD k 0) (w5T (vWord14 m))) = true := by
  decide +kernel

theorem w_cv : cvCheckOn ((Y.RL.map (tabN 14 5)).toArray) = true := by
  have hl : Y.RL.length = 384 := by decide +kernel
  unfold cvCheckOn
  rw [List.all_eq_true]
  intro k hk
  have h := List.all_eq_true.1 w_cvN k hk
  have hk' : k < Y.RL.length := by
    rw [hl]
    exact List.mem_range.1 hk
  rw [getElem!_map_tabN hk']
  simp only [commT, tblW_tabN, compT_tabN' dims14, tblEq_tabN' dims14]
  exact h

theorem w_sAct : sActOK = true := by
  unfold sActOK
  simp only [tblW_tabN, idT_tabN' dims14, tblEq_tabN' dims14]
  decide +kernel

theorem w_kWords : (kWords.all fun w => commT (tblW w) (tblW wJ)) = true := by
  simp only [commT, tblW_tabN, compT_tabN' dims14, tblEq_tabN' dims14]
  decide +kernel

end CertificateChecks.KernelYoshQ

end
