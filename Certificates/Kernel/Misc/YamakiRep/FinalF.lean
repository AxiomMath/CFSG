module

public import CFSG.Certificates.Kernel.Misc.YamakiRepSound
public import CFSG.Certificates.Kernel.Misc.YamakiRepFSound
public import Certificates.Kernel.Misc.YamakiRep.HeadF
public import Certificates.Kernel.Misc.YamakiRep.ChecksFXN
public import Certificates.Kernel.Misc.YamakiRep.ChecksFH
public import Certificates.Kernel.Misc.YamakiRep.ChecksFE
public import Certificates.Kernel.Misc.YamakiA0.Final

public section

namespace CFSG.KD.YamakiRepF

open CFSG.KC.YamakiRep CFSG.KC.YamakiRepF CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiRep CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.YamakiS0 CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

theorem yf_hdr : ∀ j < 12, RX j = CFSG.KD.YamakiA0.REC j ∧ RN j = CFSG.KD.YamakiA0.REC j ∧
    RH j = CFSG.KD.YamakiA0.REC j ∧ RE j = CFSG.KD.YamakiA0.REC j := by
  decide +kernel

theorem yf_hdrV : ∀ j < 12, RV j = CFSG.KD.YamakiA0.REC j := by
  decide +kernel

theorem yfX_gens (j : Fin 12) : yamakiMat6 j = pkMat 6 (RX j.val) := by
  rw [(yf_hdr j.val j.2).1]
  exact CFSG.KD.YamakiA0.ya0_gens j

theorem yfN_gens (j : Fin 12) : yamakiMat6 j = pkMat 6 (RN j.val) := by
  rw [(yf_hdr j.val j.2).2.1]
  exact CFSG.KD.YamakiA0.ya0_gens j

theorem yfH_gens (j : Fin 12) : yamakiMat6 j = pkMat 6 (RH j.val) := by
  rw [(yf_hdr j.val j.2).2.2.1]
  exact CFSG.KD.YamakiA0.ya0_gens j

theorem yfE_gens (j : Fin 12) : yamakiMat6 j = pkMat 6 (RE j.val) := by
  rw [(yf_hdr j.val j.2).2.2.2]
  exact CFSG.KD.YamakiA0.ya0_gens j

theorem enumX_repF :
    BInvE (fun t => arrN (recX RX 14 t)) (recF RX 14 0) (recF RX 14 1) 1536 (enumX ()) ∧
      enumOK (enumX ()) (gX ()) = true ∧ recX RX 14 0 = ONE ∧
      (∀ i < 1536 - 1, recF RX 14 0 i ≤ i ∧ recF RX 14 1 i < 2 ∧
        recX RX 14 (i + 1) = MULF (recX RX 14 (recF RX 14 0 i)) (RX (12 + recF RX 14 1 i))) ∧
      ∀ t < 1536, recX RX 14 t < 2 ^ 36 :=
  words_inv yfX_gens (ws := gWords) (L := 512) (m := 3) (by decide) rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) yfX_gen yfX_head
    (fun q hq => chunkK_of_chunkF (yfXK.all q hq))

theorem enumN_repF :
    BInvE (fun t => arrN (recX RN 14 t)) (recF RN 14 0) (recF RN 14 1) 10752 (enumN ()) ∧
      enumOK (enumN ()) (gN ()) = true ∧ recX RN 14 0 = ONE ∧
      (∀ i < 10752 - 1, recF RN 14 0 i ≤ i ∧ recF RN 14 1 i < 2 ∧
        recX RN 14 (i + 1) = MULF (recX RN 14 (recF RN 14 0 i)) (RN (12 + recF RN 14 1 i))) ∧
      ∀ t < 10752, recX RN 14 t < 2 ^ 36 :=
  words_inv yfN_gens (ws := nWords) (L := 512) (m := 21) (by decide) rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) yfN_gen yfN_head
    (fun q hq => chunkK_of_chunkF (yfNK.all q hq))

theorem enumH_repF :
    BInvE (fun t => arrN (recX RH 14 t)) (recF RH 14 0) (recF RH 14 1) 23040 (enumH ()) ∧
      enumOK (enumH ()) (gH ()) = true ∧ recX RH 14 0 = ONE ∧
      (∀ i < 23040 - 1, recF RH 14 0 i ≤ i ∧ recF RH 14 1 i < 2 ∧
        recX RH 14 (i + 1) = MULF (recX RH 14 (recF RH 14 0 i)) (RH (12 + recF RH 14 1 i))) ∧
      ∀ t < 23040, recX RH 14 t < 2 ^ 36 :=
  words_inv yfH_gens (ws := hWords) (L := 512) (m := 45) (by decide) rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) yfH_gen yfH_head
    (fun q hq => chunkK_of_chunkF (yfHK.all q hq))

theorem enumE_repF :
    BInvE (fun t => arrN (recX RE 14 t)) (recF RE 14 0) (recF RE 14 1) 11520 (enumE ()) ∧
      enumOK (enumE ()) (gE ()) = true ∧ recX RE 14 0 = ONE ∧
      (∀ i < 11520 - 1, recF RE 14 0 i ≤ i ∧ recF RE 14 1 i < 2 ∧
        recX RE 14 (i + 1) = MULF (recX RE 14 (recF RE 14 0 i)) (RE (12 + recF RE 14 1 i))) ∧
      ∀ t < 11520, recX RE 14 t < 2 ^ 36 :=
  words_inv yfE_gens (ws := e0Words) (L := 512) (m := 23) (by decide) rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) yfE_gen yfE_head
    (fun q hq => chunkK_of_chunkF (yfEK.all q hq))

theorem yfV_gens (j : Fin 12) : yamakiMat6 j = pkMat 6 (RV j.val) := by
  rw [yf_hdrV j.val j.2]
  exact CFSG.KD.YamakiA0.ya0_gens j

theorem enumV0_repF :
    BInvE (fun t => arrN (recX RV 17 t)) (recF RV 17 0) (recF RV 17 1) 32 (enumV0 ()) ∧
      enumOK (enumV0 ()) (gV0 ()) = true ∧ recX RV 17 0 = ONE ∧
      (∀ i < 32 - 1, recF RV 17 0 i ≤ i ∧ recF RV 17 1 i < 5 ∧
        recX RV 17 (i + 1) = MULF (recX RV 17 (recF RV 17 0 i)) (RV (12 + recF RV 17 1 i))) ∧
      ∀ t < 32, recX RV 17 t < 2 ^ 36 :=
  v0_inv yfV_gens yfV_gen yfV_head yfV_tab

end CFSG.KD.YamakiRepF

end
