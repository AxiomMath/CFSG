module

public import Certificates.Kernel.Misc.YamakiRep.FinalF
public import Certificates.Kernel.Misc.YamakiCE.Checks
public import Certificates.Kernel.Misc.YamakiCE.ChecksCent
public import CFSG.Certificates.Kernel.Misc.YamakiE64Sound
public import Certificates.Kernel.Misc.YamakiCE.ChecksE64
public import CFSG.Certificates.Kernel.Misc.YamakiA6NSound
public import Certificates.Kernel.Misc.YamakiCE.ChecksA6N

public section

namespace CFSG.KD.YamakiCE

open CFSG.ClassicalInvolution.Sp62Rec CFSG.KC.YamakiCE CFSG.KD.YamakiRepF CFSG.KD.YamakiRep
  CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KC.YamakiRep CFSG.KC.YamakiRepF CFSG.KD.BfsK
  CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.KD.Sp62 (MULF ONE)

theorem ce550823_hV5 : RV 5 < 2 ^ 36 :=
  Nat.blt_eq.mp (List.all_eq_true.1 ch550823bV 5 (List.mem_range.2 (by norm_num)))

theorem ce550823_hH5 : RH 5 < 2 ^ 36 :=
  Nat.blt_eq.mp (List.all_eq_true.1 ch550823bH 5 (List.mem_range.2 (by norm_num)))

theorem ceEnumCheck_holds : ceEnumCheck () = true :=
  ceEnumCheck_of ⟨enumE_repF.2.1, enumE_repF.1.1⟩ ⟨enumV0_repF.2.1, enumV0_repF.1.1⟩

theorem v0Check_holds : v0Check () = true :=
  v0Check_of enumE_repF.1 enumV0_repF.1 yfE_gens yfV_gens ch550823pV ch550823sq ch550823cj

theorem centE0Check_holds : centE0Check () = true :=
  centE0Check_of enumH_repF.1 yfH_gens enumH_repF.2.2.2.2 ce550823_hH5 ce550823cK.all

theorem commCheck_holds : commCheck () = true :=
  commCheck_of enumE_repF.1 enumV0_repF.1 yfE_gens yfV_gens enumV0_repF.2.2.2.2 ce550823_hV5
    ch550823pW ch550823gk ch550823fx ch550823tr ch550823ex

theorem e64Check_holds : e64Check () = true := by
  have hS := enumS0_inv CFSG.KD.YamakiS0.ys0_gens CFSG.KD.YamakiS0.ys0_tab_ok
  have hA := enumA0_inv CFSG.KD.YamakiA0.ya0_gens CFSG.KD.YamakiA0.ya0_tab_ok
  exact CFSG.KC.YamakiE64.e64Check_of hS.1 hA.1 hS.2.2 CFSG.KD.YamakiE64.ce550823eK.all

theorem a6Check_holds : a6Check () = true := by
  have rows := rows_of_chunks (L := 512) (m := 23)
    (fun q hq => chunkK_of_chunkF (yfEK.all q hq)) (by norm_num)
  have hstep : ∀ i < 11520 * 2, recPOS RE 14 2 i < 11520 ∧
      recX RE 14 (recPOS RE 14 2 i) = MULF (recX RE 14 (i / 2)) (RE (12 + i % 2)) := by
    intro i hi
    have s := stepAt_facts (step_of_rows (by norm_num) (by norm_num) rows i hi)
    exact ⟨s.2.2.1, s.2.2.2.1⟩
  have hg : ∀ j < 2, (gE ())[j]! = arrN (RE (12 + j)) := by
    intro j hj
    rw [gE, wordsA_get _ _ (by simpa [e0Words] using hj),
      words_gen yfE_gens e0Words 12 (by decide) yfE_gen j (by simpa [e0Words] using hj)]
  exact CFSG.KC.YamakiA6.a6Check_ofN enumE_repF.1
    (fun i hi => ⟨(enumE_repF.2.2.2.1 i hi).1, (enumE_repF.2.2.2.1 i hi).2.1⟩)
    enumE_repF.2.2.2.2 hstep hg enumV0_repF.1 enumV0_repF.2.2.2.2 CFSG.KD.YamakiA6.ce550823bK.all
    CFSG.KD.YamakiA6.ce550823bV

end CFSG.KD.YamakiCE

end
