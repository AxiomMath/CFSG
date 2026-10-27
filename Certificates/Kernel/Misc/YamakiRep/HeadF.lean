module

public import Certificates.Data.Kernel.Misc.YamakiRep
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Data.Sp62RecCR1CE
public import Certificates.Data.YamakiTables
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiRepF

open CFSG.KD.YamakiRep CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec

theorem yfX_gen : genWK RX 12 gWords = true := by quickRfl

theorem yfX_head : headK RX 14 1536 2 = true := by quickRfl

theorem yfN_gen : genWK RN 12 nWords = true := by quickRfl

theorem yfN_head : headK RN 14 10752 2 = true := by quickRfl

theorem yfH_gen : genWK RH 12 hWords = true := by quickRfl

theorem yfH_head : headK RH 14 23040 2 = true := by quickRfl

theorem yfE_gen : genWK RE 12 e0Words = true := by quickRfl

theorem yfE_head : headK RE 14 11520 2 = true := by quickRfl

theorem yfV_gen : genIK RV 12 v0Idx = true := by quickRfl

theorem yfV_head : headK RV 17 32 5 = true := by quickRfl

theorem yfV_tab : chunkK RV (rstG RV 12) 17 32 5 32 0 = true := by quickRfl

end CFSG.KD.YamakiRepF

end
