module

public import Certificates.Data.Kernel.J2H2.Defs
public import Certificates.Kernel.J2H2.Data
public import Certificates.Data.J2H2Sylow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.J2H2

open CFSG.KC.Enum CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue

@[expose] noncomputable def cocBlk (lo : Nat) : Bool :=
  strictB (rowsPack HR) (fun HP => strictB repN (fun REP =>
    allN 32 (fun i => rowOKf HP REP LMP MTP SP (Nat.add lo i))))

theorem coc0 : cocBlk 0 = true := by quickRfl
theorem coc32 : cocBlk 32 = true := by quickRfl
theorem coc64 : cocBlk 64 = true := by quickRfl
theorem coc96 : cocBlk 96 = true := by quickRfl
theorem coc128 : cocBlk 128 = true := by quickRfl
theorem coc160 : cocBlk 160 = true := by quickRfl
theorem coc192 : cocBlk 192 = true := by quickRfl
theorem coc224 : cocBlk 224 = true := by quickRfl
theorem coc256 : cocBlk 256 = true := by quickRfl
theorem coc288 : cocBlk 288 = true := by quickRfl
theorem coc320 : cocBlk 320 = true := by quickRfl
theorem coc352 : cocBlk 352 = true := by quickRfl

theorem normOK : strictB (rowsPack HR) normK = true := by quickRfl

theorem treeOK : strictB (rowsPack HR) (fun HP => treeK HP GP PP) = true := by quickRfl

theorem freeOK : strictB (rowsPack HR) (fun HP => freeK HP H2S.h2Free) = true := by quickRfl

theorem dataOK : dataK GP PP LMP genT parT lT = true := by quickRfl

theorem mtOK : mtK MTP LMP GP PP = true := by quickRfl

theorem spyOK : spyK SP C4725.aCols C4725.bCols yWords = true := by quickRfl

end CFSG.KD.J2H2

end
