module

public import Certificates.Data.Kernel.G2Three.Insp
public import Certificates.Data.S7G23Insp
public import Certificates.Kernel.G2Three.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open Certificates.S7G23Insp

theorem insp0_ok : c0K XS (XO 0) k1s k2s = true := by quickRfl

theorem insp1_ok : c1K XS k1s k2s = true := by quickRfl

theorem insp2_ok : c2K XS ((List.range 5).map GX) k1s k2s = true := by quickRfl

theorem insp3_ok : c3K XS ((List.range 576).map XX) (inspWord GA) (inspWordInv GA) = true := by
  quickRfl

theorem insp4_ok : c4K (GA 0) (GA 2) (GX 2) (GX 3) (inspWord GA) (inspWordInv GA) = true := by
  quickRfl

end CFSG.KD.G2Three

end
