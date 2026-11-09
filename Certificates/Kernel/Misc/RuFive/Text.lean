module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.PartOne.KS.RuFiveData
meta import CFSG.RankThree.PartOne.KS.RuFiveData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Misc.HexFlatRows
import Certificates.Kernel.Misc.Perm.HexTabCmd

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.RuFive.RG CFSG.RankThree.PartOne.ruFiveHex
#kmisc_hexflat_tab CertificateChecks.KernelMisc.RuFive.RG CFSG.RankThree.PartOne.ruFiveHex 3 4060 12 75

namespace CertificateChecks.KernelMisc.RuFive.RG

open CFSG.KC.Misc.HexFlat

theorem p0 :
    CFSG.KC.Misc.HexFlat.run 3 4060 12 13 F (dropL 0 (dropL 0 chars)) 0 0 0 0 0 =
      true := by quickRfl
theorem p1 :
    CFSG.KC.Misc.HexFlat.run 3 4060 12 26 F (dropL 158340 (dropL 0 chars)) 13 0 0 0 0 =
      true := by quickRfl
theorem p2 :
    CFSG.KC.Misc.HexFlat.run 3 4060 12 39 F (dropL 316680 (dropL 0 chars)) 26 0 0 0 0 =
      true := by quickRfl
theorem p3 :
    CFSG.KC.Misc.HexFlat.run 3 4060 12 52 F (dropL 75021 (dropL 399999 chars)) 39 0 0 0 0 =
      true := by quickRfl
theorem p4 :
    CFSG.KC.Misc.HexFlat.run 3 4060 12 65 F (dropL 233361 (dropL 399999 chars)) 52 0 0 0 0 =
      true := by quickRfl
theorem p5 :
    CFSG.KC.Misc.HexFlat.run 3 4060 12 75 F (dropL 391701 (dropL 399999 chars)) 65 0 0 0 0 =
      true := by quickRfl

theorem rows : RowsD chars 3 4060 12 F 0 75 :=
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p0) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p1) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p2) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p3) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p4) <|
  (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p5)

end CertificateChecks.KernelMisc.RuFive.RG

end
