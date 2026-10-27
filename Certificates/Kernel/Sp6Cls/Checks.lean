module

public import Certificates.Data.Kernel.Sp6ClsK
public import Certificates.Data.FF81Sp6Cls
public import Certificates.Kernel.Sp6A2.Rec
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6Cls

open CFSG.KD.Sp62 CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls

@[expose] noncomputable def T0P : Nat := MULF (MULF (pk hInv) (CFSG.KD.Sp6Two.REC 25)) (pk hCode)

theorem ch899111_c7 : c7K CFSG.KD.Sp6A2.REC 5705 648 CFSG.KD.Sp6Two.REC 29 63 = true := by
  quickRfl

theorem ch899111_syl : sylK CFSG.KD.Sp6Two.REC 34728 512 (at2 CFSG.KD.Sp6Two.REC 16) 5 T0P
    CFSG.KD.Sp6Two.REC 29 63 = true := by
  quickRfl

end CFSG.KD.Sp6Cls
