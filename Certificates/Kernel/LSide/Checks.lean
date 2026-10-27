module

public import Certificates.Data.Kernel.LSideK
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LSide

open CFSG.KD.Sp62 CFSG.KD.Sp6A2
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData

theorem ch799750_adm : admK CFSG.KD.Sp62.REC 6521 108 (pk (zCode 2))
    (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 1 2 0)
    (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 2 1 0)
    (sigK (pk (zCode 0)) (pk lsSig) 0) (sigK (pk (zCode 0)) (pk lsSig) 1)
    (sigK (pk (zCode 0)) (pk lsSig) 2) = true := by
  quickRfl

theorem ch799750_c1 : Nat.beq (cntK CFSG.KD.Sp62.REC 6630 108 (pk lsSig) 2) 36 = true := by
  quickRfl

theorem ch799750_c2 :
    Nat.beq (cnt3K CFSG.KD.Sp62.REC 6630 108 (pk lsSig) (pk (zCode 2)) (pk lsX2p) 2) 6 = true := by
  quickRfl

theorem ch799750_frame : frameCheckK = true := by decide +kernel

end CFSG.KD.LSide
