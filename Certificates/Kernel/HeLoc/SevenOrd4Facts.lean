module

public import Certificates.Kernel.HeLoc.SevenOrd4
public import Certificates.Kernel.HeLoc.SevenBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.OrderFour
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartOne

theorem szOK8330 : szOK 8330 14 = true := by decide +kernel

theorem permB67 : permB 8330 14 (A 67) = true :=
  permB_of_pp (pp_of_permOK szOK8330 (perm_k 67 (by norm_num)))

theorem orderFour : CFSG.HardMathSupport.Dickson.I271.orderFourOK 8330 heSevenC1Gens[2]! = true := by
  have e : heSevenC1Gens[2]! = unpack 8330 14 (A 67) := by
    rw [heSevenC1Gens]
    exact (lit3_2 _ _ _).trans (arr_eq 67 (by norm_num))
  have hid : permB 8330 14 (pidn 8330 14) = true :=
    permB_of_pp (CFSG.KC.BfsPin.PP.id szOK8330)
  rw [e, CFSG.HardMathSupport.Dickson.I271.orderFourOK, CFSG.KC.BfsPin.validA_unpack permB67,
    pow_unpack szOK8330 permB67, pow_unpack szOK8330 permB67, CFSG.KC.BfsPin.idA_eq szOK8330,
    eqA_unpack szOK8330 (permB_ppow szOK8330 permB67 4) hid,
    eqA_unpack szOK8330 (permB_ppow szOK8330 permB67 2) hid, ord4, ord2]
  rfl

end CertificateChecks.KernelHeLoc.Seven

end
