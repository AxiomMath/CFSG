module

public import Certificates.Kernel.Q8Wit.J2Data
public import Certificates.Data.Kernel.Q8Wit
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit Certificates.TwinPerpSmSp1

@[expose] noncomputable def SK : List Nat := (List.range 256).map Q.SKT

theorem hw : szOK 315 9 = true := by quickRfl

theorem keys : keysSK 315 9 j2Wit.syl.qKeys Q.N Q.T SK = true := by quickRfl

theorem bindPG : (Nat.beq CFSG.ComponentClassification.J2Cover.sylowStrong.size 5 &&
    CFSG.KC.Enum.allN 3 fun k =>
      bindArrK CFSG.ComponentClassification.J2Cover.sylowStrong[k]! 315 9 (PG k)) = true := by
  decide +kernel

theorem bindXG : (Nat.beq j2Wit.xg.size 2 &&
    CFSG.KC.Enum.allN 2 fun k => bindArrK j2Wit.xg[k]! 315 9 (XG k)) = true := by
  decide +kernel

theorem permPG : CFSG.KC.Enum.allN 3 (fun j => permB 315 9 (PG j)) = true := by quickRfl

theorem permXG : CFSG.KC.Enum.allN 2 (fun j => permB 315 9 (XG j)) = true := by quickRfl

theorem lettersQ : (j2Wit.syl.qW.toList.all fun wd => wd.all fun l => decide (l < 3)) = true := by
  decide +kernel

theorem lettersC : (j2Wit.cW.toList.all fun wd => wd.all fun l => decide (l < 2)) = true := by
  decide +kernel

theorem wordsQ : j2Wit.syl.qW.toList.map (posWordK 315 9 PG) = (List.range Q.ng).map Q.G := by
  decide +kernel

theorem wordsC : j2Wit.cW.toList.map (posWordK 315 9 XG) = (List.range nc).map C := by
  decide +kernel

theorem tabs : tabsK 315 9 Q.N Q.T SQ I = true := by quickRfl

theorem invs : invsK 315 9 nc C CI = true := by quickRfl

theorem free : q8WitFreeK 315 9 Q.N Q.T SQ I nc C CI = true := by quickRfl

end CertificateChecks.KernelQ8W.J2

end
