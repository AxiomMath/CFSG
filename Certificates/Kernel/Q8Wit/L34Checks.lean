module

public import Certificates.Kernel.Q8Wit.L34Data
public import Certificates.Data.Kernel.Q8Wit
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.L34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit Certificates.TwinPerpSmSp1

@[expose] noncomputable def SK : List Nat := (List.range 256).map Q.SKT

theorem hw : szOK 42 6 = true := by quickRfl

theorem keys : keysSK 42 6 l34Wit.syl.qKeys Q.N Q.T SK = true := by quickRfl

theorem bindPG : (Nat.beq l34Wit.syl.pg.size 6 &&
    CFSG.KC.Enum.allN 6 fun k => bindArrK l34Wit.syl.pg[k]! 42 6 (PG k)) = true := by
  decide +kernel

theorem bindXG : (Nat.beq l34Wit.xg.size 3 &&
    CFSG.KC.Enum.allN 3 fun k => bindArrK l34Wit.xg[k]! 42 6 (XG k)) = true := by
  decide +kernel

theorem permPG : CFSG.KC.Enum.allN 6 (fun j => permB 42 6 (PG j)) = true := by quickRfl

theorem permXG : CFSG.KC.Enum.allN 3 (fun j => permB 42 6 (XG j)) = true := by quickRfl

theorem lettersQ : (l34Wit.syl.qW.toList.all fun wd => wd.all fun l => decide (l < 6)) = true := by
  decide +kernel

theorem lettersC : (l34Wit.cW.toList.all fun wd => wd.all fun l => decide (l < 3)) = true := by
  decide +kernel

theorem wordsQ : l34Wit.syl.qW.toList.map (posWordK 42 6 PG) = (List.range Q.ng).map Q.G := by
  decide +kernel

theorem wordsC : l34Wit.cW.toList.map (posWordK 42 6 XG) = (List.range nc).map C := by
  decide +kernel

theorem tabs : tabsK 42 6 Q.N Q.T SQ I = true := by quickRfl

theorem invs : invsK 42 6 nc C CI = true := by quickRfl

theorem free : q8WitFreeK 42 6 Q.N Q.T SQ I nc C CI = true := by quickRfl

end CertificateChecks.KernelQ8W.L34

end
