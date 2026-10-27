module

public import Certificates.Kernel.Q8Wit.M22Data
public import Certificates.Data.Kernel.Q8Wit
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit Certificates.TwinPerpSmSp1

@[expose] noncomputable def SK : List Nat := (List.range 256).map Q.SKT

theorem hw : szOK 24 5 = true := by quickRfl

theorem keys : keysSK 24 5 m22Wit.syl.qKeys Q.N Q.T SK = true := by quickRfl

theorem bindPG : (Nat.beq m22Wit.syl.pg.size 4 &&
    CFSG.KC.Enum.allN 4 fun k => bindArrK m22Wit.syl.pg[k]! 24 5 (PG k)) = true := by
  decide +kernel

theorem bindXG : (Nat.beq m22Wit.xg.size 4 &&
    CFSG.KC.Enum.allN 4 fun k => bindArrK m22Wit.xg[k]! 24 5 (XG k)) = true := by
  decide +kernel

theorem permPG : CFSG.KC.Enum.allN 4 (fun j => permB 24 5 (PG j)) = true := by quickRfl

theorem permXG : CFSG.KC.Enum.allN 4 (fun j => permB 24 5 (XG j)) = true := by quickRfl

theorem lettersQ : (m22Wit.syl.qW.toList.all fun wd => wd.all fun l => decide (l < 4)) = true := by
  decide +kernel

theorem lettersC : (m22Wit.cW.toList.all fun wd => wd.all fun l => decide (l < 4)) = true := by
  decide +kernel

theorem wordsQ : m22Wit.syl.qW.toList.map (posWordK 24 5 PG) = (List.range Q.ng).map Q.G := by
  decide +kernel

theorem wordsC : m22Wit.cW.toList.map (posWordK 24 5 XG) = (List.range nc).map C := by
  decide +kernel

theorem tabs : tabsK 24 5 Q.N Q.T SQ I = true := by quickRfl

theorem invs : invsK 24 5 nc C CI = true := by quickRfl

theorem free : q8WitFreeK 24 5 Q.N Q.T SQ I nc C CI = true := by quickRfl

end CertificateChecks.KernelQ8W.M22

end
