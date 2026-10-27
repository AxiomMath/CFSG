module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.RowSound
public import CFSG.Sporadic.SuzOddCore.GraphArrays
meta import CFSG.Sporadic.SuzOddCore.GraphArrays
import all CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzOutT CFSG.Sporadic.SuzOddCore.graphOuterText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzOutT CFSG.Sporadic.SuzOddCore.graphOuterText 4 32 15 715

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def outInvRowsM : Array (Array Nat) :=
  let t := CFSG.Monster.B.Co2.Native.invCand 22880 outerArr
  (List.range 715).toArray.map fun j => t.extract (32 * j) (32 * j + 32)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzOutI CertificateChecks.KernelSpor.OddCore.outInvRowsM 15

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row

theorem outerArr_eq : outerArr = rowArr 22880 15 SuzOutT.F 0 := by
  have h := hexTable_rows (d := 4) (w := 15) (N := 715) (r := 715) (k := 0) SuzOutT.all
    (by omega)
  rw [← SuzOutT.eq] at h
  exact h

theorem outer_perm : rpermK 22880 15 (mask 15) SuzOutT.F 0 SuzOutI 0 = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
