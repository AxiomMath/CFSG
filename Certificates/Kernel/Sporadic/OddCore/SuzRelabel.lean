module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.RowSound
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays
import all CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzRelT CFSG.Sporadic.SuzOddCore.relabelText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRelT CFSG.Sporadic.SuzOddCore.relabelText 4 32 15 715

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def relInvRowsM : Array (Array Nat) :=
  let t := CFSG.Monster.B.Co2.Native.invCand 22880 relabelArr
  (List.range 715).toArray.map fun j => t.extract (32 * j) (32 * j + 32)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzRelI CertificateChecks.KernelSpor.OddCore.relInvRowsM 15

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row

theorem relabelArr_eq : relabelArr = rowArr 22880 15 SuzRelT.F 0 := by
  have h := hexTable_rows (d := 4) (w := 15) (N := 715) (r := 715) (k := 0) SuzRelT.all
    (by omega)
  rw [← SuzRelT.eq] at h
  exact h

theorem relabel_perm : rpermK 22880 15 (mask 15) SuzRelT.F 0 SuzRelI 0 = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
