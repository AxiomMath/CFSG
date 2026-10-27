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

#ks_chars CertificateChecks.KernelSpor.SuzCertT CFSG.Sporadic.SuzOddCore.certChainText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzCertT CFSG.Sporadic.SuzOddCore.certChainText
  4 32 15 8580

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def rowsOf (r : Nat) (t : Array Nat) : Array (Array Nat) :=
  (List.range r).toArray.map fun j => t.extract (32 * j) (32 * j + 32)

meta def certInvRowsM : Array (Array Nat) :=
  ((List.range 12).toArray.map fun k =>
    rowsOf 715 (CFSG.Monster.B.Co2.Native.invCand 22880 (certArr k))).flatten

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCertI CertificateChecks.KernelSpor.OddCore.certInvRowsM
  15

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row

theorem certArr_eq {k : Nat} (hk : k < 12) : certArr k = rowArr 22880 15 SuzCertT.F (715 * k) := by
  have h := hexTable_rows (d := 4) (w := 15) (N := 8580) (r := 715) (k := k) SuzCertT.all
    (by omega)
  rw [← SuzCertT.eq] at h
  exact h

theorem cert_perms : allN 12 (fun k =>
    rpermK 22880 15 (mask 15) SuzCertT.F (Nat.mul 715 k) SuzCertI (Nat.mul 715 k)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
