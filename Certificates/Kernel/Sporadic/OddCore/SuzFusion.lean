module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzFusT CFSG.Sporadic.SuzOddCore.invFusionText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzFusT CFSG.Sporadic.SuzOddCore.invFusionText
  3 1782 11 53

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def fusInvM : Array (Array Nat) :=
  (List.range 53).toArray.map fun k => CFSG.Monster.B.Co2.Native.invCand 1782 (invFusionRun k)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzFusI CertificateChecks.KernelSpor.OddCore.fusInvM 11

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem fusionRun_eq {k : Nat} (hk : k < 53) :
    invFusionRun k = unpack 1782 11 (SuzFusT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzFusT.all k hk
  rw [← SuzFusT.eq] at h
  exact h

theorem fus_perms : allN 53 (fun k =>
    invEqK 1782 11 (mask 11) (1782 * 11) (SuzFusT.F k) (SuzFusI k)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
