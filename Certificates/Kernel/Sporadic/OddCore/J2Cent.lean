module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
meta import CFSG.Sporadic.SmallOddCore.J2DataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.J2CentT CFSG.Sporadic.SmallOddCore.j2CentHex

#kmisc_hexflat CertificateChecks.KernelSpor.J2CentT CFSG.Sporadic.SmallOddCore.j2CentHex 3 315 9 42

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def j2CentInvM : Array (Array Nat) :=
  (List.range 42).toArray.map fun k =>
    CFSG.Monster.B.Co2.Native.invCand 315 (natArr (j2CentTbl k))

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.J2CentI CertificateChecks.KernelSpor.OddCore.j2CentInvM 9

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.KS.Raw CFSG.KC.Enum
open CFSG.KS CFSG.KS.Prim

theorem j2_perms : allN 42 (fun k =>
    invEqK 315 9 (mask 9) (315 * 9) (J2CentT.F k) (J2CentI k)) = true := by
  quickRfl

theorem j2CentTbl_eq {k : Nat} (hk : k < 42) :
    natArr (j2CentTbl k) = unpack 315 9 (J2CentT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound J2CentT.all (by norm_num) k hk
  rw [← J2CentT.eq] at h
  exact h

theorem j2_permOK_all : (List.range 42).all
    (fun k => CFSG.Sporadic.SmallOddCore.permOK 315 (j2CentTbl k)) = true := by
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 42 := List.mem_range.1 hk
  obtain ⟨h1, h2⟩ := invEqK_sound (allN_spec j2_perms k hk')
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [j2CentTbl_eq hk', h1]
  exact h2

end CertificateChecks.KernelSpor.OddCore

end
