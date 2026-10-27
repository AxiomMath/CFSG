module

public import Certificates.Kernel.Sporadic.Co3.Bind
meta import CFSG.Sporadic.Schreier.Co3Arrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSpor.Co3Z 9 CFSG.Sporadic.Schreier.Co3.co3ZArr

#ks_perm CertificateChecks.KernelSpor.Co3Tt 9 CFSG.Sporadic.Schreier.Co3.co3TtArr

namespace CertificateChecks.KernelSpor.Co3Single

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3

theorem z_line : allN 1 (fun j => Nat.beq Co3Z (Co3Text.L (Nat.add 28 j))) = true := by quickRfl

theorem tt_line : allN 1 (fun j => Nat.beq Co3Tt (Co3Text.L (Nat.add 29 j))) = true := by quickRfl

theorem z_eq : co3ZArr = unpack 276 9 Co3Z :=
  (Co3Text.field_of (f := 2) (F := fun _ => Co3Z) rfl (by omega) z_line).2 0 (by omega)

theorem tt_eq : co3TtArr = unpack 276 9 Co3Tt :=
  (Co3Text.field_of (f := 3) (F := fun _ => Co3Tt) rfl (by omega) tt_line).2 0 (by omega)

end CertificateChecks.KernelSpor.Co3Single

end
