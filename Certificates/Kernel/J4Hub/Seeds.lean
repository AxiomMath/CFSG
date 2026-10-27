module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.OrdCommon
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Fam.J4.Checks.D
public import CFSG.Certificates.Kernel.Fam.J4.Checks.K
public import CFSG.Certificates.Kernel.Fam.J4.Data.Pay
public import CFSG.Certificates.Kernel.Orders.J4.Checks.D
public import CFSG.Certificates.Kernel.Orders.J4.Checks.K
public import CFSG.Certificates.Kernel.Orders.J4.Data.Pay
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
public import CFSG.Certificates.Kernel.Fam.J4.Data.Const
public import CFSG.Certificates.Kernel.Orders.J4.Data.Sel
public import CFSG.Certificates.Kernel.Orders.J4.Data.Const
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelJ4Hub.Seed1 CFSG.Blueprint.NativeSporadic.J4Seed1

#ks_chars CertificateChecks.KernelJ4Hub.Seed2 CFSG.Blueprint.NativeSporadic.J4Seed2

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord

theorem fam1_bytes : CFSG.KS.Bytes.bytesEqK Seed1.chars CFSG.KD.FamJ4.P1 256 12789 = true := by
  quickRfl

theorem fam2_bytes : CFSG.KS.Bytes.bytesEqK Seed2.chars CFSG.KD.FamJ4.P2 256 12789 = true := by
  quickRfl

theorem ord1_bytes : CFSG.KS.Bytes.bytesEqK Seed1.chars CFSG.KD.OrdJ4.P1 256 12789 = true := by
  quickRfl

theorem ord2_bytes : CFSG.KS.Bytes.bytesEqK Seed2.chars CFSG.KD.OrdJ4.P2 256 12789 = true := by
  quickRfl

theorem fam_A : CFSG.Blueprint.NativeSporadic.decode 2 112 1 CFSG.Blueprint.NativeSporadic.J4Seed1 =
    ordMat 2 112 8 896 (CFSG.KD.FamJ4.RW 1) := by
  rw [Seed1.eq]
  exact seed_sound (hnb := rfl) (Cs := List.range 50) CFSG.KD.FamJ4.consts fam1_bytes rfl
    CFSG.KD.FamJ4.d1
    CFSG.KD.FamJ4.d1_end

theorem fam_B : CFSG.Blueprint.NativeSporadic.decode 2 112 1 CFSG.Blueprint.NativeSporadic.J4Seed2 =
    ordMat 2 112 8 896 (CFSG.KD.FamJ4.RW 2) := by
  rw [Seed2.eq]
  exact seed_sound (hnb := rfl) (Cs := List.range 50) CFSG.KD.FamJ4.consts fam2_bytes rfl
    CFSG.KD.FamJ4.d2
    CFSG.KD.FamJ4.d2_end

theorem ord_A : CFSG.Blueprint.NativeSporadic.decode 2 112 1 CFSG.Blueprint.NativeSporadic.J4Seed1 =
    ordMat 2 112 8 896 (CFSG.KD.OrdJ4.RW 1) := by
  rw [Seed1.eq]
  exact seed_sound (hnb := rfl) (Cs := List.range 50) CFSG.KD.OrdJ4.consts ord1_bytes rfl
    CFSG.KD.OrdJ4.d1
    CFSG.KD.OrdJ4.d1_end

theorem ord_B : CFSG.Blueprint.NativeSporadic.decode 2 112 1 CFSG.Blueprint.NativeSporadic.J4Seed2 =
    ordMat 2 112 8 896 (CFSG.KD.OrdJ4.RW 2) := by
  rw [Seed2.eq]
  exact seed_sound (hnb := rfl) (Cs := List.range 50) CFSG.KD.OrdJ4.consts ord2_bytes rfl
    CFSG.KD.OrdJ4.d2
    CFSG.KD.OrdJ4.d2_end

end CertificateChecks.KernelJ4Hub

end
