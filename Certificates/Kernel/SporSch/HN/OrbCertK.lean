module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Certificates.Data.Kernel.SporSch.HNXPrim
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
public import Certificates.Data.CFSGNative.HN.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.HNSA CFSG.Sporadic.HN.Native.seedA
#ks_chars CertificateChecks.KernelSporSch.HNSB CFSG.Sporadic.HN.Native.seedB

namespace CertificateChecks.KernelSporSch.HNXCert

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.KD.OrdHN CertificateChecks.KernelSporSch

theorem seedA_ok' : seedRK (RW 1) HNSA.chars = true := by quickRfl
theorem seedB_ok' : seedRK (RW 2) HNSB.chars = true := by quickRfl
theorem validA : validHN (RW 1) = true := by quickRfl
theorem validB : validHN (RW 2) = true := by quickRfl
theorem oneId : isIdK ONE = true := by quickRfl
theorem ordA : Nat.beq (CFSG.KC.LL.HN.mm (RW 1) (RW 1)) ONE = true := by quickRfl
theorem ordB : Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KC.LL.HN.mm (RW 2) (RW 2)) (RW 2)) ONE = true := by
  quickRfl

theorem neg_seed : Bool.not (seedRK (RW 2) HNSA.chars) = true := by quickRfl
theorem neg_ordA : Bool.not (Nat.beq (CFSG.KC.LL.HN.mm (RW 2) (RW 2)) ONE) = true := by quickRfl
theorem neg_ordB : Bool.not (Nat.beq (CFSG.KC.LL.HN.mm (RW 2) (RW 2)) (RW 2)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNXCert

end
