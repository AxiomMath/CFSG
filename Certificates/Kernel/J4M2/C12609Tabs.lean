module

public import Certificates.Kernel.J4M2.C12609Data
public import Certificates.Kernel.J4M2.KDefs
public import Certificates.Kernel.J4M2.C12607Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4RR CFSG.KD.J4RR CertificateChecks.KernelJ4Gam

@[expose] noncomputable def rrGs : List Nat := [GA.1, GB.1, GZ.1]

theorem rrLo_chk : allR 64 (fun a => Nat.beq (getN 0 LO a) (pK a)) = true := by quickRfl

theorem rrHi_chk : allR 64 (fun b => Nat.beq (getN 0 HI b) (pK (64 * b))) = true := by quickRfl

theorem rrGl_chk : allR 3 (fun g => allR 64 fun a =>
    Nat.beq (getN 0 (getL GLs g) a) (mulJ c rm (getN 0 rrGs g) (getN 0 LO a))) = true := by
  quickRfl

theorem rrHg_chk : allR 3 (fun g => allR 64 fun b =>
    Nat.beq (getN 0 (getL HGs g) b) (mulJ c rm (getN 0 HI b) (getN 0 rrGs g))) = true := by
  quickRfl

theorem rrHz_chk : allR 3 (fun g => allR 64 fun b =>
    Nat.beq (getN 0 (getL HZs g) b) (mulJ c rm (getN 0 (getL HGs g) b) ZM)) = true := by
  quickRfl

theorem rrZg_chk : allR 3 (fun g =>
    Nat.beq (mulJ c rm ZM (getN 0 rrGs g)) (mulJ c rm (getN 0 rrGs g) ZM)) = true := by
  quickRfl

end CertificateChecks.KernelJ4M2

end
