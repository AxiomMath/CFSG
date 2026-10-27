module

public import CFSG.Sporadic.Schreier.J4SFormData
public import Certificates.Kernel.SporSch.J4S.RealK
public import CFSG.Certificates.Kernel.SporSch.J4SFormSound
meta import CFSG.Sporadic.Schreier.J4SFormData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_rows CertificateChecks.KernelSporSch.J4FR CFSG.Sporadic.J4Schreier.formRows
#kss_rows CertificateChecks.KernelSporSch.J4FI CFSG.Sporadic.J4Schreier.formInvRows
#kss_rows CertificateChecks.KernelSporSch.J4FU CFSG.Sporadic.J4Schreier.formUpRows

namespace CertificateChecks.KernelSporSch.J4Form

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4Real

@[expose] noncomputable def defK (P : Nat) : Bool :=
  CFSG.KC.J4Q.strictB (Nat.xor (mulJ c rm (mulJ c rm P J4FU) (trJ t0 t1 t2 t3 t4 t5 t6 P)) J4FU)
    fun D => Nat.beq D (Nat.xor (Nat.land D lowJ) (trJ t0 t1 t2 t3 t4 t5 t6 (Nat.land D lowJ)))

theorem fr : packNK formRows.toList J4FR = true := by quickRfl
theorem fi : packNK formInvRows.toList J4FI = true := by quickRfl
theorem fu : allN 112 (fun i => Nat.beq (rowJ rm J4FU i) (Nat.lor (Nat.shiftLeft
    (Nat.shiftRight (formRows[i]?.getD 0) (Nat.succ i)) (Nat.succ i)) (Nat.pow 2 i))) = true := by
  quickRfl
theorem fuc : canonJ pad J4FU = true := by quickRfl
theorem sym : Nat.beq (Nat.xor J4FU (trJ t0 t1 t2 t3 t4 t5 t6 J4FU)) J4FR = true := by quickRfl
theorem inv1 : Nat.beq (mulJ c rm J4FR J4FI) one = true := by quickRfl
theorem inv2 : Nat.beq (mulJ c rm J4FI J4FR) one = true := by quickRfl
theorem defA : defK A = true := by quickRfl
theorem defB : defK B = true := by quickRfl

end CertificateChecks.KernelSporSch.J4Form

end
