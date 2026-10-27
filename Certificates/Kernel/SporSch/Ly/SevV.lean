module

public import Certificates.Kernel.SporSch.Ly.GenSeven
public import Certificates.Data.Kernel.SporSch.LySeven
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kly_sevvec CertificateChecks.KernelSporSch.LySvV 0 128
#kly_sevvec CertificateChecks.KernelSporSch.LySvV 1 128
#kly_sevvec CertificateChecks.KernelSporSch.LySvV 2 128

namespace CertificateChecks.KernelSporSch.LySvV

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev

@[expose] noncomputable def E0 (i : Nat) : Nat := rowR ET0 21 i
@[expose] noncomputable def P0 (i : Nat) : Nat := rowR PT0 24 i
@[expose] noncomputable def E1 (i : Nat) : Nat := rowR ET1 21 i
@[expose] noncomputable def P1 (i : Nat) : Nat := rowR PT1 24 i
@[expose] noncomputable def E2 (i : Nat) : Nat := rowR ET2 21 i
@[expose] noncomputable def P2 (i : Nat) : Nat := rowR PT2 24 i

@[expose] noncomputable def vq0 (q : Nat) : Bool :=
  bIf(Nat.blt q nS0, Nat.beq (vRun GP0 E0 P0 kg0 c0 (Nat.mul q 128) 128 (C0 q)) (C0 (Nat.succ q)), true)
@[expose] noncomputable def vq1 (q : Nat) : Bool :=
  bIf(Nat.blt q nS1, Nat.beq (vRun GP1 E1 P1 kg1 c1 (Nat.mul q 128) 128 (C1 q)) (C1 (Nat.succ q)), true)
@[expose] noncomputable def vq2 (q : Nat) : Bool :=
  bIf(Nat.blt q nS2, Nat.beq (vRun GP2 E2 P2 kg2 c2 (Nat.mul q 128) 128 (C2 q)) (C2 (Nat.succ q)), true)

end CertificateChecks.KernelSporSch.LySvV

#kly_chain CertificateChecks.KernelSporSch.LySvV vr0 CertificateChecks.KernelSporSch.LySvV.vq0 31 4
#kly_chain CertificateChecks.KernelSporSch.LySvV vr1 CertificateChecks.KernelSporSch.LySvV.vq1 7 4
#kly_chain CertificateChecks.KernelSporSch.LySvV vr2 CertificateChecks.KernelSporSch.LySvV.vq2 1 1

namespace CertificateChecks.KernelSporSch.LySvV

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev

theorem sz0 : Nat.beq c0 15624 = true := by quickRfl
theorem sz1 : Nat.beq c1 3125 = true := by quickRfl
theorem sz2 : Nat.beq c2 120 = true := by quickRfl
theorem cv0 : Nat.ble c0 (Nat.mul nS0 128) = true := by quickRfl
theorem cv1 : Nat.ble c1 (Nat.mul nS1 128) = true := by quickRfl
theorem cv2 : Nat.ble c2 (Nat.mul nS2 128) = true := by quickRfl
theorem ns0 : Nat.ble nS0 124 = true := by quickRfl
theorem ns1 : Nat.ble nS1 28 = true := by quickRfl
theorem ns2 : Nat.ble nS2 1 = true := by quickRfl
theorem st0 : Nat.beq (C0 0) (Nat.add 1 (Nat.mul (2 ^ 20) (2 ^ code7K (E0 0)))) = true := by quickRfl
theorem st1 : Nat.beq (C1 0) (Nat.add 1 (Nat.mul (2 ^ 20) (2 ^ code7K (E1 0)))) = true := by quickRfl
theorem st2 : Nat.beq (C2 0) (Nat.add 1 (Nat.mul (2 ^ 20) (2 ^ code7K (E2 0)))) = true := by quickRfl
theorem fin0 : Nat.beq (Nat.land (C0 nS0) 1048575) c0 = true := by quickRfl
theorem fin1 : Nat.beq (Nat.land (C1 nS1) 1048575) c1 = true := by quickRfl
theorem fin2 : Nat.beq (Nat.land (C2 nS2) 1048575) c2 = true := by quickRfl
theorem pl0 : Nat.beq (P0 0) 0 = true := by quickRfl
theorem pl1 : Nat.beq (P1 0) 0 = true := by quickRfl
theorem pl2 : Nat.beq (P2 0) 0 = true := by quickRfl

end CertificateChecks.KernelSporSch.LySvV

end
