
module

public import Certificates.Kernel.SporSch.J4S.Eta
public import Certificates.Kernel.SporSch.J4S.FiveW
meta import Certificates.Kernel.SporSch.J4S.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4K0 CertificateChecks.KernelSporSch.J4Inv.kSuf0
#kss_pairs CertificateChecks.KernelSporSch.J4K1 CertificateChecks.KernelSporSch.J4Inv.kSuf1
#kss_pairs CertificateChecks.KernelSporSch.J4K2 CertificateChecks.KernelSporSch.J4Inv.kSuf2
#kss_pairs CertificateChecks.KernelSporSch.J4K3 CertificateChecks.KernelSporSch.J4Inv.kSuf3

namespace CertificateChecks.KernelSporSch.J4InvW

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta

@[expose] noncomputable def segN (w : List Int) (T : List Nat) (N k : Nat) : Bool :=
  bAnd(Nat.beq (wFK c rm one (R 1) (R 10) (R 2) (R 11) (takeI 100 (dropI (Nat.mul 100 k) w))
      (getN one T (Nat.succ k))) (getN one T k),
    Nat.beq (wSK c rm one (R 1) (R 10) (R 2) (R 11) (takeI 100 (dropI (Nat.mul 100 k) w))
      (getN one T (Nat.add (Nat.add N 2) k))) (getN one T (Nat.add (Nat.succ N) k)))

@[expose] noncomputable def seg0 (k : Nat) : Bool := segN J4FW.w0 J4K0 169 k
@[expose] noncomputable def seg1 (k : Nat) : Bool := segN J4FW.w1 J4K1 58 k
@[expose] noncomputable def seg2 (k : Nat) : Bool := segN J4FW.w2 J4K2 2 k
@[expose] noncomputable def seg3 (k : Nat) : Bool := segN J4FW.w3 J4K3 3 k

theorem b0 : bAnd(Nat.beq (getN one J4K0 169) one, Nat.beq (getN one J4K0 339) one) = true := by
  quickRfl
theorem b1 : bAnd(Nat.beq (getN one J4K1 58) one, Nat.beq (getN one J4K1 117) one) = true := by
  quickRfl
theorem b2 : bAnd(Nat.beq (getN one J4K2 2) one, Nat.beq (getN one J4K2 5) one) = true := by
  quickRfl
theorem b3 : bAnd(Nat.beq (getN one J4K3 3) one, Nat.beq (getN one J4K3 7) one) = true := by
  quickRfl

theorem letters : ∀ w ∈ J4FW.ws, ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by decide +kernel
theorem len0 : J4FW.w0.length ≤ 100 * 169 := by decide +kernel
theorem len1 : J4FW.w1.length ≤ 100 * 58 := by decide +kernel
theorem len2 : J4FW.w2.length ≤ 100 * 2 := by decide +kernel
theorem len3 : J4FW.w3.length ≤ 100 * 3 := by decide +kernel

end CertificateChecks.KernelSporSch.J4InvW

#kss_slices CertificateChecks.KernelSporSch.J4KS0 CertificateChecks.KernelSporSch.J4InvW.seg0 1 169
#kss_slices CertificateChecks.KernelSporSch.J4KS1 CertificateChecks.KernelSporSch.J4InvW.seg1 1 58
#kss_slices CertificateChecks.KernelSporSch.J4KS2 CertificateChecks.KernelSporSch.J4InvW.seg2 1 2
#kss_slices CertificateChecks.KernelSporSch.J4KS3 CertificateChecks.KernelSporSch.J4InvW.seg3 1 3

end
