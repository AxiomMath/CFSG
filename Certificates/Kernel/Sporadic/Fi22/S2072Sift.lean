module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public import Certificates.Kernel.Sporadic.Fi22.H2066c0
public import Certificates.Kernel.Sporadic.Fi22.H2066c1
public import Certificates.Kernel.Sporadic.Fi22.H2066c2
public import Certificates.Kernel.Sporadic.Fi22.H2066c3
public import Certificates.Kernel.Sporadic.Fi22.H2066c4
public import CFSG.Certificates.Kernel.Spor.SiftBKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2072

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

@[expose] noncomputable def memK (S SI LR ST : Nat → Nat) (kS BP lo k : Nat) : Bool :=
  allN k fun j => strictB (Fi22CentT.L (Nat.add lo j)) fun q =>
    bAnd(cn q, bAnd(siftP q,
      siftBK 3510 12 (mask 12) (3510 * 12) 6 S SI LR ST kS 6 0 (baseImK 12 (mask 12) 6 q BP)))

theorem mc0s : memK Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 Fi22H0.BP 80 3 = true := by quickRfl
theorem mc0w : memK Fi22H0.S Fi22H0.SI Fi22H0.LR Fi22H0.ST 19 Fi22H0.BP 108 26 = true := by
  quickRfl
theorem mc1s : memK Fi22H1.S Fi22H1.SI Fi22H1.LR Fi22H1.ST 16 Fi22H1.BP 83 5 = true := by quickRfl
theorem mc1w : memK Fi22H1.S Fi22H1.SI Fi22H1.LR Fi22H1.ST 16 Fi22H1.BP 134 14 = true := by
  quickRfl
theorem mc2s : memK Fi22H2.S Fi22H2.SI Fi22H2.LR Fi22H2.ST 9 Fi22H2.BP 88 6 = true := by quickRfl
theorem mc2w : memK Fi22H2.S Fi22H2.SI Fi22H2.LR Fi22H2.ST 9 Fi22H2.BP 148 14 = true := by
  quickRfl
theorem mc3s : memK Fi22H3.S Fi22H3.SI Fi22H3.LR Fi22H3.ST 19 Fi22H3.BP 94 9 = true := by quickRfl
theorem mc3w : memK Fi22H3.S Fi22H3.SI Fi22H3.LR Fi22H3.ST 19 Fi22H3.BP 162 62 = true := by
  quickRfl
theorem mc4s : memK Fi22H4.S Fi22H4.SI Fi22H4.LR Fi22H4.ST 16 Fi22H4.BP 103 5 = true := by
  quickRfl
theorem mc4w : memK Fi22H4.S Fi22H4.SI Fi22H4.LR Fi22H4.ST 16 Fi22H4.BP 224 16 = true := by
  quickRfl

end CertificateChecks.KernelSpor.S2072

end
