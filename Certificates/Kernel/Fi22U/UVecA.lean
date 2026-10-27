module

public import Certificates.Kernel.Sporadic.Fi22.F1OuterS
public import Certificates.Data.Kernel.Fi22U.Codes
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22U.UVec

open CFSG.KC.Fi22U CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor

@[expose] noncomputable def BN : Nat := charsC Fi22OUP.chars

@[expose] noncomputable def VN : Nat := charsC Fi22OTV.chars

@[expose] noncomputable def seedRow (k : Nat) : Bool :=
  allN 693 fun j => Nat.blt (pg 10 (mask 10) (Fi22O693T.L (15 + k)) j) 693 &&
    normC (tvC (tabC VN k) (tabC BN j)) == tabC BN (pg 10 (mask 10) (Fi22O693T.L (15 + k)) j)

theorem pts : allN 693 (fun k => ptOK (tabC BN k)) = true := by decide +kernel

theorem lex : allN 692 (fun j => lexC (tabC BN j) (tabC BN (j + 1))) = true := by decide +kernel

theorem cnt : cntPt 4096 = 693 := by decide +kernel

theorem viso : allN 46 (fun k => hermC (tabC VN k) (tabC VN k) == 0) = true := by decide +kernel

end CertificateChecks.KernelFi22U.UVec

#kc_each CertificateChecks.KernelFi22U.UVec.seedRow 0 23

end
