module

public import Certificates.Kernel.Sporadic.Co2R3.Data
public import Certificates.Data.Kernel.Fi22Nbr3153
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.Co2R3

@[expose] noncomputable def rowB (s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 2300),
    rowOK (nat_lit 2300) (nat_lit 891) R M S x, true)) (nat_lit 64)

@[expose] noncomputable def imgB (k s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 2300),
    imgOK (nat_lit 2300) (nat_lit 891) (PK k) R M x, true)) (nat_lit 64)

@[expose] noncomputable def img0B (s : Nat) : Bool := imgB (nat_lit 0) s

@[expose] noncomputable def img1B (s : Nat) : Bool := imgB (nat_lit 1) s

end CertificateChecks.KernelSpor.Co2R3

#kc_slices CertificateChecks.KernelSpor.Co2R3.Row CertificateChecks.KernelSpor.Co2R3.rowB 36
#kc_slices CertificateChecks.KernelSpor.Co2R3.Img0 CertificateChecks.KernelSpor.Co2R3.img0B 36
#kc_slices CertificateChecks.KernelSpor.Co2R3.Img1 CertificateChecks.KernelSpor.Co2R3.img1B 36

namespace CertificateChecks.KernelSpor.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.Co2R3

theorem tree : allN 2300 (treeOK 2300 2 PK T) = true := by quickRfl

theorem sym0 : allN 891 (sym0OK R M) = true := by quickRfl

end CertificateChecks.KernelSpor.Co2R3

end
