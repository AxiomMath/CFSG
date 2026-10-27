module

public import Certificates.Kernel.Sporadic.OddCore.S2301Data
public import Certificates.Kernel.Sporadic.OddCore.S2301Gens
public import Certificates.Data.Kernel.Suz2301
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2301

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301 CFSG.KC.S2301

@[expose] noncomputable def blk (f : Nat → Bool) (s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 1782), f x, true)) (nat_lit 64)

@[expose] noncomputable def rowB (s : Nat) : Bool := blk (rowOK (nat_lit 1782) (nat_lit 416) R M S) s

@[expose] noncomputable def img0B (s : Nat) : Bool :=
  blk (imgOK (nat_lit 1782) (nat_lit 416) (GP (nat_lit 0)) R M) s

@[expose] noncomputable def img1B (s : Nat) : Bool :=
  blk (imgOK (nat_lit 1782) (nat_lit 416) (GP (nat_lit 1)) R M) s

@[expose] noncomputable def img2B (s : Nat) : Bool :=
  blk (imgOK (nat_lit 1782) (nat_lit 416) (GP (nat_lit 2)) R M) s

@[expose] noncomputable def maskB (s : Nat) : Bool := blk (maskOK (nat_lit 416) R W) s

end CertificateChecks.KernelSpor.S2301

#kc_slices CertificateChecks.KernelSpor.S2301.Row CertificateChecks.KernelSpor.S2301.rowB 28
#kc_slices CertificateChecks.KernelSpor.S2301.Img0 CertificateChecks.KernelSpor.S2301.img0B 28
#kc_slices CertificateChecks.KernelSpor.S2301.Img1 CertificateChecks.KernelSpor.S2301.img1B 28
#kc_slices CertificateChecks.KernelSpor.S2301.Img2 CertificateChecks.KernelSpor.S2301.img2B 28
#kc_slices CertificateChecks.KernelSpor.S2301.Mask CertificateChecks.KernelSpor.S2301.maskB 28

namespace CertificateChecks.KernelSpor.S2301

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301

theorem tree : allN 1782 (treeOK 1782 2 GP T) = true := by quickRfl

theorem sym0 : allN 416 (sym0OK R M) = true := by quickRfl

end CertificateChecks.KernelSpor.S2301

end
