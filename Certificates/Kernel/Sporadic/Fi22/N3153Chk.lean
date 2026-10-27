module

public import Certificates.Kernel.Sporadic.Fi22.N3153R0
public import Certificates.Kernel.Sporadic.Fi22.N3153R1
public import Certificates.Kernel.Sporadic.Fi22.N3153R2
public import Certificates.Kernel.Sporadic.Fi22.N3153R3
public import Certificates.Kernel.Sporadic.Fi22.N3153R4
public import Certificates.Kernel.Sporadic.Fi22.N3153R5
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kc_slices CertificateChecks.KernelSpor.N3153.Cell CertificateChecks.KernelSpor.N3153.cellB 6

namespace CertificateChecks.KernelSpor.N3153

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153

theorem Row.all : ∀ s < 55, rowB s = true := by
  intro s hs
  interval_cases s
  exacts [rowS0, rowS1, rowS2, rowS3, rowS4, rowS5, rowS6, rowS7, rowS8, rowS9, rowS10, rowS11,
    rowS12, rowS13, rowS14, rowS15, rowS16, rowS17, rowS18, rowS19, rowS20, rowS21, rowS22, rowS23,
    rowS24, rowS25, rowS26, rowS27, rowS28, rowS29, rowS30, rowS31, rowS32, rowS33, rowS34, rowS35,
    rowS36, rowS37, rowS38, rowS39, rowS40, rowS41, rowS42, rowS43, rowS44, rowS45, rowS46, rowS47,
    rowS48, rowS49, rowS50, rowS51, rowS52, rowS53, rowS54]

theorem Img0.all : ∀ s < 55, img0B s = true := by
  intro s hs
  interval_cases s
  exacts [img0S0, img0S1, img0S2, img0S3, img0S4, img0S5, img0S6, img0S7, img0S8, img0S9, img0S10,
    img0S11, img0S12, img0S13, img0S14, img0S15, img0S16, img0S17, img0S18, img0S19, img0S20,
    img0S21, img0S22, img0S23, img0S24, img0S25, img0S26, img0S27, img0S28, img0S29, img0S30,
    img0S31, img0S32, img0S33, img0S34, img0S35, img0S36, img0S37, img0S38, img0S39, img0S40,
    img0S41, img0S42, img0S43, img0S44, img0S45, img0S46, img0S47, img0S48, img0S49, img0S50,
    img0S51, img0S52, img0S53, img0S54]

theorem Img1.all : ∀ s < 55, img1B s = true := by
  intro s hs
  interval_cases s
  exacts [img1S0, img1S1, img1S2, img1S3, img1S4, img1S5, img1S6, img1S7, img1S8, img1S9, img1S10,
    img1S11, img1S12, img1S13, img1S14, img1S15, img1S16, img1S17, img1S18, img1S19, img1S20,
    img1S21, img1S22, img1S23, img1S24, img1S25, img1S26, img1S27, img1S28, img1S29, img1S30,
    img1S31, img1S32, img1S33, img1S34, img1S35, img1S36, img1S37, img1S38, img1S39, img1S40,
    img1S41, img1S42, img1S43, img1S44, img1S45, img1S46, img1S47, img1S48, img1S49, img1S50,
    img1S51, img1S52, img1S53, img1S54]

theorem tree : allN 3510 (treeOK 3510 2 GP T) = true := by quickRfl

theorem root : allN 3510 (rootOK M (GP 2)) = true := by quickRfl

theorem sym0 : allN 693 (sym0OK R M) = true := by quickRfl

theorem inj : strictB (GP 3) (fun T => injK 3510 S T [0, 1, 2, 3, 6, 4] 4 (O 0)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.N3153

end
