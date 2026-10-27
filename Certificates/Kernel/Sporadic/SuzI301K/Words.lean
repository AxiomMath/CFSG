module

public import Certificates.Kernel.Sporadic.SuzI301K.Data
public import Certificates.Data.Kernel.SuzI301K
public import Certificates.Kernel.LocalComp.B0SuzMat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.SuzI301K CFSG.KD.SuzI301
open CFSG.ComponentClassification.AS81.SuzB0 CertificateChecks.KernelLC

theorem kCW : cwK QJ CW = true := by quickRfl

theorem kIV : ivK CW IV = true := by quickRfl

theorem kHW : hwK CW HW = true := by quickRfl

theorem kGW : gwK (fun k i => (act k i).1) GW CW = true := by quickRfl

theorem kNotIn : notInK SuzB0M.T SuzB0M.N (nthN CW 3) = true := by quickRfl

theorem kCent : centK SuzB0M.T SuzB0M.N (nthN CW 0) CX = true := by quickRfl

theorem kForm : formK gammaBit (nthN CW 0) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzI301K

end
