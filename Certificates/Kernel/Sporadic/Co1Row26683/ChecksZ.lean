module

public import Certificates.Kernel.Sporadic.Co1Row26683.Data
public import Certificates.Kernel.Sporadic.Co1Row26683.DataZ
public import Certificates.Kernel.Sporadic.Co1Row26683.DagM
public import Certificates.Kernel.Co1B.TriD2045
public import Certificates.Kernel.Co1B.Orb2045
public import Certificates.Data.Kernel.Spor.Co1Row26683Z
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.KS.Co1Row26683 CFSG.KS.Co1Row26683Z CertificateChecks.KernelCo1B.Tri2045
  CertificateChecks.KernelSpor

theorem ch26683Z : triZK (C26683M.Z.M (nat_lit 2)) TB.PT C26683Z.PZ = true := by
  quickRfl

theorem ch26683Q :
    withXY TB.P TB.PI (nat_lit 10) (nat_lit 11)
      (fun X Y Xi Yi => zqK X Y Xi Yi C26683Z.PZ C26683.WC C26683.ZQ) = true := by
  quickRfl

theorem ch26683P : primK RO.S CFSG.Sporadic.Co1Block.twoBSubReps = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co1Row26683

end
