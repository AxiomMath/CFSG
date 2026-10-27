module

public import Certificates.Kernel.EvenBN.K27016D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CertificateChecks.KernelEvenBN

theorem d480 : ((CNtC.drop 480).take 16).all cKc = true := by quickRfl
theorem d496 : ((CNtC.drop 496).take 16).all cKc = true := by quickRfl
theorem d512 : ((CNtC.drop 512).take 16).all cKc = true := by quickRfl
theorem d528 : ((CNtC.drop 528).take 16).all cKc = true := by quickRfl
theorem d544 : ((CNtC.drop 544).take 16).all cKc = true := by quickRfl
theorem d560 : ((CNtC.drop 560).take 16).all cKc = true := by quickRfl
theorem d576 : ((CNtC.drop 576).take 16).all cKc = true := by quickRfl
theorem d592 : ((CNtC.drop 592).take 16).all cKc = true := by quickRfl
theorem d608 : ((CNtC.drop 608).take 16).all cKc = true := by quickRfl
theorem d624 : ((CNtC.drop 624).take 16).all cKc = true := by quickRfl
theorem d640 : ((CNtC.drop 640).take 16).all cKc = true := by quickRfl
theorem d656 : ((CNtC.drop 656).take 16).all cKc = true := by quickRfl
theorem d672 : ((CNtC.drop 672).take 16).all cKc = true := by quickRfl
theorem d688 : ((CNtC.drop 688).take 16).all cKc = true := by quickRfl
theorem d704 : ((CNtC.drop 704).take 16).all cKc = true := by quickRfl
theorem d720 : ((CNtC.drop 720).take 16).all cKc = true := by quickRfl
theorem d736 : ((CNtC.drop 736).take 16).all cKc = true := by quickRfl
theorem d752 : ((CNtC.drop 752).take 16).all cKc = true := by quickRfl
theorem d768 : ((CNtC.drop 768).take 16).all cKc = true := by quickRfl
theorem d784 : ((CNtC.drop 784).take 16).all cKc = true := by quickRfl
theorem d800 : ((CNtC.drop 800).take 16).all cKc = true := by quickRfl
theorem d816 : ((CNtC.drop 816).take 16).all cKc = true := by quickRfl

end CertificateChecks.Batch27016

end
