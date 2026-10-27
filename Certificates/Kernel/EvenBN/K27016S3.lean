module

public import Certificates.Kernel.EvenBN.K27016D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CertificateChecks.KernelEvenBN

theorem d832 : ((CNtC.drop 832).take 16).all cKc = true := by quickRfl
theorem d848 : ((CNtC.drop 848).take 16).all cKc = true := by quickRfl
theorem d864 : ((CNtC.drop 864).take 16).all cKc = true := by quickRfl
theorem d880 : ((CNtC.drop 880).take 16).all cKc = true := by quickRfl
theorem d896 : ((CNtC.drop 896).take 16).all cKc = true := by quickRfl
theorem d912 : ((CNtC.drop 912).take 16).all cKc = true := by quickRfl
theorem d928 : ((CNtC.drop 928).take 16).all cKc = true := by quickRfl
theorem d944 : ((CNtC.drop 944).take 16).all cKc = true := by quickRfl
theorem d960 : ((CNtC.drop 960).take 16).all cKc = true := by quickRfl
theorem d976 : ((CNtC.drop 976).take 16).all cKc = true := by quickRfl
theorem d992 : ((CNtC.drop 992).take 16).all cKc = true := by quickRfl
theorem d1008 : ((CNtC.drop 1008).take 16).all cKc = true := by quickRfl
theorem d1024 : ((CNtC.drop 1024).take 16).all cKc = true := by quickRfl
theorem d1040 : ((CNtC.drop 1040).take 16).all cKc = true := by quickRfl
theorem d1056 : ((CNtC.drop 1056).take 16).all cKc = true := by quickRfl
theorem d1072 : ((CNtC.drop 1072).take 16).all cKc = true := by quickRfl
theorem d1088 : ((CNtC.drop 1088).take 16).all cKc = true := by quickRfl
theorem d1104 : ((CNtC.drop 1104).take 16).all cKc = true := by quickRfl
theorem d1120 : ((CNtC.drop 1120).take 16).all cKc = true := by quickRfl
theorem d1136 : ((CNtC.drop 1136).take 16).all cKc = true := by quickRfl
theorem d1152 : ((CNtC.drop 1152).take 16).all cKc = true := by quickRfl
theorem d1168 : ((CNtC.drop 1168).take 16).all cKc = true := by quickRfl

end CertificateChecks.Batch27016

end
