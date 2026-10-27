module

public import Certificates.Kernel.EvenBN.K27016D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CertificateChecks.KernelEvenBN

theorem d1184 : ((CNtC.drop 1184).take 16).all cKc = true := by quickRfl
theorem d1200 : ((CNtC.drop 1200).take 16).all cKc = true := by quickRfl
theorem d1216 : ((CNtC.drop 1216).take 16).all cKc = true := by quickRfl
theorem d1232 : ((CNtC.drop 1232).take 16).all cKc = true := by quickRfl
theorem d1248 : ((CNtC.drop 1248).take 16).all cKc = true := by quickRfl
theorem d1264 : ((CNtC.drop 1264).take 16).all cKc = true := by quickRfl
theorem d1280 : ((CNtC.drop 1280).take 16).all cKc = true := by quickRfl
theorem d1296 : ((CNtC.drop 1296).take 16).all cKc = true := by quickRfl
theorem d1312 : ((CNtC.drop 1312).take 16).all cKc = true := by quickRfl
theorem d1328 : ((CNtC.drop 1328).take 16).all cKc = true := by quickRfl
theorem d1344 : ((CNtC.drop 1344).take 16).all cKc = true := by quickRfl
theorem d1360 : ((CNtC.drop 1360).take 16).all cKc = true := by quickRfl
theorem d1376 : ((CNtC.drop 1376).take 16).all cKc = true := by quickRfl
theorem d1392 : ((CNtC.drop 1392).take 16).all cKc = true := by quickRfl
theorem d1408 : ((CNtC.drop 1408).take 16).all cKc = true := by quickRfl
theorem d1424 : ((CNtC.drop 1424).take 16).all cKc = true := by quickRfl
theorem d1440 : ((CNtC.drop 1440).take 16).all cKc = true := by quickRfl
theorem d1456 : ((CNtC.drop 1456).take 16).all cKc = true := by quickRfl
theorem d1472 : ((CNtC.drop 1472).take 16).all cKc = true := by quickRfl
theorem d1488 : ((CNtC.drop 1488).take 16).all cKc = true := by quickRfl
theorem d1504 : ((CNtC.drop 1504).take 16).all cKc = true := by quickRfl
theorem d1520 : ((CNtC.drop 1520).take 16).all cKc = true := by quickRfl

end CertificateChecks.Batch27016

end
