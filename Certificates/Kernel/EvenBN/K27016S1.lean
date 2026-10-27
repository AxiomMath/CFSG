module

public import Certificates.Kernel.EvenBN.K27016D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CertificateChecks.KernelEvenBN

theorem d128 : ((CNtC.drop 128).take 16).all cKc = true := by quickRfl
theorem d144 : ((CNtC.drop 144).take 16).all cKc = true := by quickRfl
theorem d160 : ((CNtC.drop 160).take 16).all cKc = true := by quickRfl
theorem d176 : ((CNtC.drop 176).take 16).all cKc = true := by quickRfl
theorem d192 : ((CNtC.drop 192).take 16).all cKc = true := by quickRfl
theorem d208 : ((CNtC.drop 208).take 16).all cKc = true := by quickRfl
theorem d224 : ((CNtC.drop 224).take 16).all cKc = true := by quickRfl
theorem d240 : ((CNtC.drop 240).take 16).all cKc = true := by quickRfl
theorem d256 : ((CNtC.drop 256).take 16).all cKc = true := by quickRfl
theorem d272 : ((CNtC.drop 272).take 16).all cKc = true := by quickRfl
theorem d288 : ((CNtC.drop 288).take 16).all cKc = true := by quickRfl
theorem d304 : ((CNtC.drop 304).take 16).all cKc = true := by quickRfl
theorem d320 : ((CNtC.drop 320).take 16).all cKc = true := by quickRfl
theorem d336 : ((CNtC.drop 336).take 16).all cKc = true := by quickRfl
theorem d352 : ((CNtC.drop 352).take 16).all cKc = true := by quickRfl
theorem d368 : ((CNtC.drop 368).take 16).all cKc = true := by quickRfl
theorem d384 : ((CNtC.drop 384).take 16).all cKc = true := by quickRfl
theorem d400 : ((CNtC.drop 400).take 16).all cKc = true := by quickRfl
theorem d416 : ((CNtC.drop 416).take 16).all cKc = true := by quickRfl
theorem d432 : ((CNtC.drop 432).take 16).all cKc = true := by quickRfl
theorem d448 : ((CNtC.drop 448).take 16).all cKc = true := by quickRfl
theorem d464 : ((CNtC.drop 464).take 16).all cKc = true := by quickRfl

end CertificateChecks.Batch27016

end
