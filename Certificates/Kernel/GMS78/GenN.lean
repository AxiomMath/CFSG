module

public import CFSG.Certificates.Kernel.GMS78RuGenN

public section

namespace CertificateChecks.KernelGMS78

open CFSG.KC.GMS CFSG.GMS78RuN CFSG.GMS78RuS

theorem nQuad_eq : nQuadCheck = Gen.nQuadCheck nBetaTab nTwTab nCols nBasis := rfl
theorem nComp_eq : nCompCheck = Gen.nCompCheck nBetaTab nTwTab nCols nBasis := rfl
theorem nId_eq : nIdCheck = Gen.nIdCheck nBetaTab nTwTab nCols nBasis := rfl
theorem nFaith_eq : nFaithCheck = Gen.nFaithCheck nBetaTab nCols := rfl
theorem nImg_eq : nImgCheck = Gen.nImgCheck nBetaTab nTwTab nCols nBasis nImg nImgInv := rfl
theorem nRel_eq : nRelCheck = Gen.nRelCheck nBetaTab nTwTab nCols nBasis nImg nImgInv
    CFSG.ComponentClassification.GMS78.RuPi7.relsA := rfl
theorem nClo_eq : nCloCheck = Gen.nCloCheck nBetaTab nTwTab nCols nBasis nImg nImgInv nRWords nKWords
    nRTargets := rfl
theorem nA0_eq : nA0Check = Gen.nA0Check nBetaTab nTwTab nCols nBasis nImg nImgInv
    CFSG.ComponentClassification.GMS78.RuAsm.ruA0Words := rfl

end CertificateChecks.KernelGMS78

end
