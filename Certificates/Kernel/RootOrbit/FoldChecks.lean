module

public import Certificates.Data.Kernel.RootOrbit.Check
public import Certificates.Kernel.RootOrbit.Data
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighCheck

public section

open CFSG.KC.RootOrbit CFSG.KD.RootOrbit CFSG.HardMathSupport.Timmesfeld.LangTorus

namespace CertificateChecks.KernelRootOrbit

theorem foldD5 : foldCertB (rowsZ rD5) 5 3 4 (signedL pD5) fD5 = true := by decide +kernel
theorem foldD6 : foldCertB (rowsZ rD6) 6 4 5 (signedL pD6) fD6 = true := by decide +kernel
theorem foldD7 : foldCertB (rowsZ rD7) 7 5 6 (signedL pD7) fD7 = true := by decide +kernel
theorem foldD8 : foldCertB (rowsZ rD8) 8 6 7 (signedL pD8) fD8 = true := by decide +kernel

theorem orthD5 : orthOK (CartanMatrix.D 5) 3 4 (signedL pD5) = true := by decide +kernel
theorem orthD6 : orthOK (CartanMatrix.D 6) 4 5 (signedL pD6) = true := by decide +kernel
theorem orthD7 : orthOK (CartanMatrix.D 7) 5 6 (signedL pD7) = true := by decide +kernel
theorem orthD8 : orthOK (CartanMatrix.D 8) 6 7 (signedL pD8) = true := by decide +kernel

theorem smallD5 : (sepPairB (CartanMatrix.D 5) (2 * 5) 3 4 && CartanMatrix.D 5 3 4 == 0 &&
    adjOK (CartanMatrix.D 5) 3 4) = true := by decide +kernel
theorem smallD6 : (sepPairB (CartanMatrix.D 6) (2 * 6) 4 5 && CartanMatrix.D 6 4 5 == 0 &&
    adjOK (CartanMatrix.D 6) 4 5) = true := by decide +kernel
theorem smallD7 : (sepPairB (CartanMatrix.D 7) (2 * 7) 5 6 && CartanMatrix.D 7 5 6 == 0 &&
    adjOK (CartanMatrix.D 7) 5 6) = true := by decide +kernel
theorem smallD8 : (sepPairB (CartanMatrix.D 8) (2 * 8) 6 7 && CartanMatrix.D 8 6 7 == 0 &&
    adjOK (CartanMatrix.D 8) 6 7) = true := by decide +kernel

end CertificateChecks.KernelRootOrbit
