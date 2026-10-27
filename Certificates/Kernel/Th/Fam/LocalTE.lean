module

public import CFSG.Certificates.Kernel.Th.Expr
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaData

public section

namespace CertificateChecks.KernelTh.Fam.Local

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Max3 CFSG.EvenSporadicStandard.ThStd.LocalDataTh

@[expose] def a1T : TE := .nfE 0 (bitsOf 1)
@[expose] def a2T : TE := .nfE 0 (bitsOf 50)
@[expose] def a3T : TE := .nfE 0 (bitsOf 100)

@[expose] def aelT (e : ℕ) : TE :=
  .mul (.mul (.mul (.pow .z (e % 2)) (.pow a1T (e / 2 % 2))) (.pow a2T (e / 4 % 2)))
    (.pow a3T (e / 8 % 2))

@[expose] def n1T : TE := .mul .x .y

@[expose] def fusionQ0T : TE :=
  .mul (.pow (.mul (.mul (.mul (.ab (AllConj.invWord fusionWordQ0)) (.q 0))
    (.ab fusionWordQ0)) .a) 9) (.ab (AllConj.invWord fusionWordQ0))

@[expose] def n2T : TE := .mul (.word [.y, .x, .y]) fusionQ0T

@[expose] def nfCT (s n : ℕ) : TE := .nfE s (bitsOf n)

@[expose] def g1T : TE := .mul (nfCT 1 50) (.word wG1)
@[expose] def g2T : TE := nfCT 0 45
@[expose] def g3T : TE := .mul (.mul (nfCT 1 243) (.word wG3)) (nfCT 0 2)
@[expose] def g4T : TE := .mul (.mul (nfCT 0 73) (.word wG4)) (nfCT 0 10)
@[expose] def beT : TE := nfCT 0 136

@[expose] def peT (e : ℕ) : TE :=
  .mul (.mul (.mul (.pow g1T (e % 2)) (.pow g2T (e / 2 % 2))) (.pow g3T (e / 4 % 2)))
    (.pow g4T (e / 8 % 2))

@[expose] def geT (e₀ e₁ e₂ e₃ : ℕ) : TE :=
  .mul (.mul (.mul (.pow g1T e₀) (.pow g2T e₁)) (.pow g3T e₂)) (.pow g4T e₃)

end CertificateChecks.KernelTh.Fam.Local

end
