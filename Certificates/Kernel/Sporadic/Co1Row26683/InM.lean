module

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCData

public section

namespace CertificateChecks.KernelSpor.C26683M

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.EvenSporadicStandard.Solomon78

def rA : Rows := twoBXYRows.2

def rB : Rows := mul (mul twoBXYRows.1 twoBXYRows.2) twoBXYRows.1

def dagZ : List Rows × List Rows × Bool := dag [rA, rB] [co1WordZ]

def dagL : List Rows × List Rows × Bool := dag [aR, bR] [co1WordL]

def rL : Rows := dagL.1.getD 2 (one ())

def rLi : Rows := dagL.2.1.getD 2 (one ())

def dagH : List Rows × List Rows × Bool :=
  dag [rA, rB, mul (mul rL rA) rLi, mul (mul rL rB) rLi] co1DagH

end CertificateChecks.KernelSpor.C26683M

end
