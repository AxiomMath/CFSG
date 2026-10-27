module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeTcData

public section

namespace CertificateChecks.KernelTc.He

open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

@[expose] def heTcWs : List (List Int) :=
  [heTcU0, heTcV0, heTcU1, heTcV1, heTcK0, heTcK1, heTcR1, heTcR2, heTcR3, heTcR4, heTcR5, heTcR6,
    heTcS1, heTcS2, heThreeWordsA.getD 0 []]

@[expose] def cQ : CFSG.Monster.B.Fischer.ArrCert := heTcCQ ()

@[expose] def cK : CFSG.Monster.B.Fischer.ArrCert := heTcCK ()

@[expose] def cY : CFSG.Monster.B.Fischer.ArrCert := heTcCY ()

@[expose] def sig : Array (Array Nat) := heTcD.sig

@[expose] def keys7 : Array Nat := (List.range 7).toArray

end CertificateChecks.KernelTc.He

end
