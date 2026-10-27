module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.RuTcData

public section

namespace CertificateChecks.KernelTc.Ru

open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

@[expose] def cQ : CFSG.Monster.B.Fischer.ArrCert := ruTcCQ ()

@[expose] def cK : CFSG.Monster.B.Fischer.ArrCert := ruTcCK ()

@[expose] def cC : CFSG.Monster.B.Fischer.ArrCert := ruCCert ()

@[expose] def cY : CFSG.Monster.B.Fischer.ArrCert := ruSylCert ()

@[expose] def sig : Array (Array Nat) := ruTcD.sig

@[expose] def keys6 : Array Nat := (List.range 6).toArray
end CertificateChecks.KernelTc.Ru

end
