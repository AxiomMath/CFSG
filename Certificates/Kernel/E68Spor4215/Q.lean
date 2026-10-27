module

public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificateInputs

public section

namespace CFSG.KD.E68S4215

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E6.Spor

@[expose] def heUT : Array (Array Nat) :=
  (heUWords.map (wordTabA #[He.heTaC, He.heTbC] 8330)).toArray

@[expose] def ruUT : Array (Array Nat) :=
  (ruUWords.map (wordTabA #[RuCert.ruTaL, RuCert.ruTbL] 4060)).toArray

@[expose] def qp0 : List (Nat × Nat) := [(0, 0)]

end CFSG.KD.E68S4215

end
