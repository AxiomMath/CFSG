module

public meta import Lean
meta import Certificates.Data.Sp62RecCR1CE
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiRep.Gen

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec

meta def recX : List Nat := recsW gWords 1536

meta def recN : List Nat := recsW nWords 10752

meta def recH : List Nat := recsW hWords 23040

meta def recE : List Nat := recsW e0Words 11520

meta def recV : List Nat := recsI v0Idx 32

end CFSG.KD.YamakiRep.Gen

#kss_ntree CFSG.KD.YamakiRep.RX CFSG.KD.YamakiRep.Gen.recX
#kss_ntree CFSG.KD.YamakiRep.RN CFSG.KD.YamakiRep.Gen.recN
#kss_ntree CFSG.KD.YamakiRep.RH CFSG.KD.YamakiRep.Gen.recH
#kss_ntree CFSG.KD.YamakiRep.RE CFSG.KD.YamakiRep.Gen.recE
#kss_ntree CFSG.KD.YamakiRep.RV CFSG.KD.YamakiRep.Gen.recV
