module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.LyOmega.Words
public import Certificates.Data.GH74.LyTwoWeights
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CertificateChecks.KernelSporSch CFSG.Sporadic.Ly.TwoWeights

@[expose] noncomputable def twVals : List (Nat × Nat) :=
  slpVals BC LyBS.A LyBS.B LyBS.B4 twWords.toList

theorem tw_checks : relsOK BC LyBS.A LyBS.B LyBS.B4 twVals twRels = true := by quickRfl

theorem neg_tw : notB (relsOK BC LyBS.A LyBS.B LyBS.B4 twVals [([13, 13], [])]) = true := by
  quickRfl

end CFSG.KD.LyOm

end
