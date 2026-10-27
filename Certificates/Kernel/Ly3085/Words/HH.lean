module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.LyOmega.Words
public import Certificates.Data.GH74.LyHH
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CertificateChecks.KernelSporSch CFSG.Sporadic.Ly.HH

@[expose] noncomputable def hhVals : List (Nat × Nat) :=
  slpVals BC LyBS.A LyBS.B LyBS.B4 hhWords.toList

theorem hh_rels_checks : relsOK BC LyBS.A LyBS.B LyBS.B4 hhVals hhRels = true := by quickRfl

theorem hh_nes_checks : nesOK BC LyBS.A LyBS.B LyBS.B4 hhVals hhNe = true := by quickRfl

theorem neg_hh : notB (nesOK BC LyBS.A LyBS.B LyBS.B4 hhVals [([5], [5], 0)]) = true := by
  quickRfl

end CFSG.KD.LyOm

end
