module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Data.McLCls
public import Certificates.Data.Kernel.McLCls
meta import Certificates.Data.McLCls
meta import Certificates.Data.Kernel.McLCls
meta import CFSG.Sporadic.SmallOddCore.McLData

public section

namespace CertificateChecks.KernelMcLCls

meta def natL (T : Array UInt32) : Array Nat := T.map UInt32.toNat

meta def sGensM : List (Array Nat) :=
  [6, 7, 8].map fun k => natL (CFSG.SectionRank.QTK.Insp443.McLCls.clsTbl k)

meta def cGensM : Array (Array Nat) :=
  #[5, 6].map fun k => natL (CFSG.Sporadic.SmallOddCore.mclCentTbl k)

meta def v1M : Array Nat := natL (CFSG.SectionRank.QTK.Insp443.McLCls.clsTbl 0)

meta def wordM (wd : List Nat) : Array Nat :=
  wd.foldr (fun j acc => acc.map fun i => (if j == 0 then cGensM[0]! else cGensM[1]!)[i]!)
    (Array.range 275)

meta def r5M : List (Array Nat) := [wordM [1, 1, 1, 1, 0]]

meta def r7M : List (Array Nat) := [wordM [1, 1]]

meta def p3M : List (Array Nat) :=
  [wordM [1, 0, 1, 0, 1, 0, 1, 0, 1, 0], wordM [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]]

end CertificateChecks.KernelMcLCls

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelMcLCls.SE CertificateChecks.KernelMcLCls.sGensM 275 9
#lc_bfs CertificateChecks.KernelMcLCls.AE CFSG.KC.M305.oAct 7 4
#lc_bfs CertificateChecks.KernelMcLCls.R5E CertificateChecks.KernelMcLCls.r5M 275 9
#lc_bfs CertificateChecks.KernelMcLCls.R7E CertificateChecks.KernelMcLCls.r7M 275 9
#lc_bfs CertificateChecks.KernelMcLCls.P3E CertificateChecks.KernelMcLCls.p3M 275 9
#conj_orb CertificateChecks.KernelMcLCls.IE CertificateChecks.KernelMcLCls.cGensM 275 9
  CFSG.KC.M305.sKeys 105 roots CertificateChecks.KernelMcLCls.v1M gens 2

end
