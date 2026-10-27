module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Data.GH74.McLGen45
public meta import Certificates.Data.GH74.McLGen45

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLGen

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.LevelChain.Native
  CFSG.Sporadic.McL.Gen45

meta def t0M : Table := mclGenTbl 0
meta def t1M : Table := mclGenTbl 1
meta def atM : Array Nat := t0M.map (·.toNat)
meta def aiM : Array Nat := (invT 275 t0M).map (·.toNat)
meta def btM : Array Nat := t1M.map (·.toNat)
meta def biM : Array Nat := (invT 275 t1M).map (·.toNat)

meta def lettersM : Array Table := slpLetters 275 (mclLetters t0M t1M) mclGenWords

meta def ltM : Array Nat := (lettersM.map fun t => t.map (·.toNat)).flatten

meta def startsM : Array Nat := #[8, 10, 12, 14, 17, 18]
meta def lv0M : Array Nat := levelLv startsM 0
meta def lv1M : Array Nat := levelLv startsM 1
meta def lv2M : Array Nat := levelLv startsM 2
meta def lv3M : Array Nat := levelLv startsM 3
meta def lv4M : Array Nat := levelLv startsM 4

end CertificateChecks.KernelMcLGen

#krows CertificateChecks.KernelMcLGen.AT CertificateChecks.KernelMcLGen.atM
#krows CertificateChecks.KernelMcLGen.AI CertificateChecks.KernelMcLGen.aiM
#krows CertificateChecks.KernelMcLGen.BT CertificateChecks.KernelMcLGen.btM
#krows CertificateChecks.KernelMcLGen.BI CertificateChecks.KernelMcLGen.biM
#krows CertificateChecks.KernelMcLGen.LT CertificateChecks.KernelMcLGen.ltM

#ktbfs CertificateChecks.KernelMcLGen.CT0 275 0 CertificateChecks.KernelMcLGen.lettersM
  CertificateChecks.KernelMcLGen.lv0M
#ktbfs CertificateChecks.KernelMcLGen.CT1 275 3 CertificateChecks.KernelMcLGen.lettersM
  CertificateChecks.KernelMcLGen.lv1M
#ktbfs CertificateChecks.KernelMcLGen.CT2 275 4 CertificateChecks.KernelMcLGen.lettersM
  CertificateChecks.KernelMcLGen.lv2M
#ktbfs CertificateChecks.KernelMcLGen.CT3 275 5 CertificateChecks.KernelMcLGen.lettersM
  CertificateChecks.KernelMcLGen.lv3M
#ktbfs CertificateChecks.KernelMcLGen.CT4 275 1 CertificateChecks.KernelMcLGen.lettersM
  CertificateChecks.KernelMcLGen.lv4M

end
