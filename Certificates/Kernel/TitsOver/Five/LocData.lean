module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.Gen
meta import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import Certificates.Data.Kernel.MaxD2.Gen
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KS.MaxD2 Certificates.MaxD2Perm CFSG.StandardType.TitsFive

meta def cD : Data := lLocalData ()

meta def cpreM : Gen.Pre := Gen.pre cD 11

meta def cngiM : Array (Array Nat) := nGensI cD
meta def crepM : Array (Array Nat) := cpreM.rep
meta def crepiM : Array (Array Nat) := cpreM.repi
meta def cttM : Array (Array Nat) :=
  #[wT cD cD.tW, CFSG.PSL3Four.Native.invTab 1755 (wT cD cD.tW)]
meta def cptM : Array Nat := cD.fpPts.toArray
meta def cfsM : Array Nat := Gen.fpSort cpreM
meta def cksM : Array Nat := Gen.fpKeys cpreM
meta def crbM : Array Nat := Gen.repImgs cD cpreM
meta def chM : Array Nat := Gen.hints cD 11 cpreM
meta def ccnM : Array Nat := Gen.counts cD 11 cpreM
meta def cchM : Array Nat := Gen.centHints cD cpreM
meta def cnhM : Array Nat := Gen.normHints cD cpreM
meta def clM : Array Nat := Gen.labels cD
meta def cmkM : Array Nat := Gen.mkeys cD 11 cpreM
meta def cmiscM : Array Nat := #[Gen.torusPos cD cpreM, Gen.numLabels cD]

end CertificateChecks.KernelTitsOver.Five

public section

#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.CNGI CertificateChecks.KernelTitsOver.Five.cngiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.CREP
  CertificateChecks.KernelTitsOver.Five.crepM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.CREPI
  CertificateChecks.KernelTitsOver.Five.crepiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.CTT CertificateChecks.KernelTitsOver.Five.cttM 11
#krows CertificateChecks.KernelTitsOver.Five.CPT CertificateChecks.KernelTitsOver.Five.cptM
#krows CertificateChecks.KernelTitsOver.Five.CFS CertificateChecks.KernelTitsOver.Five.cfsM
#krowsw CertificateChecks.KernelTitsOver.Five.CKS 11 CertificateChecks.KernelTitsOver.Five.cksM
#krows CertificateChecks.KernelTitsOver.Five.CRB CertificateChecks.KernelTitsOver.Five.crbM
#krows CertificateChecks.KernelTitsOver.Five.CH CertificateChecks.KernelTitsOver.Five.chM
#krows CertificateChecks.KernelTitsOver.Five.CCN CertificateChecks.KernelTitsOver.Five.ccnM
#krows CertificateChecks.KernelTitsOver.Five.CCH CertificateChecks.KernelTitsOver.Five.cchM
#krows CertificateChecks.KernelTitsOver.Five.CNH CertificateChecks.KernelTitsOver.Five.cnhM
#krows CertificateChecks.KernelTitsOver.Five.CL CertificateChecks.KernelTitsOver.Five.clM
#krowsw CertificateChecks.KernelTitsOver.Five.CMK 2048 CertificateChecks.KernelTitsOver.Five.cmkM
#krows CertificateChecks.KernelTitsOver.Five.CMISC CertificateChecks.KernelTitsOver.Five.cmiscM

end
