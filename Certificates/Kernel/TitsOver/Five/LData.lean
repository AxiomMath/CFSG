module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenPair
meta import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import Certificates.Data.Kernel.MaxD2.GenPair
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KS.MaxD2 Certificates.MaxD2Perm CFSG.StandardType.TitsFive

meta def lpreM : Gen.Pre := Gen.pre lMaxData 11

meta def lgiM : Array (Array Nat) := nGensI lMaxData
meta def lrepM : Array (Array Nat) := lpreM.rep
meta def lrepiM : Array (Array Nat) := lpreM.repi
meta def lptM : Array Nat := lMaxData.fpPts.toArray
meta def lfsM : Array Nat := Gen.fpSort lpreM
meta def lksM : Array Nat := Gen.fpKeys lpreM
meta def lrbM : Array Nat := Gen.repImgs lMaxData lpreM
meta def lhM : Array Nat := Gen.hints lMaxData 11 lpreM
meta def lcnM : Array Nat := Gen.counts lMaxData 11 lpreM
meta def llM : Array Nat := Gen.labels lMaxData
meta def lmkM : Array Nat := Gen.mkeys lMaxData 11 lpreM
meta def lmiscM : Array Nat := #[Gen.numLabels lMaxData]

meta def lpairs : List (Nat × Nat) :=
  (Gen.pairList lmkM.size).filter fun (i, j) => lmkM[i]! == lmkM[j]!

meta def lpqM : Array Nat :=
  (List.range 49).toArray.map fun c =>
    (lpairs.findIdx? fun (i, j) => 7 * i + j == c).getD 0

meta def lrb2M : Array Nat :=
  (lpairs.toArray.map fun (_, j) =>
    (lMaxData.fpPts.map fun b => (lpreM.rep[j]!)[b]!).toArray).flatten

meta def lh2M : Array Nat :=
  let ks := Gen.fpKeys lpreM
  (lpairs.toArray.map fun (i, j) =>
    lpreM.nT.map fun a => Gen.hint lMaxData 11 lpreM ks lpreM.rep[j]! lpreM.repi[i]! a).flatten

meta def lsmM : Array Nat :=
  #[(CFSG.PSL3Four.Native.indexOf lpreM.nT).getD
    (CFSG.StandardType.TitsOvergroup.repT pairData)[24]! 0]

end CertificateChecks.KernelTitsOver.Five

public section

#krows CertificateChecks.KernelTitsOver.Five.LSM CertificateChecks.KernelTitsOver.Five.lsmM

#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.LGI CertificateChecks.KernelTitsOver.Five.lgiM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.LREP
  CertificateChecks.KernelTitsOver.Five.lrepM 11
#kmisc_packarrs CertificateChecks.KernelTitsOver.Five.LREPI
  CertificateChecks.KernelTitsOver.Five.lrepiM 11
#krows CertificateChecks.KernelTitsOver.Five.LPT CertificateChecks.KernelTitsOver.Five.lptM
#krows CertificateChecks.KernelTitsOver.Five.LFS CertificateChecks.KernelTitsOver.Five.lfsM
#krowsw CertificateChecks.KernelTitsOver.Five.LKS 33 CertificateChecks.KernelTitsOver.Five.lksM
#krows CertificateChecks.KernelTitsOver.Five.LRB CertificateChecks.KernelTitsOver.Five.lrbM
#krows CertificateChecks.KernelTitsOver.Five.LH CertificateChecks.KernelTitsOver.Five.lhM
#krows CertificateChecks.KernelTitsOver.Five.LCN CertificateChecks.KernelTitsOver.Five.lcnM
#krows CertificateChecks.KernelTitsOver.Five.LL CertificateChecks.KernelTitsOver.Five.llM
#krowsw CertificateChecks.KernelTitsOver.Five.LMK 128 CertificateChecks.KernelTitsOver.Five.lmkM
#krows CertificateChecks.KernelTitsOver.Five.LMISC CertificateChecks.KernelTitsOver.Five.lmiscM
#krows CertificateChecks.KernelTitsOver.Five.LPQ CertificateChecks.KernelTitsOver.Five.lpqM
#krows CertificateChecks.KernelTitsOver.Five.LRB2 CertificateChecks.KernelTitsOver.Five.lrb2M
#krows CertificateChecks.KernelTitsOver.Five.LH2 CertificateChecks.KernelTitsOver.Five.lh2M

end
