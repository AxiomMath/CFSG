
module

public import Certificates.Kernel.SporSch.HN.Invol2099K
public import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Data.Kernel.SporSch.HNF5Dig
meta import CFSG.Sporadic.HNSchreier.InvolCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.HNRoot CFSG.Sporadic.HNSchreier.Data.rootDigits
#ks_chars CertificateChecks.KernelSporSch.HNNorm CFSG.Sporadic.HNSchreier.LocalData.normalizerPayload
#ks_chars CertificateChecks.KernelSporSch.HNInv CFSG.Sporadic.HNSchreier.LocalData.involutionPayload

namespace CertificateChecks.KernelSporSch.HNInvol

open CFSG.Sporadic.HNSchreier.Native

meta def labs : List Nat := labMasks.toList

meta def taus : List Nat := tauIdx.toList

end CertificateChecks.KernelSporSch.HNInvol

#kss_ntree CertificateChecks.KernelSporSch.HNLab CertificateChecks.KernelSporSch.HNInvol.labs
#kss_ntree CertificateChecks.KernelSporSch.HNTau CertificateChecks.KernelSporSch.HNInvol.taus

namespace CertificateChecks.KernelSporSch.HNInvol

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier
open CertificateChecks.KernelSporSch

theorem payS : pay5K (sx 35) HNNorm.chars = true := by quickRfl
theorem payC : pay5K (sx 36) HNInv.chars = true := by quickRfl
theorem root : dig5K (sx 57 0) HNRoot.chars = true := by quickRfl

theorem labEq : allN 462 (fun j => Nat.beq (HNLab j) (maskOfList (LocalData.labels[j]!))) = true := by
  quickRfl

@[expose] noncomputable def tgt (i : Nat) : Nat := canonMask (permMask tauArr (HNLab i))

theorem tauOK : allN 462 (fun i => strictB (tgt i) (fun t => bAnd(Nat.blt (HNTau i) 462,
    bAnd(Nat.beq (HNLab (HNTau i)) t, allN (HNTau i) (fun j => Bool.not (Nat.beq (HNLab j) t)))))) =
      true := by
  quickRfl

theorem cx0 : allBlk 0 (fun i => Nat.beq (vm5 (sx 40) (sx 58 i)) (sx 58 (HNTau i))) 231 = true := by
  quickRfl
theorem cx1 : allBlk 231 (fun i => Nat.beq (vm5 (sx 40) (sx 58 i)) (sx 58 (HNTau i))) 231 =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNInvol

end
