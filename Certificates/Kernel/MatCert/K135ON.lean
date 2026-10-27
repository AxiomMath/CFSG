module

public import Certificates.Kernel.MatCert.Fp
public import CFSG.RankThree.PartTwo.Sec13.K135ONData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

#ks_chars CertificateChecks.KernelMC.ONS1 CFSG.Blueprint.NativeSporadic.ONSeed1
#ks_chars CertificateChecks.KernelMC.ONS2 CFSG.Blueprint.NativeSporadic.ONSeed2

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native

@[expose] noncomputable def onL : Nat := rep1 11 23716

@[expose] noncomputable def onH : Nat := Nat.shiftLeft onL 10

@[expose] noncomputable def onCM : Nat := Nat.mul 2047 (rep1 1694 154)

@[expose] noncomputable def onRM : Nat := Nat.sub (Nat.shiftLeft 1 1694) 1

@[expose] noncomputable def onONE : Nat := rep1 1705 154

@[expose] noncomputable def onLV : Nat := rep1 11 154

@[expose] noncomputable def onHV : Nat := Nat.shiftLeft onLV 10

noncomputable abbrev O3 : Ops Nat Nat := opsFpK 3 11 1694 154 8 onL onH onCM onRM onONE

theorem onConsts : constsOK 3 11 1694 154 8 onL onH onCM onRM onONE onLV onHV = true := by
  quickRfl

@[expose] noncomputable def payON (cs : List Char) : Nat := payRunP 3 154 11 1694 cs 0 0 0

@[expose] noncomputable def vldON (X : Nat) : Bool := validM 3 (154 * 1694) onL onH X

theorem k135ON_K : forceB (payON ONS1.chars) (fun A => forceB (payON ONS2.chars) fun B =>
    vldON A && vldON B && mcertN O3 A B CFSG.RankThree.PartTwo.Sec13.F135Last.K135.onCert) =
    true := by
  quickRfl

theorem k135ON_neg : (forceB (payON ONS1.chars) fun A => forceB (payON ONS2.chars) fun B =>
    !mcertN O3 A B { CFSG.RankThree.PartTwo.Sec13.F135Last.K135.onCert with
      facts := [.eq [(0, 1)] [(1, 1)]] }) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
