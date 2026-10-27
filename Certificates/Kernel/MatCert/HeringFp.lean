module

public import Certificates.Kernel.MatCert.Fp
public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourHeData
public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourJ2Data
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

#ks_chars CertificateChecks.KernelMC.J2S1 CFSG.Blueprint.NativeSporadic.J2Seed1
#ks_chars CertificateChecks.KernelMC.J2S2 CFSG.Blueprint.NativeSporadic.J2Seed2

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native

theorem fourHe_K : forceB (payHe HeS1.chars) (fun A => forceB (payHe HeS2.chars) fun B =>
    vldHe A && vldHe B && mcertN O7 A B CFSG.RankThree.PartTwo.Sec21.Hering214.FourHe.cert) =
    true := by
  quickRfl

theorem fourHe_neg : (forceB (payHe HeS1.chars) fun A => forceB (payHe HeS2.chars) fun B =>
    !mcertN O7 A B { CFSG.RankThree.PartTwo.Sec21.Hering214.FourHe.cert with
      facts := [.eq [(0, 1)] [(1, 1)]] }) = true := by
  quickRfl

@[expose] noncomputable def j2L : Nat := rep1 12 196

@[expose] noncomputable def j2H : Nat := Nat.shiftLeft j2L 11

@[expose] noncomputable def j2CM : Nat := Nat.mul 4095 (rep1 168 14)

@[expose] noncomputable def j2RM : Nat := Nat.sub (Nat.shiftLeft 1 168) 1

@[expose] noncomputable def j2ONE : Nat := rep1 180 14

@[expose] noncomputable def j2LV : Nat := rep1 12 14

@[expose] noncomputable def j2HV : Nat := Nat.shiftLeft j2LV 11

noncomputable abbrev O5 : Ops Nat Nat := opsFpK 5 12 168 14 8 j2L j2H j2CM j2RM j2ONE

theorem j2Consts : constsOK 5 12 168 14 8 j2L j2H j2CM j2RM j2ONE j2LV j2HV = true := by
  quickRfl

@[expose] noncomputable def payJ2 (cs : List Char) : Nat := payRunP 5 14 12 168 cs 0 0 0

@[expose] noncomputable def vldJ2 (X : Nat) : Bool := validM 5 (14 * 168) j2L j2H X

theorem fourJ2_K : forceB (payJ2 J2S1.chars) (fun A => forceB (payJ2 J2S2.chars) fun B =>
    vldJ2 A && vldJ2 B && mcertN O5 A B CFSG.RankThree.PartTwo.Sec21.Hering214.FourJ2.cert) =
    true := by
  quickRfl

theorem fourJ2_neg : (forceB (payJ2 J2S1.chars) fun A => forceB (payJ2 J2S2.chars) fun B =>
    !mcertN O5 A B { CFSG.RankThree.PartTwo.Sec21.Hering214.FourJ2.cert with
      facts := [.ord 0 3] }) = true := by
  quickRfl

theorem fourJ2_neg_swap : (forceB (payJ2 J2S1.chars) fun A => forceB (payJ2 J2S2.chars) fun B =>
    !mcertN O5 B A CFSG.RankThree.PartTwo.Sec21.Hering214.FourJ2.cert) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
