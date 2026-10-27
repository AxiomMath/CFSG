module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Data.Kernel.SporSch.LyMat
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Asc83Table.HeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

#ks_chars CertificateChecks.KernelMC.HeS1 CFSG.Blueprint.NativeSporadic.HeSeed1
#ks_chars CertificateChecks.KernelMC.HeS2 CFSG.Blueprint.NativeSporadic.HeSeed2

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native

@[expose] noncomputable def heL : Nat := rep1 12 2500

@[expose] noncomputable def heH : Nat := Nat.shiftLeft heL 11

@[expose] noncomputable def heCM : Nat := Nat.mul 4095 (rep1 600 50)

@[expose] noncomputable def heRM : Nat := Nat.sub (Nat.shiftLeft 1 600) 1

@[expose] noncomputable def heONE : Nat := rep1 612 50

@[expose] noncomputable def heLV : Nat := rep1 12 50

@[expose] noncomputable def heHV : Nat := Nat.shiftLeft heLV 11

noncomputable abbrev O7 : Ops Nat Nat := opsFpK 7 12 600 50 8 heL heH heCM heRM heONE

theorem heConsts : constsOK 7 12 600 50 8 heL heH heCM heRM heONE heLV heHV = true := by
  quickRfl

@[expose] noncomputable def payHe (cs : List Char) : Nat := payRunP 7 50 12 600 cs 0 0 0

@[expose] noncomputable def vldHe (X : Nat) : Bool := validM 7 (50 * 600) heL heH X

theorem he_K : forceB (payHe HeS1.chars) (fun A => forceB (payHe HeS2.chars) fun B =>
    vldHe A && vldHe B && mcertN O7 A B CFSG.RankThree.Asc83Table.He.heCert) = true := by
  quickRfl

theorem he_neg : (forceB (payHe HeS1.chars) fun A => forceB (payHe HeS2.chars) fun B =>
    !mcertN O7 A B { CFSG.RankThree.Asc83Table.He.heCert with facts := [.ord 0 3] }) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
