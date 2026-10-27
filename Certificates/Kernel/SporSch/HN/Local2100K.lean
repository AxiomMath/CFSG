
module

public import Certificates.Kernel.SporSch.HN.Invol2099T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNLocal

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNInvol

@[expose] noncomputable def imgB (k : Nat) (l : Array Nat) (i : Nat) : Bool :=
  Nat.beq (vm5 (sx k) (sx 58 i)) (sx 58 l[i]!)

@[expose] noncomputable def distB (i : Nat) : Bool :=
  allN i (fun j => Bool.not (Nat.beq (sx 58 j) (sx 58 i)))

theorem lp1a : allBlk 0 (imgB 21 LocalData.lperm1) 231 = true := by quickRfl
theorem lp1b : allBlk 231 (imgB 21 LocalData.lperm1) 231 = true := by quickRfl
theorem lp2a : allBlk 0 (imgB 22 LocalData.lperm2) 231 = true := by quickRfl
theorem lp2b : allBlk 231 (imgB 22 LocalData.lperm2) 231 = true := by quickRfl

theorem dist0 : allBlk 0 distB 231 = true := by quickRfl
theorem dist1 : allBlk 231 distB 231 = true := by quickRfl

theorem neg_lp1 : Bool.not (imgB 21 LocalData.lperm2 0) = true := by quickRfl
theorem neg_lp2 : Bool.not (imgB 22 LocalData.lperm1 0) = true := by quickRfl
theorem neg_dist : Bool.not (allN 2 (fun j => Bool.not (Nat.beq (sx 58 0) (sx 58 j)))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNLocal

end
