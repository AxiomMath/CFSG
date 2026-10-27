module

public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.SporSch.LyMat
public import Certificates.Data.GH74.LyGen45
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyGen45

open CFSG.KC.Ord CFSG.KD.OrdLy CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch.LyBS
open CFSG.Sporadic.Ly.Gen CFSG.Sporadic.Ly.Gen45

@[expose] noncomputable def letK (z : Int) : Nat :=
  if z = 1 ∨ z = -1 then A else if z = 2 then B else B4

@[expose] noncomputable def TK : Nat := genWords[5]!.foldr (fun z P => mul (letK z) P) ONE

@[expose] noncomputable def DK : Nat := powR 5 12 1332 111 8 L H CM RM ONE (mul A TK) 3

@[expose] noncomputable def ent0 (X j : Nat) : Nat := Nat.land (Nat.shiftRight X (12 * j)) 4095

theorem b_ok : (genWords[5]!.all (fun z => decide (z.natAbs ≤ 2)) && Nat.beq (mul DK DK) ONE &&
    ent0 DK 2 % 5 != 0 && ent0 DK 0 % 5 != ent0 A 0 % 5 && Nat.beq (mul A DK) (mul DK A) &&
    Nat.beq (mul TK DK) (mul DK TK)) = true := by
  quickRfl

end CertificateChecks.KernelLyGen45

end
