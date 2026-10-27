module

public import Certificates.Kernel.Ly3085.Omega.Base
public import Certificates.Kernel.SporSch.Ly.BSData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CertificateChecks.KernelSporSch

@[expose] noncomputable def XS : Nat :=
  fMul BC (fMul BC (fMul BC LyBS.A (fMul BC (fMul BC LyBS.B LyBS.A) (fMul BC LyBS.B LyBS.A)))
    LyBS.B) (fMul BC (fMul BC LyBS.A LyBS.B4) (fMul BC LyBS.A LyBS.B4))

@[expose] noncomputable def xPow (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) BC.ONEF (fun _ acc => fMul BC acc XS) n

theorem formA : Nat.beq (fMul BC (fMul BC (fTr LyBS.A) FL) LyBS.A) FL = true := by quickRfl

theorem formB : Nat.beq (fMul BC (fMul BC (fTr LyBS.B) FL) LyBS.B) FL = true := by quickRfl

theorem vXS : fVld BC XS = true := by quickRfl

theorem x67 : Nat.beq (xPow 67) BC.ONEF = true := by quickRfl

theorem neg_x66 : notB (Nat.beq (xPow 66) BC.ONEF) = true := by quickRfl

theorem neg_formA : notB (Nat.beq (fMul BC (fMul BC (fTr LyBS.A) FL) LyBS.A) (Nat.add FL 1)) =
    true := by quickRfl

end CFSG.KD.LyOm

end
