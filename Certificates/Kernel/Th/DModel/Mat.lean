module

public import CFSG.Certificates.Kernel.Th.S.SurjS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Surj_const
public import CFSG.Sporadic.Th.Recog.JLettersInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Recognition.PresentedWordsClosure
public import CFSG.Sporadic.Th.Max3.CentA

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.DModel

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.KD.ThS CFSG.Sporadic.Th.Recog

@[expose] noncomputable def codeW (w : List (Fin 8 × Bool)) : List Nat :=
  w.map fun l => Nat.add (Nat.mul 2 l.1.val) (Bool.rec (motive := fun _ => Nat) 1 0 l.2)

@[expose] noncomputable def duQ : Nat :=
  wordV CFSG.KD.ThSj.RB c rm (codeW (hswWord 3 ++ hswWord 7)) ONE

theorem k_du : Nat.beq (mulB c rm duQ (mulB c rm duQ (mulB c rm duQ (mulB c rm duQ
    (mulB c rm duQ duQ))))) ONE = true := by
  quickRfl

end CertificateChecks.KernelTh.DModel

end
