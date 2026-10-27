module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def outerK (i j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) pid (fun k _ => wO ((cent0Words.getD i []).getD k [])) j

theorem kOuter : List.all [3, 4] (fun i => bAnd(allN 4 (fun k =>
    bAnd(lettersK 17 ((cent0Words.getD i []).getD k []), cn (outerK i (Nat.succ k)))),
    allN 5 fun a => allN a fun b => bIf(Nat.beq (outerK i a) (outerK i b), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
