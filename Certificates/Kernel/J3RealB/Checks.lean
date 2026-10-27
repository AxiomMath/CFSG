module

public import Certificates.Kernel.SporSch.J3K426.Checks
public import Certificates.Data.J3RealB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3RealB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSporSch
open CFSG.RankThree.PartTwo.KFacts.K426

@[expose] noncomputable def rbW (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 6156 13)
    (fun j _ ih => strictN ih (fun acc => pcomp 6156 13 (mask 13) (PJ3.S j) acc)) wd

@[expose] noncomputable def rbTest (x g : Nat) : Bool :=
  Nat.beq (pcomp 6156 13 (mask 13) g x) (pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) x x) g)

@[expose] noncomputable def rbChk (wd : List Nat) : Bool :=
  strictB (rbW wd) (rbTest J3KT.X1)

theorem rb_ok : rbChk j3RealBWord = true := by quickRfl

end CertificateChecks.KernelJ3RealB

end
