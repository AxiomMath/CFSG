
module

public import Certificates.Data.Kernel.LyFive
public import Certificates.Kernel.Ly3085.Omega.Base
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.LyFive "Certificates/Kernel/LyFiveL1/data/five.json.gz" 1517155 13929500547944207317
  (LT : List Nat) (AB : List Nat) (TB : List Nat) (PB : List Nat) (NT : Nat) (CJ : List Nat)
  (BW : List (List Nat)) (BT : List Nat) (RT : List Nat) (GX : List Nat) (GY : List Nat)
  (TG : List (List Nat))

public section

namespace CFSG.KD.LyFive

open CertificateChecks.KernelSporSch.LySv (AF AI)

@[expose] noncomputable def UG (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 27), LT.getD l 0,
    nIf(Nat.blt l (nat_lit 34), AF (Nat.sub l (nat_lit 27)), AI (Nat.sub l (nat_lit 34))))

@[expose] noncomputable def GA (l : Nat) : Nat := AB.getD l 0

@[expose] noncomputable def treeChk (k : Nat) : Bool :=
  CFSG.KC.LyFive.treeBlk CFSG.KD.LyOm.BC UG TB CJ RT NT k

@[expose] noncomputable def baseChk (c : Nat) : Bool := CFSG.KC.LyFive.baseBlk CFSG.KD.LyOm.BC UG PB c

end CFSG.KD.LyFive

end
