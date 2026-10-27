module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24R2W.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Kernel.Sporadic.Fi24K.K2077
public import Certificates.Data.Kernel.Spor.Fi24F4J
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_json_gz CFSG.KD.Fi24F4.S "Certificates/Kernel/Sporadic/Fi24F4/data/f4s.json.gz" 1915
  17055141734951770022
  (sig : List Nat)

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fi24F4J CFSG.KC.Fi24R2W
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi24R2W

@[expose] noncomputable def packL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 9))) l

@[expose] noncomputable def sigP : Nat := packL S.sig

@[expose] noncomputable def sigc : Bool :=
  allN 504 (fun j => andB (Nat.blt (nthV S.sig j) 504) (andB
    (Nat.beq (pg 9 (mask 9) sigP j) (nthV S.sig j))
    (Nat.beq (CFSG.KC.Fi24NetPt.ptF CFSG.KD.Fi24Kit.NT (fpt FP.F j)) (fpt FP.F (nthV S.sig j)))))

@[expose] noncomputable def sftc : Bool :=
  andB (canonK 504 9 (mask 9) (504 * 9) sigP)
    (Bool.not (siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24KC.LR Fi24KC.TRI Fi24KC.BP 7 0 sigP))

end CFSG.KD.Fi24F4

namespace CFSG.KD.Fi24F4.Ck

theorem sig : CFSG.KD.Fi24F4.sigc = true := by quickRfl

theorem sft : CFSG.KD.Fi24F4.sftc = true := by quickRfl

end CFSG.KD.Fi24F4.Ck

end
