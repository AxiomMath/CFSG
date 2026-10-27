module

public import Certificates.Data.Kernel.PCentSet
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Kernel.G24Th799103.TGData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

#kc_repo #kc_json_gz CertificateChecks.KernelG24Th
  "Certificates/Kernel/G24Th799103/data/inv.json.gz" 1146006 9432617220002638142
  (X0 : Nat) (DM : Nat) (FM : Nat) (EM : Nat) (P0 : List (Nat × Nat × Nat × Nat)) (HG : List Nat)
  (HT : List Nat) (KG : List Nat) (KT : List Nat) (NG : List Nat) (NT : List Nat)
  (SR : List (Nat × Nat × Nat × Nat)) (SF : List (Nat × Nat × Nat × Nat))
  (NL : List (Nat × Nat × Nat × Nat))

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask)
open CertificateChecks.KernelG24.Tri27206

@[expose] noncomputable def mulG (x y : Nat) : Nat := pcomp 1365 11 (mask 11) x y

@[expose] noncomputable def commG (x y : Nat) : Bool := Nat.beq (mulG x y) (mulG y x)

@[expose] noncomputable def rG (k : Nat) : Nat := [LC.S 0, LC.S 1, TG.F 2].getD k (nat_lit 0)

@[expose] noncomputable def inDK (g : Nat) : Bool :=
  CFSG.KS.Prim.canonK 1365 11 (mask 11) (1365 * 11) g &&
    CFSG.KS.Raw.siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0 g

@[expose] noncomputable def inRK (g t : Nat) : Bool :=
  cond (Nat.beq t 0) (inDK g) (inDK (mulG g (TG.F 2)))

@[expose] noncomputable def hG (k : Nat) : Nat := HG.getD k (nat_lit 0)

@[expose] noncomputable def kG (k : Nat) : Nat := KG.getD k (nat_lit 0)

@[expose] noncomputable def nG (k : Nat) : Nat := NG.getD k (nat_lit 0)

@[expose] noncomputable def fixMK (g M : Nat) : Bool :=
  allN 1365 (fun i => Bool.beq (Nat.testBit M i) (Nat.beq (pg 11 (mask 11) g i) i))

@[expose] noncomputable def fix2MK (g h M : Nat) : Bool :=
  allN 1365 (fun i => Bool.beq (Nat.testBit M i)
    (Nat.beq (pg 11 (mask 11) g i) i && Nat.beq (pg 11 (mask 11) h i) i))

@[expose] noncomputable def popK (M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => cond (Nat.testBit M i) (Nat.succ acc) acc) 1365

@[expose] noncomputable def commPt (x y : Nat) : Bool :=
  allN 1365 (fun i => Nat.beq (pg 11 (mask 11) x (pg 11 (mask 11) y i))
    (pg 11 (mask 11) y (pg 11 (mask 11) x i)))

@[expose] noncomputable def invPt (y : Nat) : Bool :=
  allN 1365 (fun i => Nat.beq (pg 11 (mask 11) y (pg 11 (mask 11) y i)) i)

@[expose] noncomputable def invT (y : Nat) : Bool :=
  !(commPt y (TG.F 0) && commPt y (TG.F 1) && invPt y) ||
    Nat.beq y (pidn 1365 11) || Nat.beq y (TG.F 2)

@[expose] def bumpHead (R : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat) :=
  match R with
  | [] => []
  | r :: t => (r.1 + 1, r.2) :: t

end CertificateChecks.KernelG24Th

end
