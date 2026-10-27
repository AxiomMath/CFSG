module

public import Certificates.Data.Kernel.PCentExt
public import Certificates.Data.Kernel.PackSet
public import Certificates.Kernel.G24Th799103.InvData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

#kc_repo #kc_json_gz CertificateChecks.KernelG24Th
  "Certificates/Kernel/G24Th799103/data/basic.json.gz" 186291 11815260201103035805
  (WT : List Nat) (TT : Nat) (E9 : List Nat) (PL : List (Nat × Nat × Nat × Nat)) (PO : Nat)
  (SQ : List Nat) (CL : List Nat) (CJ : List Nat)

open CFSG.KC.Enum (pg pidn allN)
open CFSG.KS (mask)

@[expose] noncomputable def wT (k : Nat) : Nat := WT.getD k (nat_lit 0)

@[expose] noncomputable def e9 (k : Nat) : Nat := E9.getD k (nat_lit 0)

@[expose] noncomputable def pG (k : Nat) : Nat := TG.F (Nat.add 8 k)

@[expose] noncomputable def dK (k : Nat) : Nat :=
  [TG.F 10, pidn 1365 11, TG.F 11, TG.F 12].getD k (nat_lit 0)

@[expose] noncomputable def pL (i : Nat) : Nat := (PL.getD i (0, 0, 0, 0)).1

@[expose] noncomputable def powG (g e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 1365 11) (fun _ acc => mulG g acc) e

@[expose] noncomputable def cubePt (x : Nat) : Bool :=
  allN 1365 (fun i => Nat.beq (pg 11 (mask 11) x (pg 11 (mask 11) x (pg 11 (mask 11) x i))) i)

@[expose] noncomputable def cjPair (C : List Nat) (i j : Nat) : Bool :=
  (List.range 4).any fun k => Nat.blt (C.getD (Nat.add (Nat.mul 27 k) i) 9) 9 &&
    Nat.blt (C.getD (Nat.add (Nat.mul 27 k) j) 9) 9

@[expose] noncomputable def pairsK (C : List Nat) : Bool :=
  allN 27 fun i => allN 27 fun j =>
    !(Nat.beq (pg 11 (mask 11) (pL i) (pg 11 (mask 11) (pL j) PO))
      (pg 11 (mask 11) (pL j) (pg 11 (mask 11) (pL i) PO))) ||
      Nat.beq (pL i) (pidn 1365 11) || Nat.beq (pL j) (pidn 1365 11) || Nat.beq j i ||
      Nat.beq j (SQ.getD i 0) || cjPair C i j

end CertificateChecks.KernelG24Th

end
