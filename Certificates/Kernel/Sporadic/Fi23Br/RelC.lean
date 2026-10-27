module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.Fi23Br.Data
public import Certificates.Kernel.Sporadic.Fi23Br.Words
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.BrFi23 "Certificates/Kernel/Sporadic/Fi23Br/data/segs.json.gz" 595
  9237144184899505328 (SG : List (List Nat))

public noncomputable section

namespace CFSG.KD.BrFi23

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RB (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253)
    (nat_lit 8) L H CM RM) relsX (nat_lit 12) ONE r

@[expose] def stM (s : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (MT (Nat.sub s 1)) ONE (Nat.beq s 0)

@[expose] def sg (i c : Nat) : Nat := List.getD (List.getD SG i []) c 0

@[expose] def rsC (i : Nat) : Bool :=
  CFSG.KC.Ord.relSegOK RB (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253)
    (nat_lit 8) L H CM RM) relsX ONE (nat_lit 12) (sg i 0) (sg i 1) (sg i 2) (stM (sg i 3))
    (stM (sg i 4))

end CFSG.KD.BrFi23

end
