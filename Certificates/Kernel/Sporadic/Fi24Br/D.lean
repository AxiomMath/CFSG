module

public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Kernel.Sporadic.Fi24Br.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.BrFi24 "Certificates/Kernel/Sporadic/Fi24Br/data/seed.json.gz" 6828
  7694364780480428996 (DA1 : List Nat) (DA2 : List Nat)

public noncomputable section

namespace CFSG.KD.BrFi24

@[expose] def dL (k : Nat) : List Nat := List.range' (256 * k) (min 256 (2414 - 256 * k))

@[expose] def d1C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun3 P1 256 617792 781 609961 RM (RB 23) (dL k) (DA1.getD k 0))
    (DA1.getD (k + 1) 0)

@[expose] def d2C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun3 P2 256 617792 781 609961 RM (RB 24) (dL k) (DA2.getD k 0))
    (DA2.getD (k + 1) 0)

theorem d1_end : CFSG.KC.Ord.seedDone (nat_lit 781) VLD (RB (nat_lit 23)) (nat_lit 2439847) = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone (nat_lit 781) VLD (RB (nat_lit 24)) (nat_lit 2439847) = true := by
  quickRfl

end CFSG.KD.BrFi24

#kc_each CFSG.KD.BrFi24.d1C 0 10

#kc_each CFSG.KD.BrFi24.d2C 0 10

namespace CFSG.KD.BrFi24

#kc_forall_chunks D1.all (fun k => d1C k = true) 10 CFSG.KD.BrFi24.d1C 1

#kc_forall_chunks D2.all (fun k => d2C k = true) 10 CFSG.KD.BrFi24.d2C 1

end CFSG.KD.BrFi24

end
