module

public import CFSG.Certificates.Kernel.Orders.Cert
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi23Br.Data
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Spor.BytesF
public import Certificates.Data.CFSGNative.Fi23.Data

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CFSG.KD.BrFi23 "Certificates/Kernel/Sporadic/Fi23Br/data/seed.json.gz" 12459
  9034109315379265453 (DA1 : List Nat) (DA2 : List Nat)

#ks_chars CFSG.KD.BrFi23.Fi23SeedA CFSG.Sporadic.Fi23.Native.seedA

#ks_chars CFSG.KD.BrFi23.Fi23SeedB CFSG.Sporadic.Fi23.Native.seedB

namespace CFSG.KD.BrFi23

@[expose] def dL (k : Nat) : List Nat := List.range' (16 * k) (min 16 (255 - 16 * k))

@[expose] noncomputable def d1C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun P1 256 65042 3 253 11 2783 RM (RB 11) (dL k) (DA1.getD k 0))
    (DA1.getD (k + 1) 0)

@[expose] noncomputable def d2C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun P2 256 65042 3 253 11 2783 RM (RB 12) (dL k) (DA2.getD k 0))
    (DA2.getD (k + 1) 0)

theorem d1_end : CFSG.KC.Ord.seedDone (nat_lit 253) (CFSG.KC.Ord.validM (nat_lit 3) (nat_lit 704099)
    L H) (RB (nat_lit 11)) (nat_lit 256039) = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone (nat_lit 253) (CFSG.KC.Ord.validM (nat_lit 3) (nat_lit 704099)
    L H) (RB (nat_lit 12)) (nat_lit 256039) = true := by
  quickRfl

theorem seed1_run : CFSG.KS.Bytes.runF P1 256 65042 Fi23SeedA.chars 0 = true := by quickRfl

theorem seed2_run : CFSG.KS.Bytes.runF P2 256 65042 Fi23SeedB.chars 0 = true := by quickRfl

end CFSG.KD.BrFi23

#kc_each CFSG.KD.BrFi23.d1C 0 16

#kc_each CFSG.KD.BrFi23.d2C 0 16

namespace CFSG.KD.BrFi23

#kc_forall_chunks D1.all (fun k => d1C k = true) 16 CFSG.KD.BrFi23.d1C 1

#kc_forall_chunks D2.all (fun k => d2C k = true) 16 CFSG.KD.BrFi23.d2C 1

end CFSG.KD.BrFi23

end
