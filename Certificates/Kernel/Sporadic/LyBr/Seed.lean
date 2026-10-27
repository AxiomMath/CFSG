module

public import CFSG.Certificates.Kernel.Orders.Cert
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.LyBr.Data
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Spor.Bytes
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CFSG.KD.BrLy "Certificates/Kernel/Sporadic/LyBr/data/seed.json.gz" 1134
  17086380611077481029 (DA1 : List Nat) (DA2 : List Nat)

#ks_chars CFSG.KD.BrLy.LySeedA CFSG.Blueprint.NativeSporadic.LySeed1

#ks_chars CFSG.KD.BrLy.LySeedB CFSG.Blueprint.NativeSporadic.LySeed2

namespace CFSG.KD.BrLy

@[expose] def dL (k : Nat) : List Nat := List.range' (16 * k) (min 16 (71 - 16 * k))

@[expose] noncomputable def d1C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun P1 256 18063 5 111 12 1332 RM (RH 314) (dL k) (DA1.getD k 0))
    (DA1.getD (k + 1) 0)

@[expose] noncomputable def d2C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun P2 256 18063 5 111 12 1332 RM (RH 3890) (dL k) (DA2.getD k 0))
    (DA2.getD (k + 1) 0)

theorem d1_end : CFSG.KC.Ord.seedDone 111 (CFSG.KC.Ord.validM 5 147852 L H) (RH 314) 49287 = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone 111 (CFSG.KC.Ord.validM 5 147852 L H) (RH 3890) 49287 = true := by
  quickRfl

theorem seed1_bytes : CFSG.KS.Bytes.bytesEqK LySeedA.chars P1 256 18063 = true := by quickRfl

theorem seed2_bytes : CFSG.KS.Bytes.bytesEqK LySeedB.chars P2 256 18063 = true := by quickRfl

end CFSG.KD.BrLy

#kc_each CFSG.KD.BrLy.d1C 0 5

#kc_each CFSG.KD.BrLy.d2C 0 5

namespace CFSG.KD.BrLy

#kc_forall_chunks D1.all (fun k => d1C k = true) 5 CFSG.KD.BrLy.d1C 1

#kc_forall_chunks D2.all (fun k => d2C k = true) 5 CFSG.KD.BrLy.d2C 1

end CFSG.KD.BrLy

end
