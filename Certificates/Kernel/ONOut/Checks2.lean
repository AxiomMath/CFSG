module

import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.ONOut.Data
public import Certificates.Data.Kernel.Spor.BytesF

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.ONOut "Certificates/Kernel/ONOut/data/seed.json.gz" 58
  11264094121665876189 (DA1 : List Nat) (DA2 : List Nat)

public noncomputable section

namespace CFSG.KD.ONOut

theorem consts : CFSG.KC.Ord.consts3OK (nat_lit 154) (nat_lit 9) (nat_lit 23716) LO RM CI ONE UP =
    true := by
  quickRfl

theorem ccK : Nat.beq CC (Nat.lor CI (Nat.shiftLeft CI (nat_lit 23716))) = true := by quickRfl

@[expose] def vC (k : Nat) : Bool := VLD (MT k)

theorem mV : Nat.beq (Nat.land (MT (nat_lit 4)) CC) (MT (nat_lit 4)) = true := by quickRfl

theorem mU : Nat.beq (Nat.land (MT (nat_lit 5)) (Nat.lor RM (Nat.shiftLeft RM (nat_lit 23716))))
    (MT (nat_lit 5)) = true := by
  quickRfl

theorem dN : CFSG.KC.ONOut.run27 (nat_lit 1) (nat_lit 23716) (nat_lit 23716) (MT (nat_lit 2))
    ONN0.chars (nat_lit 0) = true := by
  quickRfl

theorem dR : CFSG.KC.ONOut.run27 (nat_lit 1) (nat_lit 23716) (nat_lit 23716) (MT (nat_lit 3))
    ONR.chars (nat_lit 0) = true := by
  quickRfl

theorem dV : CFSG.KC.ONOut.run27 (nat_lit 154) (nat_lit 154) (nat_lit 23716) (MT (nat_lit 4))
    ONV.chars (nat_lit 0) = true := by
  quickRfl

theorem dU : CFSG.KC.ONOut.run27 (nat_lit 1) (nat_lit 154) (nat_lit 23716) (MT (nat_lit 5))
    ONU.chars (nat_lit 0) = true := by
  quickRfl

theorem kW : Nat.beq (MUL WM (MT (nat_lit 4))) (nat_lit 0) = true := by quickRfl

theorem kR : Nat.beq (CFSG.KC.ONOut.addM3 (nat_lit 23716) LO (MUL (MT (nat_lit 3)) WM)
    (MUL (MT (nat_lit 4)) (MT (nat_lit 5)))) ONE = true := by
  quickRfl

theorem sp0 : Nat.beq (CFSG.KC.ONOut.colM3 CC (MT (nat_lit 6)) (nat_lit 0)) (MT (nat_lit 4)) =
    true := by
  quickRfl

@[expose] def spC (i : Nat) : Bool :=
  CFSG.KC.ONOut.spinK MUL (MT 0) (MT 1) (MT 6) CC parF labF (16 * i + 1) (min 16 (153 - 16 * i))

theorem spI : Nat.beq (MUL (MT (nat_lit 7)) (MT (nat_lit 6))) ONE = true := by quickRfl

theorem n2 : Nat.beq (MUL (MT (nat_lit 2)) (MT (nat_lit 2))) NEG = true := by quickRfl

@[expose] def dL (k : Nat) : List Nat := List.range' (32 * k) (min 32 (94 - 32 * k))

@[expose] def d1C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun3 P1 256 24045 154 23716 RM (MT 0) (dL k) (DA1.getD k 0))
    (DA1.getD (k + 1) 0)

@[expose] def d2C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun3 P2 256 24045 154 23716 RM (MT 1) (dL k) (DA2.getD k 0))
    (DA2.getD (k + 1) 0)

theorem d1_end : CFSG.KC.Ord.seedDone (nat_lit 154) VLD (MT (nat_lit 0)) (nat_lit 94867) = true := by
  quickRfl

theorem r1 : CFSG.KS.Bytes.runF P1 (nat_lit 256) (nat_lit 24045) ONSA.chars (nat_lit 0) = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone (nat_lit 154) VLD (MT (nat_lit 1)) (nat_lit 94867) = true := by
  quickRfl

theorem r2 : CFSG.KS.Bytes.runF P2 (nat_lit 256) (nat_lit 24045) ONSB.chars (nat_lit 0) = true := by
  quickRfl

end CFSG.KD.ONOut

#kc_each CFSG.KD.ONOut.vC 0 8

#kc_each CFSG.KD.ONOut.spC 0 10

#kc_each CFSG.KD.ONOut.d1C 0 3

#kc_each CFSG.KD.ONOut.d2C 0 3

namespace CFSG.KD.ONOut

#kc_forall_chunks SP.all (fun i => spC i = true) 10 CFSG.KD.ONOut.spC 1

#kc_forall_chunks D1.all (fun k => d1C k = true) 3 CFSG.KD.ONOut.d1C 1

#kc_forall_chunks D2.all (fun k => d2C k = true) 3 CFSG.KD.ONOut.d2C 1

end CFSG.KD.ONOut

end
