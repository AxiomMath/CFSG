module

public import Certificates.Kernel.K133.GBarChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK133

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.KLie.CT (fget)

@[expose] noncomputable def gbClA (k i : Nat) : Bool :=
  Nat.blt (fget (GB.E i) k 16) GB.N && Nat.beq (GB.T (fget (GB.E i) k 16)) (pc (GB.G k) (GB.T i))

@[expose] noncomputable def gbClI (i : Nat) : Bool := gbClA 3 i && gbClA 9 i && gbClA 10 i

@[expose] noncomputable def gbWK (ws : List Nat) (b : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) b (fun l _ acc => pc (GB.G l) acc) ws

theorem gbCl0 : allBlk 0 gbClI 400 = true := by quickRfl
theorem gbCl1 : allBlk 400 gbClI 400 = true := by quickRfl
theorem gbCl2 : allBlk 800 gbClI 400 = true := by quickRfl
theorem gbCl3 : allBlk 1200 gbClI 400 = true := by quickRfl
theorem gbCl4 : allBlk 1600 gbClI 400 = true := by quickRfl
theorem gbCl5 : allBlk 2000 gbClI 400 = true := by quickRfl
theorem gbCl6 : allBlk 2400 gbClI 400 = true := by quickRfl
theorem gbCl7 : allBlk 2800 gbClI 400 = true := by quickRfl
theorem gbCl8 : allBlk 3200 gbClI 400 = true := by quickRfl
theorem gbCl9 : allBlk 3600 gbClI 400 = true := by quickRfl
theorem gbCl10 : allBlk 4000 gbClI 400 = true := by quickRfl
theorem gbCl11 : allBlk 4400 gbClI 400 = true := by quickRfl
theorem gbCl12 : allBlk 4800 gbClI 400 = true := by quickRfl
theorem gbCl13 : allBlk 5200 gbClI 400 = true := by quickRfl
theorem gbCl14 : allBlk 5600 gbClI 400 = true := by quickRfl
theorem gbCl15 : allBlk 6000 gbClI 400 = true := by quickRfl
theorem gbCl16 : allBlk 6400 gbClI 400 = true := by quickRfl
theorem gbCl17 : allBlk 6800 gbClI 400 = true := by quickRfl
theorem gbCl18 : allBlk 7200 gbClI 400 = true := by quickRfl
theorem gbCl19 : allBlk 7600 gbClI 400 = true := by quickRfl
theorem gbCl20 : allBlk 8000 gbClI 400 = true := by quickRfl
theorem gbCl21 : allBlk 8400 gbClI 400 = true := by quickRfl
theorem gbCl22 : allBlk 8800 gbClI 400 = true := by quickRfl
theorem gbCl23 : allBlk 9200 gbClI 400 = true := by quickRfl
theorem gbCl24 : allBlk 9600 gbClI 400 = true := by quickRfl
theorem gbCl25 : allBlk 10000 gbClI 400 = true := by quickRfl
theorem gbCl26 : allBlk 10400 gbClI 400 = true := by quickRfl
theorem gbCl27 : allBlk 10800 gbClI 400 = true := by quickRfl
theorem gbCl28 : allBlk 11200 gbClI 400 = true := by quickRfl
theorem gbCl29 : allBlk 11600 gbClI 400 = true := by quickRfl
theorem gbCl30 : allBlk 12000 gbClI 400 = true := by quickRfl
theorem gbCl31 : allBlk 12400 gbClI 400 = true := by quickRfl
theorem gbCl32 : allBlk 12800 gbClI 400 = true := by quickRfl
theorem gbCl33 : allBlk 13200 gbClI 400 = true := by quickRfl
theorem gbCl34 : allBlk 13600 gbClI 400 = true := by quickRfl
theorem gbCl35 : allBlk 14000 gbClI 400 = true := by quickRfl

theorem gbT0 : Nat.beq (GB.T 0) (pidn 256 9) = true := by quickRfl

theorem gbCanG : allN 11 (fun k => canonK 256 9 (mask 9) (256 * 9) (GB.G k)) = true := by quickRfl

theorem gbWd0 : Nat.beq (GB.G 0) (gbWK [3] (GB.G 3)) = true := by quickRfl
theorem gbWd1 : Nat.beq (GB.G 1) (gbWK [3] (GB.G 3)) = true := by quickRfl
theorem gbWd2 : Nat.beq (GB.G 2) (gbWK [3] (GB.G 3)) = true := by quickRfl
theorem gbWd4 : Nat.beq (GB.G 4) (gbWK [9, 3, 9, 3, 9, 3, 9, 3, 9, 9] (GB.G 3)) = true := by
  quickRfl
theorem gbWd5 : Nat.beq (GB.G 5) (gbWK [] (GB.G 3)) = true := by quickRfl
theorem gbWd6 :
    Nat.beq (GB.G 6) (gbWK [9, 3, 9, 10, 3, 9, 9, 9, 3, 9, 10, 3, 9] (GB.G 9)) = true := by
  quickRfl
theorem gbWd7 : Nat.beq (GB.G 7) (gbWK [10, 9, 3, 9, 10, 3, 9] (GB.G 9)) = true := by quickRfl
theorem gbWd8 : Nat.beq (GB.G 8) (gbWK [9, 3, 9, 10, 3, 9, 10, 3] (GB.G 9)) = true := by quickRfl

end CertificateChecks.KernelK133

end
