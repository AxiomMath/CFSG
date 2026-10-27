module

public import Certificates.Data.Kernel.L43Q8.Defs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelL43Q8.TT "Certificates/Kernel/L43Q8/data/pts.bin"
  4 8 115792089237316195423570985008687907853269984665640564039457584007913129639935 16384
  8235746391845461870

#kc_repo #kc_blocked_root CertificateChecks.KernelL43Q8.OT "Certificates/Kernel/L43Q8/data/tab.bin"
  6 4 65535 8304 4741299932468661623

namespace CertificateChecks.KernelL43Q8

open CFSG.KD.L43Q8

@[expose] noncomputable def G (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 342941147431063163152168562476491800608
      83078180795327658557562461748199936 (Nat.beq k 2))
    (Bool.rec (motive := fun _ => Nat) 21267668214970675766071393953557643280
      21267668214987601059587392088776507394 (Nat.beq k 0))
    (Nat.blt k 2)

@[expose] def T0Q : Nat := 42535336429955858070129097172216446977

@[expose] def Q1AQ : Nat := 21267668214970675766071393953557643280

@[expose] def Q1BQ : Nat := 21267668214990018911226621347126902801

@[expose] def Q2AQ : Nat := 2658780510142833004239108197349064705

@[expose] def Q2BQ : Nat := 23926793526074352703001438727045120001

@[expose] def WCQ : Nat := 42535985467082518345511109577507143682

@[expose] noncomputable def T (i : Nat) : Nat := TT i

@[expose] noncomputable def E (i k : Nat) : Nat := OT (Nat.add (Nat.mul 4 i) k)

@[expose] noncomputable def PA (i : Nat) : Nat := OT (Nat.add 2048 i)

@[expose] noncomputable def LA (i : Nat) : Nat := OT (Nat.add 2560 i)

@[expose] noncomputable def SO (i : Nat) : Nat := OT (Nat.add 3072 i)

@[expose] noncomputable def SOI (i : Nat) : Nat := OT (Nat.add 3584 i)

@[expose] noncomputable def II (a : Nat) : Nat := OT (Nat.add 4096 a)

@[expose] noncomputable def l43q8Blk (q : Nat) : Bool :=
  blkQ 4 512 G T E PA LA SO SOI (Nat.mul 64 q) 64

@[expose] noncomputable def l43q8Pr (q : Nat) : Bool :=
  CFSG.KC.Enum.allBlk (Nat.mul 4 q) (fun a => CFSG.KC.Enum.strictB a fun a =>
    CFSG.KC.Enum.strictB (T (II a)) fun A => CFSG.KC.Enum.allBlk 0 (fun b =>
      CFSG.KC.Enum.strictB (T (II b)) fun B => pairQ Q1AQ Q1BQ Q2AQ Q2BQ WCQ A B) 56) 4

end CertificateChecks.KernelL43Q8

end
