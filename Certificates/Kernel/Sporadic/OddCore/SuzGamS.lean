module

public import Certificates.Kernel.Sporadic.OddCore.SuzGamD
public import Certificates.Data.Kernel.SuzGamma2294
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.SGam

open CFSG.KC.Enum CFSG.KC.G2294 CertificateChecks.KernelSpor

@[expose] noncomputable def blk (f : Nat → Bool) (s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 22880), f x, true)) (nat_lit 64)

@[expose] noncomputable def blkL (f : Nat → Bool) (s : Nat) : Bool :=
  allN (nat_lit 1024) (fun i => strictB (Nat.add (Nat.mul (nat_lit 1024) s) i) fun x =>
    bIf(Nat.blt x (nat_lit 22880), f x, true))

@[expose] noncomputable def rnd (a h b s : Nat) : Bool :=
  strictB (SuzGamC a) fun C => strictB (SuzGamC h) fun H => strictB (SuzGamC b) fun C' =>
    blk (roundOK (nat_lit 280) SuzGamR C H C') s

@[expose] noncomputable def rnd0 (s : Nat) : Bool := rnd (nat_lit 1) (nat_lit 13) (nat_lit 2) s
@[expose] noncomputable def rnd1 (s : Nat) : Bool := rnd (nat_lit 2) (nat_lit 14) (nat_lit 3) s
@[expose] noncomputable def rnd2 (s : Nat) : Bool := rnd (nat_lit 5) (nat_lit 15) (nat_lit 6) s
@[expose] noncomputable def rnd3 (s : Nat) : Bool := rnd (nat_lit 6) (nat_lit 16) (nat_lit 7) s
@[expose] noncomputable def rnd4 (s : Nat) : Bool := rnd (nat_lit 8) (nat_lit 17) (nat_lit 9) s
@[expose] noncomputable def rnd5 (s : Nat) : Bool := rnd (nat_lit 10) (nat_lit 18) (nat_lit 11) s
@[expose] noncomputable def rnd6 (s : Nat) : Bool := rnd (nat_lit 11) (nat_lit 19) (nat_lit 12) s

@[expose] noncomputable def img (k s : Nat) : Bool :=
  strictB (SuzGamG k) fun G => blk (imgOK (nat_lit 22880) (nat_lit 280) G SuzGamR) s

@[expose] noncomputable def img0 (s : Nat) : Bool := img (nat_lit 0) s
@[expose] noncomputable def img1 (s : Nat) : Bool := img (nat_lit 1) s

@[expose] noncomputable def rowB (s : Nat) : Bool := blk (rowOK (nat_lit 22880) (nat_lit 280) SuzGamR) s

@[expose] noncomputable def hashSrc (j : Nat) : Nat := [1, 2, 5, 6, 8, 10, 11].getD j (nat_lit 0)

@[expose] noncomputable def hashL (j s : Nat) : Bool :=
  strictB (SuzGamC (hashSrc j)) fun C => strictB (SuzGamC (Nat.add (nat_lit 13) j)) fun H =>
    blkL (hashOK C H) s

@[expose] noncomputable def mv (G0 G1 t v : Nat) : Nat :=
  nIf(Nat.beq t (nat_lit 0), v, nIf(Nat.beq t (nat_lit 1), gp G0 v,
    strictN (gp G1 (gp G1 v)) fun u => nIf(Nat.beq t (nat_lit 2), u, gp G0 u)))

@[expose] noncomputable def baseSrc (t : Nat) : Nat × Nat :=
  [(0, 4), (4, 5), (7, 8), (9, 10)].getD t (0, 0)

@[expose] noncomputable def baseL (t s : Nat) : Bool :=
  strictB (SuzGamG (nat_lit 0)) fun G0 => strictB (SuzGamG (nat_lit 1)) fun G1 =>
    strictB (SuzGamC (baseSrc t).1) fun C => strictB (SuzGamC (nat_lit 3)) fun E =>
      strictB (SuzGamC (baseSrc t).2) fun C' => blkL (baseOK (mv G0 G1 t) C E C') s

end CertificateChecks.KernelSpor.OddCore.SGam

end
