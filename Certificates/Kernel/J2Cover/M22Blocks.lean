module

public import Certificates.Kernel.J2Cover.ModelsP2
public import Certificates.Kernel.LocalComp.BlockGen
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def mtK (a d : Nat) : Nat := nIf(Nat.blt a 128, pg 7 (mask 7) (MTR a) d, 0)

@[expose] noncomputable def witK (j i : Nat) : Nat :=
  nIf(Nat.beq j 0, pg 7 (mask 7) CW0P i, pg 7 (mask 7) CW1P i)

@[expose] noncomputable def actK (j i : Nat) : Nat :=
  nIf(Nat.beq j 0, pg 13 (mask 13) CA0P i, pg 13 (mask 13) CA1P i)

@[expose] noncomputable def yDK (k i : Nat) : Nat × Nat :=
  (pg 7 (mask 7) (YP k) i, pg 13 (mask 13) (YI k) i)

@[expose] noncomputable def yFold (k i : Nat) : Nat × Nat :=
  (nth [] yWords k).foldl (fun pc x => (mtK pc.1 (witK x pc.2), actK x pc.2)) (0, i)

@[expose] noncomputable def fMT (a : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (MTR a) (128 * 7)) 0,
    allN 128 fun d => Nat.beq (mulIdx a d) (pg 7 (mask 7) (MTR a) d))

@[expose] noncomputable def fYD (m : Nat) : Bool :=
  (fun k i => bAnd(Nat.beq (yFold k i).1 (yDK k i).1, Nat.beq (yFold k i).2 (yDK k i).2))
    (Nat.div m 4725) (Nat.mod m 4725)

@[expose] noncomputable def fDC (a : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (DP a) (4725 * 7)) 0, bAnd(Nat.beq (Nat.shiftRight (DI a) (4725 * 13)) 0,
  bIf(Nat.beq a 0, allN 4725 (fun i => bAnd(Nat.beq (pg 7 (mask 7) (DP 0) i) 0,
      Nat.beq (pg 13 (mask 13) (DI 0) i) i)),
    bAnd(Nat.blt (par a) a, allN 4725 fun i => strictB (pg 7 (mask 7) (YP (gen a)) i) fun yp =>
      strictB (pg 13 (mask 13) (YI (gen a)) i) fun yi => bAnd(Nat.blt yi 4725,
        bAnd(Nat.beq (pg 7 (mask 7) (DP a) i) (mtK yp (pg 7 (mask 7) (DP (par a)) yi)),
          Nat.beq (pg 13 (mask 13) (DI a) i) (pg 13 (mask 13) (DI (par a)) yi)))))))

#lc_blocks MTB fMT 128 1

#lc_blocks YDB fYD 14175 64

#lc_blocks DCBJ2 fDC 128 1

end CertificateChecks.KernelJ2Cover

end
