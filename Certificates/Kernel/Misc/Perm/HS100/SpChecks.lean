module

public import Certificates.Kernel.Misc.Perm.HS100.SpData
public import Certificates.Kernel.Misc.Perm.HS100.NChecks
public import Certificates.Data.Kernel.RightOrbBits
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Sp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermWit
  CFSG.KC.ConjOrb
open CFSG.KC.Misc.ArrEnum (permB memK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.S0 (cK Z0)
open CertificateChecks.KernelMisc.HS100.N (pZ)

@[expose] noncomputable def pZI (a x : Nat) : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (pinvS 100 7 (mask 7) a) x) a

@[expose] noncomputable def omB (i : Nat) : Bool :=
  Nat.beq i 8 || Nat.beq i 51 || Nat.beq i 53 || Nat.beq i 92 || Nat.beq i 70 || Nat.beq i 97

@[expose] noncomputable def fixOmK (x : Nat) : Bool :=
  allN 100 fun i => !(omB i) || Nat.beq (pg 7 (mask 7) x i) i

@[expose] noncomputable def rootPt (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.RightOrbBits.bitK (OT 0) i)
    (cond (allN 16 fun j => Nat.beq (pg 7 (mask 7) (S0.E0.T j) i) i) 1 0)

theorem sift : (allN 2 (fun k => siftR 100 7 C.LR C.TRI C.BP 5 (N.NX.F k)) &&
    allN 4 (fun k => siftR 100 7 C.LR C.TRI C.BP 5 (S0.EX.F k))) = true := by quickRfl

theorem eInv : (allN 16 (fun i => Nat.beq (pcomp 100 7 (mask 7) (S0.E0.T i) (S0.E0.T i))
      (pidn 100 7)) &&
    allN 16 (fun i => allN 16 fun j => cK (S0.E0.T i) (S0.E0.T j))) = true := by quickRfl

theorem eNorm : allN 2 (fun k => allN 16 fun i =>
    memK S0.E0.N S0.E0.T (pZ (N.NX.F k) (S0.E0.T i)) &&
      memK S0.E0.N S0.E0.T (pZI (N.NX.F k) (S0.E0.T i))) = true := by quickRfl

theorem trans : allN 16 (fun i => Nat.beq (S0.E0.T i) (pidn 100 7) ||
    (Nat.blt (NW i) 11520 && Nat.beq (pZ (N.NN.T (NW i)) Z0) (S0.E0.T i))) = true := by quickRfl

theorem orbRoot : allN 100 rootPt = true := by quickRfl

theorem om : (Nat.beq (cntK 100 omB) 6 &&
    allN 2 (fun k => allN 100 fun i => Bool.beq (omB (pg 7 (mask 7) (N.NX.F k) i)) (omB i)) &&
    allN 16 (fun i => fixOmK (S0.E0.T i))) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Sp

end
