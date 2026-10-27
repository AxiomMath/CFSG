module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Data.Kernel.Spor.CommCent
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.Fi22CI

open CFSG.EvenSporadicStandard.HypOne.Fi22 CertificateChecks.KernelSpor.Fi22CB

meta def lettersOf (k : Nat) (gs : List Nat) : Array (Array Nat) :=
  let t := CFSG.Sporadic.FischerOddCore.fi22ExtArr (21 + k)
  let G := (gs.map fun j => (hypTbl j).map (·.toNat)).toArray
  let G := if k < 3 then G else G.map fun g => compA g t
  #[G[0]!, G[1]!, t, invA G[0]!, invA G[1]!]

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def lettersOK (M : Nat → Nat) (t : Nat) : Bool :=
  bAnd(allN 5 (fun z => Fi22X.cn (M z)),
  bAnd(Nat.beq (M 2) t,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (M 0) (M 3),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (M 1) (M 4),
  bAnd(Fi22X.siftP (M 0), bAnd(Fi22X.siftP (M 1),
  bAnd(Nat.beq (Fi22X.c (M 0) t) (Fi22X.c t (M 0)),
  Nat.beq (Fi22X.c (M 1) t) (Fi22X.c t (M 1)))))))))

@[expose] def Ts : List Nat :=
  [nat_lit 54, nat_lit 182, nat_lit 694, nat_lit 72, nat_lit 360, nat_lit 64]

@[expose] noncomputable def tsOK : Bool :=
  allN 6 (fun j => memL (fixCnt 3510 12 (mask 12) (Fi22ExtT.L (Nat.add 21 j))) Ts)

theorem tsAll : tsOK = true := by quickRfl

@[expose] noncomputable def centChk (M : Nat → Nat) (B : List BaseRec) (PF ZF DF RF : Nat) : Bool :=
  centFixOK 3510 12 (mask 12) M 5 2 B PF ZF DF RF Ts

end CertificateChecks.KernelSpor.Fi22CI

end
