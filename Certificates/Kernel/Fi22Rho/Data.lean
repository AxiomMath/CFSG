module

public import Certificates.Data.Kernel.Fi22.Letters
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
public import Certificates.Kernel.Sporadic.RowsWCmd
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
public meta import Mathlib
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Rho

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.Sporadic.Recognition.Fi22Multiplier

meta def nodeTabs : Array Nat := Id.run do
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  let bi := invT 3510 O.beta
  let mut out : Array Nat := #[]
  for c in [0:9] do
    let T := wordTab 3510 O.alpha O.alpha O.beta bi (fi22Letter c)
    for x in [0:3510] do
      out := out.push (ap T x)
  return out

end CertificateChecks.KernelFi22Rho

#krowsw CertificateChecks.KernelFi22Rho.NT 12 CertificateChecks.KernelFi22Rho.nodeTabs

namespace CertificateChecks.KernelFi22Rho

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22L CFSG.KS.Row CFSG.Sporadic.Recognition.Fi22Multiplier

@[expose] noncomputable def appK (l : Nat × Bool) (y : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (nIf(Nat.beq l.1 (nat_lit 0), lk (orbT (nat_lit 0)) y, reg ljPacked (nat_lit 2) y))
    (nIf(Nat.beq l.1 (nat_lit 0), lk (orbT (nat_lit 0)) y, lk (orbT (nat_lit 1)) y)) l.2

@[expose] noncomputable def wordK (w : List (Nat × Bool)) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun l _ ih => strictN ih fun z => appK l z) w

@[expose] noncomputable def nt (c y : Nat) : Nat :=
  rg (nat_lit 12) (mask (nat_lit 12)) NT (nat_lit 0) (Nat.add (Nat.mul (nat_lit 3510) c) y)

@[expose] noncomputable def wordN (w : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun c _ ih => strictN ih fun z => nt c z) w

@[expose] noncomputable def nodeSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 6)) fun c => strictB (Nat.mul (Nat.mod s (nat_lit 6)) (nat_lit 585))
    fun lo => allN (nat_lit 585) fun t =>
      Nat.beq (nt c (Nat.add lo t)) (wordK (fi22Letter c) (Nat.add lo t))

@[expose] def nodeRels : List (List Nat) := CFSG.YGroups.yRels 3 3 2 ++ [f332Word]

@[expose] noncomputable def relAtN (r y : Nat) : Nat :=
  nIf(Nat.blt r (nat_lit 47), wordN (List.getD nodeRels r []) y,
    wordN fi22BWord (reg ljPacked (nat_lit 2) y))

@[expose] noncomputable def relSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 6)) fun r => strictB (Nat.mul (Nat.mod s (nat_lit 6)) (nat_lit 585))
    fun lo => allN (nat_lit 585) fun t => Nat.beq (relAtN r (Nat.add lo t)) (Nat.add lo t)

end CertificateChecks.KernelFi22Rho

end
