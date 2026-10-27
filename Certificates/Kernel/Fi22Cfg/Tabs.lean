module

public import Certificates.Data.Kernel.Fi22.Cent
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Kernel.Sporadic.RowsWCmd
public meta import CFSG.Sporadic.Fi22.TriangularCfgInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cfg

open CFSG.Sporadic.Th.Native

meta def cfgTabs : Array Nat := Id.run do
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  let mut out : Array Nat := #[]
  for i in [0:8] do
    let T := CFSG.Sporadic.Fi22.Native.rank3CfgTab O i
    for x in [0:3510] do
      out := out.push (ap T x)
  return out

end CertificateChecks.KernelFi22Cfg

#krowsw CertificateChecks.KernelFi22Cfg.CT 12 CertificateChecks.KernelFi22Cfg.cfgTabs

namespace CertificateChecks.KernelFi22Cfg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Fi22Cent

@[expose] noncomputable def cfgPt (i : Nat) : Nat :=
  List.getD [0, 1, 63, 369, 322, 2441, 2488, 3427] i (nat_lit 0)

@[expose] noncomputable def cfgTb (i x : Nat) : Nat :=
  rg (nat_lit 12) (mask (nat_lit 12)) CT (nat_lit 0) (Nat.add (Nat.mul (nat_lit 3510) i) x)

@[expose] noncomputable def cfgTabSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 6)) fun i => strictB (Nat.mul (Nat.mod s (nat_lit 6)) (nat_lit 585))
    fun lo => allN (nat_lit 585) fun t =>
      Nat.beq (cfgTb i (Nat.add lo t)) (cK (cfgPt i) (Nat.add lo t))

@[expose] noncomputable def cfgRelSl (c : Nat) : Bool :=
  bIf(Nat.blt c (nat_lit 4),
    strictB (Nat.mul 2 c) fun p => strictB (Nat.add (Nat.mul 2 c) 1) fun q =>
      allN (nat_lit 3510) fun x =>
        Nat.beq (cfgTb p (cfgTb q (cfgTb p x))) (cfgTb q (cfgTb p (cfgTb q x))),
    strictB (Nat.div (Nat.sub c 4) 8) fun a => strictB (Nat.mod (Nat.sub c 4) 8) fun b =>
      bIf(Nat.beq (Nat.div a 2) (Nat.div b 2), true,
        allN (nat_lit 3510) fun x => Nat.beq (cfgTb a (cfgTb b x)) (cfgTb b (cfgTb a x))))

end CertificateChecks.KernelFi22Cfg

end
