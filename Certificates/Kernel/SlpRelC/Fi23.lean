module

public import Certificates.Data.Kernel.SlpRel
public import Certificates.Kernel.Fi23M.Data
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi23Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSlpRel

open CFSG.KC.Enum CFSG.KC.SlpRel CFSG.KD.Fi23M
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

@[expose] noncomputable def fiNZ (X : Nat) : Bool := Nat.beq (Nat.land X (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def fiSlpK (prog : List (List Nat)) (ps : List (List Nat × List Nat))
    (ne : List Nat) : Bool :=
  strictB LO fun lo => strictB CI fun ci => strictB RM fun rm => strictB ONE fun one =>
  strictB (MT (nat_lit 0)) fun a => strictB (MT (nat_lit 1)) fun b =>
    slpRelK strictB (CFSG.KC.Ord.mul3s (nat_lit 253) (nat_lit 64009) lo ci rm) one Nat.beq fiNZ
      [a, b] prog ps ne

@[expose] def fiRelsI (i : Nat) : List (List Nat × List Nat) :=
  [([fiHeisX i, fiHeisX i, fiHeisX i], []), ([fiHeisY i, fiHeisY i, fiHeisY i], []),
   ([fiHeisX i, fiHeisZ], [fiHeisZ, fiHeisX i]), ([fiHeisY i, fiHeisZ], [fiHeisZ, fiHeisY i]),
   ([fiHeisX i, fiHeisY i], [fiHeisY i, fiHeisX i, fiHeisZ])]

@[expose] def fiRelsIJ (i j : Nat) : List (List Nat × List Nat) :=
  ([fiHeisX i, fiHeisX j], [fiHeisX j, fiHeisX i]) ::
    if i = j then [] else
      [([fiHeisY i, fiHeisY j], [fiHeisY j, fiHeisY i]),
       ([fiHeisX i, fiHeisY j], [fiHeisY j, fiHeisX i])]

@[expose] def fiRelsK : List (List Nat × List Nat) :=
  ((List.range 4).flatMap fun i => fiRelsI i ++ (List.range 4).flatMap (fiRelsIJ i)) ++
    [([fiHeisZ, fiHeisZ, fiHeisZ], [])]

set_option Elab.async false

theorem ch129030_ok : fiSlpK fiHeisProg fiRelsK [fiHeisZ] = true := by
  quickRfl

end CertificateChecks.KernelSlpRel

end
