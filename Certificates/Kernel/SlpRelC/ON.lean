module

public import Certificates.Data.Kernel.SlpRel
public import Certificates.Kernel.Sporadic.ONC.Tau
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ONCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSlpRel

open CFSG.KC.Enum CFSG.KC.SlpRel CFSG.KS.ONC CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CertificateChecks.KernelSpor.ONC (FA FB)

@[expose] noncomputable def onNZ (X : Nat) : Bool :=
  Bool.not (Nat.beq (Nat.mod X (nat_lit 2048)) (nat_lit 1))

@[expose] noncomputable def onSlpK (FA FB : Nat → Nat) (prog : List (List Nat))
    (ps : List (List Nat × List Nat)) (ne : List Nat) : Bool :=
  strictB CS fun cs => strictB DS fun ds => strictB LL fun L => strictB HH fun H =>
  strictB CM fun cm => strictB RM fun rm => strictB ONE fun one =>
  strictB (batK cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
  strictB (batK cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
    slpRelK strictB (mul3 L H cm rm) one Nat.beq onNZ [a, b] prog ps ne

@[expose] def onRelsK : List (List Nat × List Nat) :=
  [([onHeisX, onHeisX, onHeisX, onHeisX, onHeisX, onHeisX, onHeisX], []),
   ([onHeisY, onHeisY, onHeisY, onHeisY, onHeisY, onHeisY, onHeisY], []),
   ([onHeisZ, onHeisZ, onHeisZ, onHeisZ, onHeisZ, onHeisZ, onHeisZ], []),
   ([onHeisX, onHeisZ], [onHeisZ, onHeisX]),
   ([onHeisY, onHeisZ], [onHeisZ, onHeisY]),
   ([onHeisX, onHeisY], [onHeisY, onHeisX, onHeisZ]),
   ([onHeisG, onHeisZ, onHeisZ, onHeisZ, onHeisZ, onHeisZ, onHeisZ], [onHeisZ, onHeisG])]

set_option Elab.async false

theorem ch129009_ok : onSlpK FA FB onHeisProg onRelsK [onHeisZ] = true := by
  quickRfl

end CertificateChecks.KernelSlpRel

end
