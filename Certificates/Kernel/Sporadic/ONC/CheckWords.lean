module

public import Certificates.Data.Kernel.Spor.ONTauK
public import Certificates.Kernel.Sporadic.ON2.Data
public import CFSG.Sporadic.Recognition.ONMultiplierInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KS.ONC CFSG.Sporadic.Recognition.ONMultiplier

@[expose] def onLetterIdx (z : Int) : Nat :=
  if 0 < z then (z - 1).toNat else (-z - 1).toNat + 4

@[expose] def seedInv (w : List Int) : List Int := (w.map Neg.neg).reverse

@[expose] def onGW : List (List Int) :=
  onGenWords.toList ++ onGenWords.toList.map seedInv ++ [[1], [2]]

@[expose] def onCheckPairs : List (List Nat × List Nat) :=
  onCheckWords.map (fun w => (w.map onLetterIdx, [])) ++
    [(onSurjA.map onLetterIdx, [8]), (onSurjB.map onLetterIdx, [9])]

set_option Elab.async false

theorem checkWords_ok :
    relsK (fun j => List.getD ONW.LA j (nat_lit 0)) (fun j => List.getD ONW.LB j (nat_lit 0))
      onGW onCheckPairs = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONC

end
