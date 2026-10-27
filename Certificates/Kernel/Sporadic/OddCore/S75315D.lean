module

public import Certificates.Kernel.Sporadic.OddCore.S129062D
public import Certificates.Data.IRRSuz
meta import Certificates.Data.IRRSuz
meta import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
meta import Certificates.Kernel.Sporadic.OddCore.S129062D
meta import Certificates.Kernel.Sporadic.OddCore.S2307D

public section

namespace CertificateChecks.KernelSpor.S75315

open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.ComponentClassification.Walter86

meta def dataM : Array Nat := Id.run do
  let E := CertificateChecks.KernelSpor.S2307.eM
  let z := invFusionRepArr 19
  let I := CertificateChecks.KernelSpor.S129062.idxM
  let Wi := I.filter fun k => inM E[k]!
  let mut U : Array Nat := #[]
  let mut found := false
  for a in Wi do
    if !found then
      for b in Wi do
        if !found && IRRSuz.zWitOK z E[a]! E[b]! then
          U := #[a, b]
          found := true
  let mut wu : Array Nat := #[]
  for k in I do
    let y := E[k]!
    if y == z then
      wu := wu.push 0
    else
      let zy := comp 1782 z y
      match (List.range U.size).find? (fun u => IRRSuz.witOK z y zy E[U[u]!]!) with
      | some u => wu := wu.push u
      | none =>
        match Wi.find? (fun b => IRRSuz.witOK z y zy E[b]!) with
        | some b =>
          U := U.push b
          wu := wu.push (U.size - 1)
        | none => wu := wu.push 0
  return #[U.size, 0, 1] ++ U ++ wu

end CertificateChecks.KernelSpor.S75315

#krows32 CertificateChecks.KernelSpor.S75315W CertificateChecks.KernelSpor.S75315.dataM

end
