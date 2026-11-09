module

public import Certificates.Kernel.SmallSpor.M12Data
public meta import Certificates.Kernel.SmallSpor.M12Data
public meta import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.ListBridgeSelfComm
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSmallSpor.M12

meta def commWit1 : List Nat := Id.run do
  let cmp := fun (a b : Array Nat) => Array.ofFn (n := 12) fun x => a[b[x.val]!]!
  let inv := fun (a : Array Nat) => Id.run do
    let mut r : Array Nat := Array.replicate 12 0
    for x in [0:12] do
      r := r.set! a[x]! x
    return r
  let one : Array Nat := Array.ofFn (n := 12) fun i => i.val
  let kp := (CFSG.KC.BfsGen.search 12 4 k1G).1
  let up := (CFSG.KC.BfsGen.search 12 4 u1G).1
  let mut out : Array Nat := #[]
  for t in kp do
    let mut ws : Array Nat := #[]
    if cmp t (cmp t t) == one && t != one then
      let ti := inv t
      let mut seen : Array (Array Nat) := #[]
      for j in [0:up.size] do
        if ws.size < 9 then
          let u := up[j]!
          let c := cmp (cmp (cmp u t) (inv u)) ti
          if !seen.contains c then
            seen := seen.push c
            ws := ws.push j
    for k in [0:9] do
      out := out.push (ws[k]?.getD 0)
  return out.toList

end CertificateChecks.KernelSmallSpor.M12

end

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelSmallSpor.M12.CWU1 CertificateChecks.KernelSmallSpor.M12.commWit1

namespace CertificateChecks.KernelSmallSpor.M12

open CFSG.KC.ListBridge

public theorem commU1 : commSelfK 12 4 EK1.N EK1.T EU1.N EU1.T CWU1 = true := by quickRfl

end CertificateChecks.KernelSmallSpor.M12
