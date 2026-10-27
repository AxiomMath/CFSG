module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.FischerOddCore.Fi22PairCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22PrD

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

meta def rowsM : Array (Array Nat) := Id.run do
  let roots := fi22ExtRoots
  let inv : Array Nat := (Array.range 6143).map fun k => fi22ExtInvRec k 14
  let res : Array (Array Nat) := inv.map fi22ExtResArr
  let mut mp : Std.HashMap (Array Nat) Nat := {}
  for k in [0:6143] do
    mp := mp.insert res[k]! inv[k]!
  let mut rows : Array (Array Nat) := #[]
  for j in [0:79] do
    let I0 := roots[j]!
    let good := fi22GoodFix (fixCount 3510 (fi22ExtFullArr I0))
    let rw := fi22ExtResArr I0
    let mut row : Array Nat := Array.replicate (48 * 128) 0
    if good then
      for k in [0:6143] do
        let I := inv[k]!
        let r := res[k]!
        if I != I0 then
          let p := compA 256 rw r
          if eqA 256 p (compA 256 r rw) then
            row := row.set! k (mp.getD p 0)
    for c in [0:48] do
      rows := rows.push (row.extract (128 * c) (128 * c + 128))
  return rows

end CertificateChecks.KernelSpor.Fi22PrD

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22PrD.T CertificateChecks.KernelSpor.Fi22PrD.rowsM 18

end
