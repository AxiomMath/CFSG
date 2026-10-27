module

public import Certificates.Kernel.TwoHSLe4.S9Defs
meta import Certificates.Kernel.TwoHSLe4.S9Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
public import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelTwoHSLe4.S9

open CFSG.EvenSporadicStandard.TwoHS

meta def bfsW : Array R4 × Array (List ℕ) := Id.run do
  let mut elems : Array R4 := #[R4.one]
  let mut words : Array (List ℕ) := #[[]]
  let mut i := 0
  for _ in [0:400] do
    if i < elems.size then
      let a := elems[i]!
      for l in [0:2] do
        let b := rmul a (genL l)
        if !elems.contains b then
          elems := elems.push b
          words := words.push (words[i]! ++ [l])
      i := i + 1
  return (elems, words)

meta def wM : Array (Array ℕ) :=
  (q0Data.map rl).toArray.map fun a =>
    let w := (bfsW.2)[(bfsW.1.findIdx? (· == a)).getD 0]!
    #[w.length] ++ w.toArray

end CertificateChecks.KernelTwoHSLe4.S9

#kmisc_packarrs CertificateChecks.KernelTwoHSLe4.S9.WT CertificateChecks.KernelTwoHSLe4.S9.wM 6

end
