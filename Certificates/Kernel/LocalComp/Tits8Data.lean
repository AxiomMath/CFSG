module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsTests
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CertificateChecks.KernelLC.Tits8

open CFSG.ComponentClassification.RankTwoExceptional.TitsSec8 CFSG.Sporadic.Schreier.Tits

meta def productsN : Array (Nat × Array Nat) := Id.run do
  let Ls := titsNLevels
  let n := 1755
  let c := (List.range 5).map fun i => Ls[i]!.pts.size
  let mut out : Array (Nat × Array Nat) := #[]
  for a in [0:c[0]!] do
    for b in [0:c[1]!] do
      let tab := CFSG.KS.RawGen.comp n Ls[0]!.tr[a]! Ls[1]!.tr[b]!
      for cc in [0:c[2]!] do
        let tabc := CFSG.KS.RawGen.comp n tab Ls[2]!.tr[cc]!
        for d in [0:c[3]!] do
          let t3 := CFSG.KS.RawGen.comp n tabc Ls[3]!.tr[d]!
          for e in [0:c[4]!] do
            let g := CFSG.KS.RawGen.comp n t3 Ls[4]!.tr[e]!
            out := out.push ((((a * c[1]! + b) * c[2]! + cc) * c[3]! + d) * c[4]! + e, g)
  return out

meta def commM (x y : Array Nat) : Bool :=
  CFSG.KS.RawGen.comp 1755 x y == CFSG.KS.RawGen.comp 1755 y x

meta def words : Array (Array Nat) := (titsSec8ZWords ++ titsSec8TWords).toArray.map wA

meta def comms : Array (Array Nat) :=
  #[firstComm titsSec8ZWords, secondComm titsSec8ZWords, firstComm titsSec8TWords,
    secondComm titsSec8TWords]

meta def ccCodes : Array (Array Nat) :=
  titsCCQ.toArray.map fun c => #[((productsN.find? fun (_, g) => g == c).map (·.1)).getD 0]

meta def witCodes : Array (Array Nat) :=
  titsCCQ.toArray.map fun c => #[((productsN.find? fun (_, g) =>
    commM g titsTArr && !commM c g).map (·.1)).getD 0]

end CertificateChecks.KernelLC.Tits8

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelLC.Tits8W include_bytes "data/Tits8Data.Tits8W.items" 19340 17332483150934979165
#kc_items CertificateChecks.KernelLC.Tits8U include_bytes "data/Tits8Data.Tits8U.items" 9672 409762185272807455
#kc_items CertificateChecks.KernelLC.Tits8CC include_bytes "data/Tits8Data.Tits8CC.items" 39 18362343629704035864
#kc_items CertificateChecks.KernelLC.Tits8Wit include_bytes "data/Tits8Data.Tits8Wit.items" 40 13253798844641020624

end
