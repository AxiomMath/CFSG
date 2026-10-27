module

public import Certificates.Data.Item434SporRu
public import Certificates.Data.Kernel.Item434Gen
public import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.Item434SporRu
meta import CFSG.Sporadic.Schreier.RuDefs
import Certificates.Kernel.Misc.Perm.HexCmd

namespace CertificateChecks.KernelItem434.Ru

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.Sporadic.RuSchreier

meta def arrsM : Array (Array Nat) :=
  let n := 4060
  let a := ruArr4060 0
  let b := ruArr4060 1
  let x := wab n a b ruXW
  let y := wab n a b ruYW
  let sg := [ruFix0, ruFix1, ruFix2, ruFix3].flatMap fun c =>
    (List.range 4).map fun j => wab n a b (c.sw.getD j [])
  #[a, invCand n a, b, invCand n b, x, invCand n x, y, invCand n y, cmA n x y, compA n x y,
    compA n x (powN n y 2)] ++ sg.toArray ++ (sg.map (invCand n)).toArray

end CertificateChecks.KernelItem434.Ru

public section

#kmisc_packarrs CertificateChecks.KernelItem434.Ru.RV CertificateChecks.KernelItem434.Ru.arrsM 12

namespace CertificateChecks.KernelItem434.Ru

open CFSG.KC.Item434Gen

noncomputable abbrev L : Nat → Nat := twoK (RV 0) (RV 2)

noncomputable abbrev LI : Nat → Nat := twoK (RV 1) (RV 3)

@[expose] noncomputable def SV (c j : Nat) : Nat := RV (11 + 4 * c + j)

@[expose] noncomputable def SIV (c j : Nat) : Nat := RV (27 + 4 * c + j)

end CertificateChecks.KernelItem434.Ru

end
