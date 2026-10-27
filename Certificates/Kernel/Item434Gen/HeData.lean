module

public import Certificates.Data.Item434SporHe
public import Certificates.Data.Kernel.Item434Gen
public import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.Item434SporHe
meta import CFSG.Sporadic.HeldB.CertPChainData
import Certificates.Kernel.Misc.Perm.HexCmd

namespace CertificateChecks.KernelItem434.He

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen CFSG.Sporadic.HeldB

meta def arrsM : Array (Array Nat) :=
  let n := 8330
  let a := heGen 0
  let b := heGen 1
  let x := wab n a b heXW
  let y := wab n a b heYW
  let sg := [heFix0, heFix1, heFix2, heFix3].flatMap fun c =>
    (List.range 4).map fun j => wab n a b (c.sw.getD j [])
  #[a, invCand n a, b, invCand n b, x, invCand n x, y, invCand n y, cmA n x y, compA n x y,
    compA n x (powN n y 2)] ++ sg.toArray ++ (sg.map (invCand n)).toArray

end CertificateChecks.KernelItem434.He

public section

#kmisc_packarrs CertificateChecks.KernelItem434.He.HV CertificateChecks.KernelItem434.He.arrsM 14

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Item434Gen

noncomputable abbrev L :Nat → Nat := twoK (HV 0) (HV 2)

noncomputable abbrev LI :Nat → Nat := twoK (HV 1) (HV 3)

@[expose] noncomputable def SV (c j : Nat) : Nat := HV (11 + 4 * c + j)

@[expose] noncomputable def SIV (c j : Nat) : Nat := HV (27 + 4 * c + j)

end CertificateChecks.KernelItem434.He

end
