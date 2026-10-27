module

public import Certificates.Kernel.HeLoc.Seven0Data

public section

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.RankThree.Native

meta def fr2M : List Nat := forceOf heSevenCase2Rels 7

meta def aw2M : List Nat := heSevenA2Gens.toList.map (idxOf heSevenC2Cert)

meta def cw2M : List Nat := (List.range 6).map fun m =>
  idxOf heSevenA2Cert (conjA 8330 heSevenC2Gens[m / 2]! heSevenA2Gens[m % 2]!)

meta def sw2M : List Nat := heSevenC2Cert.pts.toList.map fun c =>
  match (List.range 2).find? (fun l => !commA 8330 c heSevenA2Gens[l]!) with
  | some l => l + 1
  | none => idxOf heSevenA2Cert c + 100

end CertificateChecks.KernelHeLoc.Seven

#kh_tree CertificateChecks.KernelHeLoc.Seven.C2 CFSG.RankThree.PartOne.heSevenC2Cert 8330
  CFSG.RankThree.PartOne.heSevenKeys
#kh_tree CertificateChecks.KernelHeLoc.Seven.A2 CFSG.RankThree.PartOne.heSevenA2Cert 8330
  CFSG.RankThree.PartOne.heSevenKeys
#knatlist CertificateChecks.KernelHeLoc.Seven.FR2 CertificateChecks.KernelHeLoc.Seven.fr2M
#knatlist CertificateChecks.KernelHeLoc.Seven.AW2 CertificateChecks.KernelHeLoc.Seven.aw2M
#knatlist CertificateChecks.KernelHeLoc.Seven.CW2 CertificateChecks.KernelHeLoc.Seven.cw2M
#knatlist CertificateChecks.KernelHeLoc.Seven.SW2 CertificateChecks.KernelHeLoc.Seven.sw2M

end
