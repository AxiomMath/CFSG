module

public import Certificates.Data.Kernel.PCent
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaHSData
meta import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaHSData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.RankThree.PartOne.KS.PKit
meta import CFSG.RankThree.PartOne.KS.PKit

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS799102.TV1
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThV1Hex
#kmisc_hexflat CertificateChecks.KernelHS799102.TV1
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThV1Hex 3 100 7 21
#ks_chars CertificateChecks.KernelHS799102.TV2
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThV2Hex
#kmisc_hexflat CertificateChecks.KernelHS799102.TV2
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThV2Hex 3 100 7 23
#ks_chars CertificateChecks.KernelHS799102.TV3
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThV3Hex
#kmisc_hexflat CertificateChecks.KernelHS799102.TV3
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThV3Hex 3 100 7 21

public section

namespace CertificateChecks.KernelHS799102

#kc_repo #kc_json_gz CertificateChecks.KernelHS799102
  "Certificates/Kernel/HS799102/data/chain.json.gz" 24126 1651976557584644063
  (M1 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (M2 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (M3 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (D1 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (D2 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (D3 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (X1 : Nat) (X2 : Nat) (X3 : Nat)
  (O1 : List (Nat × Nat × Nat × Nat)) (O2 : List (Nat × Nat × Nat × Nat))
  (O3 : List (Nat × Nat × Nat × Nat))

open CFSG.KC.Enum (pcomp)
open CFSG.KS (mask pinvS)

@[expose] noncomputable def commK (x y : Nat) : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) x y)
    (pcomp 100 7 (mask 7) (pinvS 100 7 (mask 7) x) (pinvS 100 7 (mask 7) y))

@[expose] noncomputable def mG1 (k : Nat) : Nat := TV1.F (Nat.add (nat_lit 15) k)

@[expose] noncomputable def mG2 (k : Nat) : Nat := TV2.F (Nat.add (nat_lit 16) k)

@[expose] noncomputable def mG3 (k : Nat) : Nat := TV3.F (Nat.add (nat_lit 13) k)

@[expose] noncomputable def dGen (F : Nat → Nat) (o k : Nat) : Nat :=
  commK (F (Nat.add o (Nat.mul (nat_lit 2) k))) (F (Nat.add o (Nat.add (Nat.mul (nat_lit 2) k) 1)))

@[expose] noncomputable def dG1 (k : Nat) : Nat := dGen TV1.F (nat_lit 17) k

@[expose] noncomputable def dG2 (k : Nat) : Nat := dGen TV2.F (nat_lit 19) k

@[expose] noncomputable def dG3 (k : Nat) : Nat := dGen TV3.F (nat_lit 17) k

end CertificateChecks.KernelHS799102

end
