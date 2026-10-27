module

public import Certificates.Data.Kernel.PCent
public import Certificates.Kernel.HS100.ChainData
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaHSData
meta import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaHSData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.RankThree.PartOne.KS.PKit
meta import CFSG.RankThree.PartOne.KS.PKit

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS799102.TH
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThHex
#kmisc_hexflat CertificateChecks.KernelHS799102.TH
  CFSG.RankThree.PartTwo.Sec21.Holder214Theta.hsThHex 3 100 7 9

public section

namespace CertificateChecks.KernelHS799102

#kc_repo #kc_json_gz CertificateChecks.KernelHS799102
  "Certificates/Kernel/HS799102/data/cls.json.gz" 4080412 16236382003318263865
  (G : List Nat) (R1 : List (Nat × Nat × Nat × Nat)) (R2 : List (Nat × Nat × Nat × Nat))
  (R3 : List (Nat × Nat × Nat × Nat))

open CFSG.KS (mask pinvS)

@[expose] noncomputable def pG (k : Nat) : Nat := G.getD k (nat_lit 0)

@[expose] noncomputable def pGI (k : Nat) : Nat := pG (Nat.land (Nat.add k (nat_lit 2)) (nat_lit 3))

@[expose] noncomputable def pGBind : Bool :=
  Nat.beq (pG 0) (CertificateChecks.KernelHS100.HP.F 0) &&
    Nat.beq (pG 1) (CertificateChecks.KernelHS100.HP.F 1) &&
    Nat.beq (pG 2) (pinvS 100 7 (mask 7) (CertificateChecks.KernelHS100.HP.F 0)) &&
    Nat.beq (pG 3) (pinvS 100 7 (mask 7) (CertificateChecks.KernelHS100.HP.F 1))

end CertificateChecks.KernelHS799102

end
