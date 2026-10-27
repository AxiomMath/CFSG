module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.F2Reg
public import Certificates.Kernel.VecCert.Co2

#kc_repo #kc_json_gz CFSG.KD.SporCovF2.Co2Three.F "Certificates/Kernel/SporCovF2/data/co23.json.gz"
  49932 12759412832705006750
  (Rg : List (List Nat)) (Ms : List Nat) (H : List (List Nat)) (R : List (List Nat))
  (P : List Nat) (T : List (List Nat)) (Rp : List (List Nat)) (Gs : List (List Nat))
  (Y10 : List Nat) (Y20 : List Nat) (G10 : List Nat) (G20 : List Nat) (M0 : List (List Nat))
  (N0 : Nat) (NL0 : Nat) (C0 : List (List Nat))
  (Y11 : List Nat) (Y21 : List Nat) (G11 : List Nat) (G21 : List Nat) (M1 : List (List Nat))
  (N1 : Nat) (NL1 : Nat) (C1 : List (List Nat)) (Rs : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovF2.Co2Three

open CFSG.KC.SporCov CFSG.KC.M1F2 CertificateChecks.KernelVec.Co2

@[expose] noncomputable def L : Nat → Bool := letRL 239

@[expose] noncomputable def clC (E : List Nat → List Nat → Bool) (t y₁ y₂ g₁ g₂ : List Nat)
    (M : List (List Nat)) (n nL : Nat) (C : List (List Nat)) : Bool :=
  clH E L 3 t y₁ y₂ g₁ g₂ M nL && allLt nL (clL E y₁ y₂ n M) && stH L F.Rs 2 &&
    allLt 2 (stOK E M C F.Rs) && chW L t

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) (K : List Nat → Nat) : Bool :=
  allLt 6 (fun i => allLt 6 fun j => Nat.blt j i || pcR E 3 F.H F.R 6 i j) &&
    cenH E L F.H F.Rp F.Gs F.P 729 && keyInc K F.H 6 3 F.P &&
    allLt 729 (cenOK E 3 F.H 6 F.Rp F.Gs F.P F.T 729) &&
    clC E (nthW F.Rp 0) F.Y10 F.Y20 F.G10 F.G20 F.M0 F.N0 F.NL0 F.C0 &&
    clC E (nthW F.Rp 1) F.Y11 F.Y21 F.G11 F.G21 F.M1 F.N1 F.NL1 F.C1

namespace Ck

theorem ok : kitR 22 MA MB 2 5 F.Ms F.Rg 239 chk = true := by quickRfl

end Ck

end CFSG.KD.SporCovF2.Co2Three

end
