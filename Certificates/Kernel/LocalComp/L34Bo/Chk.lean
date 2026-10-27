module

public import Certificates.Kernel.LocalComp.L34Bo.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Bo

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CertificateChecks.KernelLC.L34X Certificates.L34Borel
open CFSG.KLie.CT (andB notB)

theorem k_top : andB (CFSG.KS.Raw.bindArrK u0iT 42 6 UI)
    (andB (canonK 42 6 (mask 6) (42 * 6) UI)
    (andB (Nat.beq (pcomp 42 6 (mask 6) UI (UE0.G 0)) (pidn 42 6))
    (andB (Nat.beq (pcomp 42 6 (mask 6) (UE0.G 0) UI) (pidn 42 6))
    (andB (notB (Nat.beq (UE0.G 0) (pidn 42 6)))
    (andB (Nat.beq (pcomp 42 6 (mask 6) (UE0.G 0) (pcomp 42 6 (mask 6) (UE0.G 0) (UE0.G 0)))
      (pidn 42 6)) (inS (UE0.G 0))))))) = true := by
  quickRfl

theorem k_syl0 : sylK 0 SY0.k SY0.cnt SY0.G SY0.GI SY0.T SY0.PL SY0.POS SY0.SRT SY0.SRI
    sylGens[0]! = true := by quickRfl
theorem k_syl1 : sylK 1 SY1.k SY1.cnt SY1.G SY1.GI SY1.T SY1.PL SY1.POS SY1.SRT SY1.SRI
    sylGens[1]! = true := by quickRfl
theorem k_syl2 : sylK 2 SY2.k SY2.cnt SY2.G SY2.GI SY2.T SY2.PL SY2.POS SY2.SRT SY2.SRI
    sylGens[2]! = true := by quickRfl
theorem k_syl3 : sylK 3 SY3.k SY3.cnt SY3.G SY3.GI SY3.T SY3.PL SY3.POS SY3.SRT SY3.SRI
    sylGens[3]! = true := by quickRfl
theorem k_syl4 : sylK 4 SY4.k SY4.cnt SY4.G SY4.GI SY4.T SY4.PL SY4.POS SY4.SRT SY4.SRI
    sylGens[4]! = true := by quickRfl
theorem k_syl5 : sylK 5 SY5.k SY5.cnt SY5.G SY5.GI SY5.T SY5.PL SY5.POS SY5.SRT SY5.SRI
    sylGens[5]! = true := by quickRfl

theorem k_fix : allN 6 (fun j => allN 64 (fun q =>
    andB (Nat.beq (pg 6 (mask 6) (syT j q) (fa j)) (fa j))
      (Nat.beq (pg 6 (mask 6) (syT j q) (fb j)) (fb j)))) = true := by
  quickRfl

theorem kNegBo : notB (inSY 0 (UE0.G 0)) = true := by
  quickRfl

@[expose] noncomputable def nrm0 (s : Nat) : Bool := nrm 0 s
@[expose] noncomputable def nrm1 (s : Nat) : Bool := nrm 1 s
@[expose] noncomputable def nrm2 (s : Nat) : Bool := nrm 2 s
@[expose] noncomputable def nrm3 (s : Nat) : Bool := nrm 3 s
@[expose] noncomputable def nrm4 (s : Nat) : Bool := nrm 4 s
@[expose] noncomputable def nrm5 (s : Nat) : Bool := nrm 5 s

end CertificateChecks.KernelLC.L34Bo

end
