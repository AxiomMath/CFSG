module

public import Certificates.Kernel.Sporadic.McLC.SylData
public import Certificates.Kernel.Sporadic.McLC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def cKS (p : Nat) : Bool := canonK 275 9 (mask 9) (275 * 9) p

theorem sylBase_ok : bAnd(szOK 275 9, bAnd(cKS (pidn 275 9), bAnd(CFSG.KS.Prim.idK 275 9 (mask 9),
    bAnd(allN 4 (fun j => bAnd(cKS (McLCS.GI j), bAnd(Nat.beq (McLCS.G j) (pidn 275 9),
      bAnd(cKS (McLCSI j), invEqK 275 9 (mask 9) (275 * 9) (McLCS.GI j) (McLCSI j))))),
    bAnd(Nat.beq McLCS.cnt 128, penumHdK (pidn 275 9) McLCS.cnt 50000 McLCS.T McLCS.PL)))))
      = true := by
  quickRfl

theorem sylE_ok : penumSlK 275 9 (mask 9) (275 * 9) true McLCS.G McLCS.GI 4 McLCS.cnt McLCS.T
    McLCS.PL McLCS.POS McLCS.SRT McLCS.SRI 0 McLCS.cnt = true := by quickRfl

theorem sylH_ok : slK McLCS.cnt (hsortPtK 275 9 (mask 9) McLCS.cnt McLCS.T McLCS.HS McLCS.HSI)
    0 McLCS.cnt = true := by quickRfl

theorem sylCl_ok : slK (Nat.mul McLCS.cnt 8)
    (findPtK McLCS.cnt McLCS.T (prodQK 275 9 (mask 9) 8 McLCS.T (bothK 4 McLCS.GI McLCSI))
      McLCSCl) 0 (Nat.mul McLCS.cnt 8) = true := by quickRfl

theorem sylGen_ok : allN 4 (fun j => allN 275 fun x => Nat.beq (pk (McLCS.GI j) x)
    (List.foldr GK x (List.getD CFSG.ClassicalInvolution.McLData.sWords j []))) = true := by
  quickRfl

theorem sylConj_ok : allN 35 (fun j => bAnd(cKS (McLCSJ j), allN 275 fun x =>
    Nat.beq
      (pk (McLCSJ j) (List.foldr GA x (List.getD CFSG.ClassicalInvolution.McLData.conjWords j [])))
      (List.foldr GA (r32 McLK.AL x)
        (List.getD CFSG.ClassicalInvolution.McLData.conjWords j [])))) = true := by
  quickRfl

@[expose] noncomputable def covS (i : Nat) : Bool :=
  bIf(Nat.beq (pcomp 275 9 (mask 9) (McLCS.T i) (McLCS.T i)) (pidn 275 9),
    bIf(Nat.beq (McLCS.T i) (pidn 275 9), true,
      List.any (List.range 35) fun j => Nat.beq (McLCS.T i) (McLCSJ j)),
    true)

theorem sylCov_ok : allN 128 covS = true := by quickRfl

end CertificateChecks.KernelSpor.McLC

end
