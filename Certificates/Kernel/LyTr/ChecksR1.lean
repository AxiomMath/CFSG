module

public import Certificates.Kernel.LyTr.Defs
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Raw
open CFSG.Sporadic.Recognition.LyonsSims

theorem k_r1base : bAnd(szOK 1080 11, bAnd(c11 id11, bAnd(CFSG.KS.Prim.idK 1080 11 (mask 11),
    bAnd(allN 4 (fun j => bAnd(c11 (UH.F j), bAnd(c11 (UHI j), i11 (UH.F j) (UHI j)))),
    bAnd(allN 5 (fun j => bAnd(c11 (R1.GI j), bAnd(Nat.beq (R1.G j) id11,
      Nat.beq (wK 1080 11 LU (Ly1080.txyWords.getD j [])) (R1.GI j)))),
    bAnd(Nat.beq R1.cnt 3888, penumHdK id11 R1.cnt 5000 R1.T R1.PL)))))) = true := by
  quickRfl

theorem k_r1h0 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 0 486 = true :=
  by quickRfl
theorem k_r1h1 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 486 486 = true :=
  by quickRfl
theorem k_r1h2 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 972 486 = true :=
  by quickRfl
theorem k_r1h3 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 1458 486 = true :=
  by quickRfl
theorem k_r1h4 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 1944 486 = true :=
  by quickRfl
theorem k_r1h5 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 2430 486 = true :=
  by quickRfl
theorem k_r1h6 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 2916 486 = true :=
  by quickRfl
theorem k_r1h7 : slK R1.cnt (hsortPtKF 1080 11 (mask 11) R1.cnt R1.T R1.HS R1.HSI) 3402 486 = true :=
  by quickRfl

theorem k_tree : bAnd(allN 122 (fun r => Nat.beq (R1.PL r) (R2.PL r)),
    allN 608 (fun r => Nat.beq (R1.POS r) (R2.POS r))) = true := by
  quickRfl

end CertificateChecks.KernelLyTr

end
