module

public import Certificates.Kernel.MaxD2.McLP.Enum
public import Certificates.Kernel.MaxD2.McLP.Data
public import Certificates.Kernel.MaxD2.McLP.CentData
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.McLCentOver
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.MclCentOver

@[expose] noncomputable def coK : Bool :=
  allN 5 fun k => wordEqK 275 9 (mask 9) (pidn 275 9) NE.G NGI NE.k (cW[k]!) (CO k) &&
    (canonK 275 9 (mask 9) (275 * 9) (CO k) && permOK 275 9 (mask 9) (275 * 9) (CO k) (COI k))

@[expose] noncomputable def cbK : Bool :=
  allN 5 (fun k => Nat.beq (pcomp 275 9 (mask 9) (CO k) (GP 1)) (pcomp 275 9 (mask 9) (GP 1) (CO k))) &&
  (Nat.beq (pw 275 9 (GP 1) 5) (pidn 275 9) &&
  (bIf(Nat.beq (GP 1) (pidn 275 9), false, true) &&
  (Nat.beq (CO 0) (GP 1) &&
  (Nat.blt (r32 CHB 0) RE.cnt && (Nat.beq (RE.T (r32 CHB 0)) (GP 1) &&
  (Nat.beq (pcomp 275 9 (mask 9) (GP 1) (RE.G 0)) (pcomp 275 9 (mask 9) (RE.G 0) (GP 1)) &&
  (Nat.beq (pcomp 275 9 (mask 9) (GP 1) (RE.G 1)) (pcomp 275 9 (mask 9) (RE.G 1) (GP 1)) &&
  (Nat.beq (pcomp 275 9 (mask 9) (TT 0) (GP 1)) (pcomp 275 9 (mask 9) (pw 275 9 (GP 1) 2) (TT 0)) &&
  allN NE.k fun i => Nat.blt (r32 CHB (Nat.add i 1)) 5 &&
    Nat.beq (pcomp 275 9 (mask 9) (NE.G i) (GP 1))
      (pcomp 275 9 (mask 9) (pw 275 9 (GP 1) (r32 CHB (Nat.add i 1))) (NE.G i))))))))))

@[expose] noncomputable def xlK (k l : Nat) : Nat := nIf(Nat.blt l 5, CO l, XT k)

@[expose] noncomputable def xliK (k l : Nat) : Nat := nIf(Nat.blt l 5, COI l, XTI k)

@[expose] noncomputable def xOneK (k : Nat) : Bool :=
  Nat.beq (XT k) (pcomp 275 9 (mask 9) (REP (Nat.add (Nat.div k 4) 1)) (pw 275 9 (TT 0) (Nat.mod k 4))) &&
  (permOK 275 9 (mask 9) (275 * 9) (XT k) (XTI k) &&
  (wordEqK 275 9 (mask 9) (pidn 275 9) (xlK k) (xliK k) 6 (aW[k]!) (GP 0) &&
   wordEqK 275 9 (mask 9) (pidn 275 9) (xlK k) (xliK k) 6 [1] (GP 1)))

@[expose] noncomputable def xK (lo m : Nat) : Bool := allN m fun d => xOneK (Nat.add lo d)

theorem k_co : coK = true := by quickRfl
theorem k_cb : cbK = true := by quickRfl
theorem k_aw : aW.length = 4 * mclFiveDataP.repW.length := by decide +kernel
theorem k_x0 : xK 0 113 = true := by quickRfl
theorem k_x1 : xK 113 113 = true := by quickRfl
theorem k_x2 : xK 226 113 = true := by quickRfl
theorem k_x3 : xK 339 113 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP

end
