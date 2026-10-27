module

public import Certificates.Kernel.SporSch.Mathieu.M12OddK
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Spor.MulH
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12Odd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KC.Child3 CFSG.KS.PEnum CFSG.KS.MulH Certificates.BTFinCk.M12 CertificateChecks.KernelSporSch

@[expose] noncomputable def wK (wd : List Int) : Nat :=
  abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1) wd

@[expose] noncomputable def recK (ws : List (List Int)) (G GI : Nat → Nat) : Bool :=
  allN ws.length (fun j => abOK (ws.getD j []) && Nat.beq (GI j) (wK (ws.getD j [])) &&
    Nat.beq (G j) (pidn 12 4) && canonK 12 4 (mask 4) (12 * 4) (GI j))

@[expose] noncomputable def repK' (k : Nat) : Bool :=
  abOK (rows.getD k default).2.1 && canonK 12 4 (mask 4) (12 * 4) (wK (rows.getD k default).2.1) &&
    ordIs 12 4 (mask 4) (pidn 12 4) (wK (rows.getD k default).2.1) ((rows.getD k default).1 - 1)

@[expose] noncomputable def commRow (k : Nat) : Bool :=
  allN (rows.getD k default).2.2.2.2.length (fun j =>
    abOK ((rows.getD k default).2.2.2.2.getD j []) &&
      commK 12 4 (mask 4) (12 * 4) (wK ((rows.getD k default).2.2.2.2.getD j []))
        (wK (rows.getD k default).2.1))

theorem r0 : repK' 0 = true := by quickRfl
theorem r1 : repK' 1 = true := by quickRfl
theorem r2 : repK' 2 = true := by quickRfl
theorem r3 : repK' 3 = true := by quickRfl
theorem r4 : repK' 4 = true := by quickRfl

theorem m0 : commRow 0 = true := by quickRfl
theorem m1 : commRow 1 = true := by quickRfl
theorem m2 : commRow 2 = true := by quickRfl
theorem m3 : commRow 3 = true := by quickRfl
theorem m4 : commRow 4 = true := by quickRfl

theorem f0r : recK (rows.getD 0 default).2.2.2.2 F0.G F0.GI = true := by quickRfl
theorem f1r : recK (rows.getD 1 default).2.2.2.2 F1.G F1.GI = true := by quickRfl
theorem f2r : recK (rows.getD 2 default).2.2.2.2 F2.G F2.GI = true := by quickRfl
theorem f3r : recK (rows.getD 3 default).2.2.2.2 F3.G F3.GI = true := by quickRfl
theorem f4r : recK (rows.getD 4 default).2.2.2.2 F4.G F4.GI = true := by quickRfl

theorem f0h : penumHdK (pidn 12 4) F0.cnt 1000 F0.T F0.PL = true := by quickRfl
theorem f1h : penumHdK (pidn 12 4) F1.cnt 1000 F1.T F1.PL = true := by quickRfl
theorem f2h : penumHdK (pidn 12 4) F2.cnt 1000 F2.T F2.PL = true := by quickRfl
theorem f3h : penumHdK (pidn 12 4) F3.cnt 1000 F3.T F3.PL = true := by quickRfl
theorem f4h : penumHdK (pidn 12 4) F4.cnt 1000 F4.T F4.PL = true := by quickRfl

theorem f0p : penumSlK 12 4 (mask 4) (12 * 4) true F0.G F0.GI (rows.getD 0 default).2.2.2.2.length
    F0.cnt F0.T F0.PL F0.POS F0.SRT F0.SRI 0 F0.cnt = true := by quickRfl
theorem f1p : penumSlK 12 4 (mask 4) (12 * 4) true F1.G F1.GI (rows.getD 1 default).2.2.2.2.length
    F1.cnt F1.T F1.PL F1.POS F1.SRT F1.SRI 0 F1.cnt = true := by quickRfl
theorem f2p : penumSlK 12 4 (mask 4) (12 * 4) true F2.G F2.GI (rows.getD 2 default).2.2.2.2.length
    F2.cnt F2.T F2.PL F2.POS F2.SRT F2.SRI 0 F2.cnt = true := by quickRfl
theorem f3p : penumSlK 12 4 (mask 4) (12 * 4) true F3.G F3.GI (rows.getD 3 default).2.2.2.2.length
    F3.cnt F3.T F3.PL F3.POS F3.SRT F3.SRI 0 F3.cnt = true := by quickRfl
theorem f4p : penumSlK 12 4 (mask 4) (12 * 4) true F4.G F4.GI (rows.getD 4 default).2.2.2.2.length
    F4.cnt F4.T F4.PL F4.POS F4.SRT F4.SRI 0 F4.cnt = true := by quickRfl

theorem f0s : slK F0.cnt (hsortPtK 12 4 (mask 4) F0.cnt F0.T F0.HS F0.HSI) 0 F0.cnt = true := by
  quickRfl
theorem f1s : slK F1.cnt (hsortPtK 12 4 (mask 4) F1.cnt F1.T F1.HS F1.HSI) 0 F1.cnt = true := by
  quickRfl
theorem f2s : slK F2.cnt (hsortPtK 12 4 (mask 4) F2.cnt F2.T F2.HS F2.HSI) 0 F2.cnt = true := by
  quickRfl
theorem f3s : slK F3.cnt (hsortPtK 12 4 (mask 4) F3.cnt F3.T F3.HS F3.HSI) 0 F3.cnt = true := by
  quickRfl
theorem f4s : slK F4.cnt (hsortPtK 12 4 (mask 4) F4.cnt F4.T F4.HS F4.HSI) 0 F4.cnt = true := by
  quickRfl

theorem f0c : Nat.beq F0.cnt (rows.getD 0 default).2.2.2.1 = true := by quickRfl
theorem f1c : Nat.beq F1.cnt (rows.getD 1 default).2.2.2.1 = true := by quickRfl
theorem f2c : Nat.beq F2.cnt (rows.getD 2 default).2.2.2.1 = true := by quickRfl
theorem f3c : Nat.beq F3.cnt (rows.getD 3 default).2.2.2.1 = true := by quickRfl
theorem f4c : Nat.beq F4.cnt (rows.getD 4 default).2.2.2.1 = true := by quickRfl

@[expose] def ws3 : List (List Int) := [(rows.getD 0 default).2.1, (rows.getD 1 default).2.1]
@[expose] def ws5 : List (List Int) := [(rows.getD 2 default).2.1]
@[expose] def ws11 : List (List Int) := [(rows.getD 3 default).2.1, (rows.getD 4 default).2.1]

theorem k3b : allN 2 (fun j => Nat.beq (K3.GP j) (M12Q.S j)) = true := by quickRfl
theorem k5b : allN 2 (fun j => Nat.beq (K5.GP j) (M12Q.S j)) = true := by quickRfl
theorem k11b : allN 2 (fun j => Nat.beq (K11.GP j) (M12Q.S j)) = true := by quickRfl

theorem k3m : allN 2 (fun j => permOK 12 4 (mask 4) (12 * 4) (K3.GP j) (K3.GIP j)) = true := by
  quickRfl
theorem k5m : allN 2 (fun j => permOK 12 4 (mask 4) (12 * 4) (K5.GP j) (K5.GIP j)) = true := by
  quickRfl
theorem k11m : allN 2 (fun j => permOK 12 4 (mask 4) (12 * 4) (K11.GP j) (K11.GIP j)) = true := by
  quickRfl

theorem k3c : allN 2 (fun j => canonK 12 4 (mask 4) (12 * 4) (K3.GP j) &&
    canonK 12 4 (mask 4) (12 * 4) (K3.GIP j)) = true := by quickRfl
theorem k5c : allN 2 (fun j => canonK 12 4 (mask 4) (12 * 4) (K5.GP j) &&
    canonK 12 4 (mask 4) (12 * 4) (K5.GIP j)) = true := by quickRfl
theorem k11c : allN 2 (fun j => canonK 12 4 (mask 4) (12 * 4) (K11.GP j) &&
    canonK 12 4 (mask 4) (12 * 4) (K11.GIP j)) = true := by quickRfl

theorem k3w : allN ws3.length (fun i => abOK (ws3.getD i []) &&
    Nat.beq (wK (ws3.getD i [])) (K3.E (lget K3.OFF i))) = true := by quickRfl
theorem k5w : allN ws5.length (fun i => abOK (ws5.getD i []) &&
    Nat.beq (wK (ws5.getD i [])) (K5.E (lget K5.OFF i))) = true := by quickRfl
theorem k11w : allN ws11.length (fun i => abOK (ws11.getD i []) &&
    Nat.beq (wK (ws11.getD i [])) (K11.E (lget K11.OFF i))) = true := by quickRfl

theorem k3o : offOK K3.CS K3.OFF K3.N = true := by quickRfl
theorem k5o : offOK K5.CS K5.OFF K5.N = true := by quickRfl
theorem k11o : offOK K11.CS K11.OFF K11.N = true := by quickRfl

theorem k3p : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) K3.CS = true := by quickRfl
theorem k5p : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) K5.CS = true := by quickRfl
theorem k11p : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) K11.CS = true := by quickRfl

theorem k3r : allN K3.N (repK 12 4 K3.GP K3.GIP 2 K3.CS K3.OFF K3.CI K3.E K3.P K3.L K3.K K3.S
    K3.SI K3.N 20000) = true := by quickRfl
theorem k5r : allN K5.N (repK 12 4 K5.GP K5.GIP 2 K5.CS K5.OFF K5.CI K5.E K5.P K5.L K5.K K5.S
    K5.SI K5.N 20000) = true := by quickRfl
theorem k11r : allN K11.N (repK 12 4 K11.GP K11.GIP 2 K11.CS K11.OFF K11.CI K11.E K11.P K11.L
    K11.K K11.S K11.SI K11.N 20000) = true := by quickRfl

end CertificateChecks.KernelSporSch.M12Odd

end
