module

public import Certificates.Kernel.HS3850.InnerKDefs
public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Data.Kernel.PkPow
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalQT.HSAut.K4146R

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.HN
open CFSG.KD.LQT.C4126 CFSG.KC.PkPow CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

@[expose] noncomputable def memT (j : Nat) : Nat := IT.F ([0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13].getD j 0)

@[expose] noncomputable def e8K (Y e : Nat) : Nat := kW Y (yWc.getD e [])

theorem IK.perm : allN 14 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (IT.F k) &&
    invEqK 3850 12 (mask 12) (3850 * 12) (IT.F k) (pinvS 3850 12 (mask 12) (IT.F k))) = true := by
  quickRfl

theorem IK.gi : (canonK 3850 12 (mask 12) (3850 * 12) GI1 && Nat.beq (pc (IT.F 0) GI1) idn &&
    Nat.beq (pc GI1 (IT.F 0)) idn) = true := by quickRfl

theorem IK.mem : allN 11 (fun j => Nat.blt (MI j) 7680 && Nat.beq (A.T (MI j)) (memT j)) = true := by
  quickRfl

theorem IK.sift : (Nat.beq (IT.F 9) (wfoldR ls8 SW9) && Nat.beq (IT.F 10) (wfoldR ls8 SW10) &&
    Nat.beq (IT.F 11) (wfoldR ls8 SW11)) = true := by quickRfl

theorem IK.ord : (Nat.beq (p5K (IT.F 0)) idn && (Nat.beq (IT.F 0) idn).not &&
    Nat.beq (pc (IT.F 2) (IT.F 0)) (pc (IT.F 0) (IT.F 2)) && patK (IT.F 1)) = true := by quickRfl

theorem IK.eHead : (Nat.beq EE.cnt 16 && penumHdK idn EE.cnt 16 EE.T EE.PL &&
    allN 4 (fun j => Nat.beq (EE.G j) (kW (IT.F 1) (eWc.getD j [])) &&
      Nat.beq (EE.GI j) (EE.G j))) = true := by quickRfl

theorem IK.eRec : penumSlK 3850 12 (mask 12) (3850 * 12) false EE.G EE.GI 4 EE.cnt EE.T EE.PL EE.POS
    EE.SRT EE.SRI 0 16 = true := by quickRfl

theorem IK.e : (allN 16 (fun x => allN 16 fun y =>
      Nat.beq (pc (EE.T x) (EE.T y)) (pc (EE.T y) (EE.T x))) &&
    allN 16 (fun x => Nat.beq (pc (EE.T x) (EE.T x)) idn) &&
    (List.range 16).any (fun x => Nat.beq (EE.T x) (HC.F 5)) &&
    allN 16 (fun x => Nat.beq (EE.T x) idn || Nat.beq (nfix 3850 12 (EE.T x)) 170)) = true := by
  quickRfl

theorem IK.pres : (allN 2 (fun i => Nat.beq (pc (IT.F (3 + i)) (IT.F (3 + i))) idn &&
      Nat.beq (nfix 3850 12 (IT.F (3 + i))) 170 &&
      allN 4 fun j => Nat.blt (PW (4 * i + j)) 16 &&
        Nat.beq (pc (IT.F (7 + i)) (kW (IT.F (3 + i)) (eWc.getD j [])))
          (pc (EE.T (PW (4 * i + j))) (IT.F (7 + i)))) &&
    allN 2 (fun i => Nat.beq (pc (IT.F (5 + i)) (IT.F (5 + i))) idn &&
      Nat.beq (nfix 3850 12 (IT.F (5 + i))) 30)) = true := by quickRfl

theorem IK.cls : (Nat.beq (nfix 3850 12 (HC.F 12)) 30 && Nat.beq (nfix 3850 12 (HC.F 5)) 170 &&
    Nat.beq (nfix 3850 12 (IT.F 1)) 170 && Nat.beq (pc (IT.F 1) (IT.F 1)) idn &&
    Nat.beq (pc (kW (IT.F 1) wbc) (kW (IT.F 1) wbc)) idn &&
    Nat.beq (nfix 3850 12 (kW (IT.F 1) wbc)) 30 &&
    Nat.beq (pc (IT.F 9) (IT.F 9)) idn && Nat.beq (nfix 3850 12 (IT.F 9)) 30 &&
    Nat.beq (pc (IT.F 9) (kW (IT.F 1) wbc)) (pc (kW (IT.F 1) wbc) (IT.F 9)) &&
    Nat.beq (nfix 3850 12 (pc (IT.F 9) (kW (IT.F 1) wbc))) 30 &&
    allN 2 (fun i => Nat.beq (pc (kW (IT.F (5 + i)) wbc) (kW (IT.F (5 + i)) wbc)) idn &&
      Nat.beq (nfix 3850 12 (kW (IT.F (5 + i)) wbc)) 170)) = true := by quickRfl

theorem IK.stab : (allN 8 (fun e => Nat.beq (pc (e8K (IT.F 1) e) (HC.F 5))
      (e8K (IT.F 1) (zmulL.getD e 0))) &&
    Nat.beq (e8K (IT.F 1) 0) idn && Nat.beq (e8K (IT.F 1) 1) (IT.F 1) &&
    allN 2 (fun j => allN 8 fun e => Nat.beq (pc (IT.F (10 + j)) (e8K (IT.F 1) e))
      (pc (e8K (IT.F 1) ((sigmaL.getD j []).getD e 0)) (IT.F (10 + j)))) &&
    allN 2 (fun i => allN 8 fun e => Nat.beq (pc (IT.F (12 + i)) (e8K (IT.F (5 + i)) e))
      (pc (e8K (IT.F 1) ((psiL.getD i []).getD e 0)) (IT.F (12 + i))))) = true := by quickRfl

end CertificateChecks.KernelHS3850

end
