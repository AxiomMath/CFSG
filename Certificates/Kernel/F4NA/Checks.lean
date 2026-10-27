module

public import Certificates.Data.Kernel.F4NA
public import Certificates.Data.F4NA
public import Certificates.Kernel.F4NA.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.F4NA

open CFSG.KC.F4NA CFSG.KC.F4Salt CFSG.RankThree.PartOne.F106

theorem ch271035_rt : bindB 10 RT f4ThreeRt = true := by quickRfl
theorem ch271035_inv : bindB 10 INV f4ThreeInv = true := by quickRfl
theorem ch271035_pw : pwB PW f4ThreePaths = true := by quickRfl
theorem ch271035_gw : gwB f4ThreeGens GW = true := by quickRfl
theorem ch271035_e3 : e3B RT PW E3 = true := by quickRfl
theorem ch271035_cw : cubeWtB E3 WT = true := by quickRfl

theorem ch271035_wtA : wtB PW WT (pk 2 f4WA) 0 = true := by quickRfl
theorem ch271035_wtB : wtB PW WT (pk 2 f4WB) 1 = true := by quickRfl
theorem ch271035_wtC : wtB PW WT (pk 2 f4WC) 2 = true := by quickRfl
theorem ch271035_wtY : wtB PW WT (pk 2 f4WY2) 3 = true := by quickRfl
theorem ch271035_homA : homB RT WT (pk 2 f4WA) 0 = true := by quickRfl
theorem ch271035_homB : homB RT WT (pk 2 f4WB) 1 = true := by quickRfl
theorem ch271035_homC : homB RT WT (pk 2 f4WC) 2 = true := by quickRfl
theorem ch271035_homY : homB RT WT (pk 2 f4WY2) 3 = true := by quickRfl

theorem ch271035_zb : centB RT PW WT 1 f4NaZ = true := by quickRfl
theorem ch271035_za : (List.rec (motive := fun _ => Bool) true
    (fun z _ ih => centB RT PW WT 0 z && ih) f4ZaList) = true := by quickRfl
theorem ch271035_zc : (List.rec (motive := fun _ => Bool) true
    (fun z _ ih => centB RT PW WT 2 z && ih) f4ZcList) = true := by quickRfl

theorem ch271035_zaw : (List.rec (motive := fun _ => Bool) true
    (fun z _ ih => Nat.blt z 729 && Nat.beq (l2 WT z 0) 0 && ih) f4ZaList) = true := by quickRfl
theorem ch271035_zcw : (List.rec (motive := fun _ => Bool) true
    (fun z _ ih => Nat.blt z 729 && Nat.beq (l2 WT z 2) 0 && ih) f4ZcList) = true := by quickRfl

theorem ch271035_one : (Nat.beq (l32 PW 0) 0 && eqS (lS MSP 0) oneS) = true := by quickRfl
theorem ch271035_g0 : genB PW MSP 0 (GW.getD 0 (0, 0)).1 (GW.getD 0 (0, 0)).2 = true := by quickRfl
theorem ch271035_g1 : genB PW MSP 1 (GW.getD 1 (0, 0)).1 (GW.getD 1 (0, 0)).2 = true := by quickRfl
theorem ch271035_g2 : genB PW MSP 2 (GW.getD 2 (0, 0)).1 (GW.getD 2 (0, 0)).2 = true := by quickRfl
theorem ch271035_g3 : genB PW MSP 3 (GW.getD 3 (0, 0)).1 (GW.getD 3 (0, 0)).2 = true := by quickRfl
theorem ch271035_g4 : genB PW MSP 4 (GW.getD 4 (0, 0)).1 (GW.getD 4 (0, 0)).2 = true := by quickRfl
theorem ch271035_g5 : genB PW MSP 5 (GW.getD 5 (0, 0)).1 (GW.getD 5 (0, 0)).2 = true := by quickRfl

theorem ch271035_e0 : edgesB PW PAR MSP 1 91 = true := by quickRfl
theorem ch271035_e1 : edgesB PW PAR MSP 92 91 = true := by quickRfl
theorem ch271035_e2 : edgesB PW PAR MSP 183 91 = true := by quickRfl
theorem ch271035_e3' : edgesB PW PAR MSP 274 91 = true := by quickRfl
theorem ch271035_e4 : edgesB PW PAR MSP 365 91 = true := by quickRfl
theorem ch271035_e5 : edgesB PW PAR MSP 456 91 = true := by quickRfl
theorem ch271035_e6 : edgesB PW PAR MSP 547 91 = true := by quickRfl
theorem ch271035_e7 : edgesB PW PAR MSP 638 91 = true := by quickRfl

theorem ch271035_tr0 : trB f4ShortPos MSP TR 0 243 = true := by quickRfl
theorem ch271035_tr1 : trB f4ShortPos MSP TR 243 243 = true := by quickRfl
theorem ch271035_tr2 : trB f4ShortPos MSP TR 486 243 = true := by quickRfl

theorem ch271035_wits : witsB RT PW INV wits = true := by quickRfl
theorem ch271035_cover : coverB E3 WT (recMask wits) = true := by quickRfl

theorem ch271035_cA : Nat.beq (cnt fun i => Nat.beq (l2 WT i 0) 0) 243 = true := by quickRfl
theorem ch271035_cB : Nat.beq (cnt fun i => Nat.beq (l2 WT i 1) 0) 243 = true := by quickRfl
theorem ch271035_cC : Nat.beq (cnt fun i => Nat.beq (l2 WT i 2) 0) 243 = true := by quickRfl
theorem ch271035_cE0 : Nat.beq (cnt fun i =>
    Nat.beq (l2 WT i 0) 0 && Nat.beq (l2 WT i 3) 0) 81 = true := by quickRfl
theorem ch271035_cQ : Nat.beq (cnt fun i => Nat.beq (l2 WT i 1) 0 && (!bt TR i &&
    !bt TR (mulI RT PW i f4NaZ) && !bt TR (mulI RT PW (mulI RT PW i f4NaZ) f4NaZ))) 24 = true := by
  quickRfl
theorem ch271035_cA0 : Nat.beq (cnt fun i => Nat.beq (l2 WT i 0) 0 &&
    Nat.beq (l2 WT i 3) 0 && !Nat.beq i 0 && !bt TR i) 24 = true := by quickRfl
theorem ch271035_zbf : (Nat.beq (l2 WT f4NaZ 1) 0 && bt E3 f4NaZ && bt TR f4NaZ) = true := by
  quickRfl

end CFSG.KD.F4NA

end
