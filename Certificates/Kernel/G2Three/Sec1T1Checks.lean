module

public import Certificates.Data.Kernel.G2Three.Sec1T1
public import Certificates.Kernel.G2Three.Sec1T1Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three

theorem r1_one : (Nat.beq (R1U 7) ONEP && Nat.beq (R1H 0) ONEP && Nat.beq (R1K1 0) ONEP &&
    Nat.beq (R1K2 0) ONEP && Nat.beq (R1Q1 0) ONEP && Nat.beq (R1Q2 0) ONEP &&
    Nat.beq (R1S 0) ONEP && Nat.beq (R1A 0) ONEP && Nat.beq (R1M 0) ONEP && Nat.beq (R1KY 0) 28 &&
    Nat.beq (R1PY 0) 2340 && Nat.beq (R1PI 0) 2340) = true := by quickRfl

theorem r1_rel : eqK (fun q => R1U (R1RA q)) (fun q => R1U (R1RB q)) (fun q => R1U (R1RC q))
    (fun q => R1U (R1RD q)) 67 2 = true := by quickRfl

theorem r1_nrel : neK (fun q => R1U (R1NA q)) (fun q => R1U (R1NB q)) (fun q => R1U (R1NC q))
    (fun q => R1U (R1ND q)) 4 1 = true := by quickRfl

theorem r1_swp : allBelow 11 1 (fun q => Nat.beq (SWP (R1U (R1SWA q))) (R1U (R1SWB q))) = true := by
  quickRfl

theorem r1_parH : parK R1HPA R1HPB R1HPOS 3 575 9 = true := by quickRfl

theorem r1_closH0 : closP R1H (fun s => R1U (R1HG s)) R1HPOS 576 3 0 432 7 = true := by quickRfl
theorem r1_closH1 : closP R1H (fun s => R1U (R1HG s)) R1HPOS 576 3 432 432 7 = true := by quickRfl
theorem r1_closH2 : closP R1H (fun s => R1U (R1HG s)) R1HPOS 576 3 864 432 7 = true := by quickRfl
theorem r1_closH3 : closP R1H (fun s => R1U (R1HG s)) R1HPOS 576 3 1296 432 7 = true := by quickRfl

theorem r1_sortH : sortK R1H R1HSRT R1HSRI 576 9 = true := by quickRfl

theorem r1_genH : (idxK R1H R1U R1IH 576 8 1 &&
    idxK R1H (fun s => SWP (R1U (R1HG s))) R1ISW 576 3 1) = true := by quickRfl

theorem r1_K1 : (parK R1K1PA R1K1PB R1K1POS 2 23 1 &&
    closP R1K1 (fun s => R1U (R1K1G s)) R1K1POS 24 2 0 48 1 && sortK R1K1 R1K1SRT R1K1SRI 24 1) =
    true := by quickRfl

theorem r1_K2 : (parK R1K2PA R1K2PB R1K2POS 2 23 1 &&
    closP R1K2 (fun s => R1U (R1K2G s)) R1K2POS 24 2 0 48 1 && sortK R1K2 R1K2SRT R1K2SRI 24 1) =
    true := by quickRfl

theorem r1_Q1 : (parK R1Q1PA R1Q1PB R1Q1POS 2 7 1 &&
    closP R1Q1 (fun s => R1U (R1Q1G s)) R1Q1POS 8 2 0 16 1 && sortK R1Q1 R1Q1SRT R1Q1SRI 8 1) =
    true := by quickRfl

theorem r1_Q2 : (parK R1Q2PA R1Q2PB R1Q2POS 2 7 1 &&
    closP R1Q2 (fun s => R1U (R1Q2G s)) R1Q2POS 8 2 0 16 1 && sortK R1Q2 R1Q2SRT R1Q2SRI 8 1) =
    true := by quickRfl

theorem r1_S : (parK R1SPA R1SPB R1SPOS 5 63 1 &&
    closP R1S (fun s => R1U (R1SG s)) R1SPOS 64 5 0 320 5 && sortK R1S R1SSRT R1SSRI 64 1) =
    true := by quickRfl

theorem r1_A : (parK R1APA R1APB R1APOS 4 31 1 &&
    closP R1A (fun s => R1U (R1AG s)) R1APOS 32 4 0 128 2 && sortK R1A R1ASRT R1ASRI 32 1) =
    true := by quickRfl

theorem r1_M : (parK R1MPA R1MPB R1MPOS 2 191 3 &&
    closP R1M (fun s => R1U (R1MG s)) R1MPOS 192 2 0 384 6 && sortK R1M R1MSRT R1MSRI 192 3) =
    true := by quickRfl

theorem r1_genM : idxK R1M (fun q => R1U (R1IMU q)) R1IM 192 5 1 = true := by quickRfl

theorem r1_E : (basisK R1E (fun s => R1U (R1EG s)) 3 8 1 && sortK R1E R1ESRT R1ESRI 8 1) = true := by
  quickRfl

theorem r1_F : (basisK R1F (fun s => R1U (R1FG s)) 3 8 1 && sortK R1F R1FSRT R1FSRI 8 1) = true := by
  quickRfl

theorem r1_Y2 : (basisK R1Y2 (fun s => R1U (R1Y2G s)) 3 8 1 && sortK R1Y2 R1Y2SRT R1Y2SRI 8 1) =
    true := by quickRfl

theorem r1_Y3 : (basisK R1Y3 (fun s => R1U (R1Y3G s)) 3 8 1 && sortK R1Y3 R1Y3SRT R1Y3SRI 8 1) =
    true := by quickRfl

theorem r1_normK : (eqK (fun q => R1U (Nat.div q 2)) (fun q => R1U (R1K1G (Nat.mod q 2)))
    (fun q => R1K1 (R1NK1 q)) (fun q => R1U (Nat.div q 2)) 10 1 && ltK R1NK1 24 10 1 &&
    eqK (fun q => R1U (Nat.div q 2)) (fun q => R1U (R1K2G (Nat.mod q 2)))
    (fun q => R1K2 (R1NK2 q)) (fun q => R1U (Nat.div q 2)) 10 1 && ltK R1NK2 24 10 1) = true := by
  quickRfl

theorem r1_normQ : (eqK (fun q => R1U (Nat.div q 2)) (fun q => R1U (R1Q1G (Nat.mod q 2)))
    (fun q => R1Q1 (R1NQ1 q)) (fun q => R1U (Nat.div q 2)) 10 1 && ltK R1NQ1 8 10 1 &&
    eqK (fun q => R1U (Nat.div q 2)) (fun q => R1U (R1Q2G (Nat.mod q 2)))
    (fun q => R1Q2 (R1NQ2 q)) (fun q => R1U (Nat.div q 2)) 10 1 && ltK R1NQ2 8 10 1) = true := by
  quickRfl

theorem r1_normA : (eqK (fun q => R1U (Nat.div q 4)) (fun q => R1U (R1AG (Nat.mod q 4)))
    (fun q => R1A (R1NA5 q)) (fun q => R1U (Nat.div q 4)) 20 1 && ltK R1NA5 32 20 1) = true := by
  quickRfl

theorem r1_cenK1 : Nat.beq (cntK R1K1 (fun s => R1U (R1K1G s)) 2 24 1) 2 = true := by quickRfl

theorem r1_cenS : Nat.beq (cntK R1S (fun s => R1U (R1SG s)) 5 64 1) 2 = true := by quickRfl

theorem r1_cenA : Nat.beq (cntK R1A (fun s => R1U (R1AG s)) 4 32 1) 2 = true := by quickRfl

theorem r1_cB : Nat.beq (cntK R1H (fun _ => R1U 13) 1 576 9) 32 = true := by quickRfl

theorem r1_cE : Nat.beq (cntK R1H (fun s => R1U (R1EG s)) 3 576 9) 8 = true := by quickRfl

theorem r1_cF : Nat.beq (cntK R1H (fun s => R1U (R1FG s)) 3 576 9) 8 = true := by quickRfl

theorem r1_cmA : Nat.beq (cntMK R1H (fun s => R1U (R1AG s)) (fun s => R1U (R1AG s))
    (fun s => R1U (Nat.add 25 s)) 4 576 9) 32 = true := by quickRfl

theorem r1_cmAs : Nat.beq (cntMK R1H (fun s => SWP (R1U (R1AG s))) (fun s => R1U (R1AG s))
    (fun s => R1U (Nat.add 25 s)) 4 576 9) 0 = true := by quickRfl

theorem r1_cmEF : Nat.beq (cntMK R1H (fun s => R1U (R1EFG s)) (fun s => R1U (R1EFG s))
    (fun s => R1U (Nat.add 29 s)) 3 576 9) 32 = true := by quickRfl

theorem r1_cmEFs : Nat.beq (cntMK R1H (fun s => SWP (R1U (R1EFG s))) (fun s => R1U (R1EFG s))
    (fun s => R1U (Nat.add 29 s)) 3 576 9) 0 = true := by quickRfl

theorem r1_kY : (closF MUL22 R1KY R1KG R1K1POS 24 2 0 48 1 && sortK R1KY R1KYSRT R1KYSRI 24 1) =
    true := by quickRfl

theorem r1_pY0 : closF MUL33 R1PY R1PG R1HPOS 576 3 0 432 7 = true := by quickRfl
theorem r1_pY1 : closF MUL33 R1PY R1PG R1HPOS 576 3 432 432 7 = true := by quickRfl
theorem r1_pY2 : closF MUL33 R1PY R1PG R1HPOS 576 3 864 432 7 = true := by quickRfl
theorem r1_pY3 : closF MUL33 R1PY R1PG R1HPOS 576 3 1296 432 7 = true := by quickRfl

theorem r1_pGen : (idxK R1PY R1PU R1IH 576 8 1 &&
    allBelow 3 1 (fun s => Nat.beq (R1PY (R1ISW s)) (MUL33 (MUL33 (R1PG 3) (R1PG s)) (R1PG 3))) &&
    Nat.beq (MUL33 (R1PG 3) (R1PG 3)) 2340) = true := by quickRfl

theorem r1_pI : (parK R1PIPA R1PIPB R1PIPOS 4 35 1 && closF MUL33 R1PI R1PG R1PIPOS 36 4 0 144 3 &&
    sortK R1PI R1PISRT R1PISRI 36 1) = true := by quickRfl

theorem r1_act : actK R1E (fun s => R1U (R1EMG s)) R1EM 7 1 = true := by quickRfl

theorem r1_conjE : (eqK (fun q => R1U (R1EDJ q)) (fun q => R1U (R1EDD q)) (fun q => R1U (R1EDI q))
    (fun _ => R1U 7) 3 1 && ltK R1EDW 3 3 1 &&
    neK (fun q => R1U (R1EDD (Nat.div q 8))) (fun q => R1E (Nat.shiftLeft 1 (R1EDW (Nat.div q 8))))
      (fun q => R1E (Nat.mod q 8)) (fun q => R1U (R1EDD (Nat.div q 8))) 24 1) = true := by quickRfl

theorem r1_fixE : (neK (fun q => R1M (R1FXK q)) (fun q => R1E (R1EO q)) (fun q => R1E (R1EO q))
    (fun q => R1M (R1FXK q)) 6 1 && ltK R1FXK 192 6 1) = true := by quickRfl

theorem r1_transE : (eqK (fun q => R1M (R1ETK q)) (fun q => R1E (R1ETU q))
    (fun q => R1E (R1ETV q)) (fun q => R1M (R1ETK q)) 36 1 && ltK R1ETK 192 36 1) = true := by
  quickRfl

theorem r1_cosA : (ltK R1RAR 32 4 1 && ltK R1RAW 32 4 1 && ltK R1RAT 4 4 1 && ltK R1RAE 8 4 1 &&
    neqK (fun q => R1RAT (Nat.succ q)) Nat.succ 3 1 &&
    eqK (fun _ => R1U 19) (fun q => R1A (R1RAR q)) (fun q => R1A (R1RAW q)) (fun _ => R1U 19) 4 1 &&
    eqK (fun q => R1A (R1RAW q)) (fun _ => R1U 7) (fun q => R1A (R1RAR (R1RAT q)))
      (fun q => R1E (R1RAE q)) 4 1 &&
    neK (fun q => R1A (R1RAR (R1P4I (Nat.div q 8)))) (fun _ => R1U 7)
      (fun q => R1A (R1RAR (R1P4J (Nat.div q 8)))) (fun q => R1E (Nat.mod q 8)) 48 1) = true := by
  quickRfl

theorem r1_orb1 : (eqK (fun q => R1U (R1O1K q)) (fun _ => R1U 5) (fun q => R1Q1 (R1O1V q))
    (fun q => R1U (R1O1K q)) 6 1 &&
    eqK (fun q => R1Q1 (R1O1V q)) (fun _ => R1U 7) (fun q => R1Q1 (R1O1W q)) (fun q => R1U (R1O1E q))
      6 1 && ltK R1O1V 8 6 1 && ltK R1O1W 8 6 1 &&
    allBelow 5 1 (fun q => Nat.blt (R1O1W q) (R1O1W (Nat.succ q))) &&
    neK (fun q => R1Q1 (R1O1W (Nat.div q 2))) (fun _ => R1U 7)
      (fun q => R1U (Nat.add 7 (Nat.mul 4 (Nat.mod q 2)))) (fun _ => R1U 7) 12 1) = true := by
  quickRfl

theorem r1_orb2 : (eqK (fun q => R1U (R1O2K q)) (fun _ => R1U 6) (fun q => R1Q2 (R1O2V q))
    (fun q => R1U (R1O2K q)) 6 1 &&
    eqK (fun q => R1Q2 (R1O2V q)) (fun _ => R1U 7) (fun q => R1Q2 (R1O2W q)) (fun q => R1U (R1O2E q))
      6 1 && ltK R1O2V 8 6 1 && ltK R1O2W 8 6 1 &&
    allBelow 5 1 (fun q => Nat.blt (R1O2W q) (R1O2W (Nat.succ q))) &&
    neK (fun q => R1Q2 (R1O2W (Nat.div q 2))) (fun _ => R1U 7)
      (fun q => R1U (Nat.add 7 (Nat.mul 4 (Nat.mod q 2)))) (fun _ => R1U 7) 12 1) = true := by
  quickRfl

theorem r1_orb3 : (eqK (fun q => R1U (R1O3K q)) (fun _ => R1U 12) (fun q => R1A (R1O3V q))
    (fun q => R1U (R1O3K q)) 18 1 &&
    eqK (fun q => R1A (R1O3V q)) (fun _ => R1U 7) (fun q => R1A (R1O3W q)) (fun q => R1U (R1O3E q))
      18 1 && ltK R1O3V 32 18 1 && ltK R1O3W 32 18 1 &&
    allBelow 17 1 (fun q => Nat.blt (R1O3W q) (R1O3W (Nat.succ q))) &&
    neK (fun q => R1A (R1O3W (Nat.div q 8))) (fun _ => R1U 7) (fun q => R1Q1 (Nat.mod q 8))
      (fun _ => R1U 7) 144 3 &&
    neK (fun q => R1A (R1O3W (Nat.div q 8))) (fun _ => R1U 7) (fun q => R1Q2 (Nat.mod q 8))
      (fun _ => R1U 7) 144 3) = true := by quickRfl

theorem r1_f19 : (eqK (fun _ => R1U 0) (fun q => R1E (Nat.shiftLeft 1 q)) (fun q => R1Y2 (R1Y2W q))
    (fun _ => R1U 0) 3 1 && ltK R1Y2W 8 3 1 &&
    eqK (fun _ => R1U 0) (fun q => R1F (Nat.shiftLeft 1 q)) (fun q => R1Y3 (R1Y3W q))
    (fun _ => R1U 0) 3 1 && ltK R1Y3W 8 3 1) = true := by quickRfl

end CFSG.KD.G2Three.Sec1

end
