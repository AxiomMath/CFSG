module

public import Certificates.Data.Kernel.G2Three.Sec1
public import Certificates.Kernel.G2Three.Sec1T5Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three

theorem q5_one : (Nat.beq (Q5U 7) ONEP && Nat.beq (Q5X 0) ONEP && Nat.beq (Q5S 0) ONEP &&
    Nat.beq (Q5A 0) ONEP && Nat.beq (Q5B 0) ONEP && Nat.beq (Q5P 0) ONEP && Nat.beq (Q5C 0) ONEP &&
    Nat.beq (Q5J 0) ONEP && Nat.beq (Q59 0) 273 && Nat.beq (Q5RJ 0) 0 && Nat.beq (Q5RAR 0) 0) =
    true := by quickRfl

theorem q5_rel : eqK (fun q => Q5U (Q5RA q)) (fun q => Q5U (Q5RB q)) (fun q => Q5U (Q5RC q))
    (fun q => Q5U (Q5RD q)) 48 1 = true := by quickRfl

theorem q5_nrel : neK (fun q => Q5U (Q5NA q)) (fun q => Q5U (Q5NB q)) (fun q => Q5U (Q5NC q))
    (fun q => Q5U (Q5ND q)) 5 1 = true := by quickRfl

theorem q5_parX : parK Q5XPA Q5XPB Q5XPOS 2 1343 21 = true := by quickRfl

theorem q5_closX0 : closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 0 448 7 =
    true := by quickRfl
theorem q5_closX1 : closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 448 448 7 =
    true := by quickRfl
theorem q5_closX2 : closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 896 448 7 =
    true := by quickRfl
theorem q5_closX3 : closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 1344 448 7 =
    true := by quickRfl
theorem q5_closX4 : closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 1792 448 7 =
    true := by quickRfl
theorem q5_closX5 : closP Q5X (fun s => Q5U (Nat.add 11 (Nat.mul 3 s))) Q5XPOS 1344 2 2240 448 7 =
    true := by quickRfl

theorem q5_sortX : sortK Q5X Q5XSRT Q5XSRI 1344 21 = true := by quickRfl

theorem q5_genX : idxK Q5X Q5U Q5I5 1344 7 1 = true := by quickRfl

theorem q5_S : (parK Q5SPA Q5SPB Q5SPOS 5 63 1 && closP Q5S Q5U Q5SPOS 64 5 0 320 5 &&
    sortK Q5S Q5SSRT Q5SSRI 64 1) = true := by quickRfl

theorem q5_A : (parK Q5APA Q5APB Q5APOS 4 31 1 && closP Q5A Q5U Q5APOS 32 4 0 128 2 &&
    sortK Q5A Q5ASRT Q5ASRI 32 1) = true := by quickRfl

theorem q5_B : (parK Q5BPA Q5BPB Q5BPOS 4 31 1 &&
    closP Q5B (fun s => Q5U (Q5BG s)) Q5BPOS 32 4 0 128 2 && sortK Q5B Q5BSRT Q5BSRI 32 1) = true := by
  quickRfl

theorem q5_P : (parK Q5PPA Q5PPB Q5PPOS 2 191 3 &&
    closP Q5P (fun s => Q5U (Q5PG s)) Q5PPOS 192 2 0 384 6 && sortK Q5P Q5PSRT Q5PSRI 192 3) =
    true := by quickRfl

theorem q5_C : (parK Q5CPA Q5CPB Q5CPOS 2 191 3 &&
    closP Q5C (fun s => Q5U (Q5CG s)) Q5CPOS 192 2 0 384 6 && sortK Q5C Q5CSRT Q5CSRI 192 3) =
    true := by quickRfl

theorem q5_J : (parK Q5JPA Q5JPB Q5JPOS 2 15 1 &&
    closP Q5J (fun s => Q5U (Q5JG s)) Q5JPOS 16 2 0 32 1 && sortK Q5J Q5JSRT Q5JSRI 16 1) = true := by
  quickRfl

theorem q5_F : (basisK Q5F (fun s => Q5U (Q5FG s)) 3 8 1 && sortK Q5F Q5FSRT Q5FSRI 8 1) = true := by
  quickRfl

theorem q5_E : (basisK Q5E (fun s => Q5U (Q5EG s)) 3 8 1 && sortK Q5E Q5ESRT Q5ESRI 8 1) = true := by
  quickRfl

theorem q5_Y : (basisK Q5Y (fun s => Q5U (Q5YG s)) 3 8 1 && sortK Q5Y Q5YSRT Q5YSRI 8 1) = true := by
  quickRfl

theorem q5_cntB : Nat.beq (cntK Q5S (fun _ => Q5U 9) 1 64 1) 32 = true := by quickRfl

theorem q5_cntZB : Nat.beq (cntK Q5B (fun s => Q5U (Q5BG s)) 4 32 1) 4 = true := by quickRfl

theorem q5_normB : (eqK (fun q => Q5U (Q5PG (Nat.div q 4))) (fun q => Q5U (Q5BG (Nat.mod q 4)))
    (fun q => Q5B (Q5NBW q)) (fun q => Q5U (Q5PG (Nat.div q 4))) 8 1 && ltK Q5NBW 32 8 1) = true := by
  quickRfl

theorem q5_normJ : (eqK (fun q => Q5U (Q5PG (Nat.div q 2))) (fun q => Q5U (Q5JG (Nat.mod q 2)))
    (fun q => Q5J (Q5NJW q)) (fun q => Q5U (Q5PG (Nat.div q 2))) 4 1 && ltK Q5NJW 16 4 1) = true := by
  quickRfl

theorem q5_tauP : idxK Q5P (fun _ => Q5U 20) Q5TP 192 1 1 = true := by quickRfl

theorem q5_act : actK Q5F (fun s => Q5U (Q5MG s)) Q5M 9 1 = true := by quickRfl

theorem q5_gl : (parK Q59PA Q59PB Q59POS 2 167 3 && clos9 Q59 Q5M Q59POS 168 2 6 &&
    sortK Q59 Q59SRT Q59SRI 168 3) = true := by quickRfl

theorem q5_conjZ : (eqK (fun q => Q5U (Q5CZ q)) (fun _ => Q5U 10) (fun q => Q5F (Q5CZW q))
    (fun q => Q5U (Q5CZ q)) 7 1 && ltK Q5CZW 8 7 1 &&
    neqK (fun q => Q5CZW (Q5P7I q)) (fun q => Q5CZW (Q5P7J q)) 21 1) = true := by quickRfl

theorem q5_conjB : (eqK (fun q => Q5U (Q5CBU q)) (fun q => Q5U (Q5CBV q)) (fun q => Q5F (Q5CBW q))
    (fun q => Q5U (Q5CBU q)) 14 1 && ltK Q5CBW 8 14 1 &&
    neqK (fun q => spanM (Q5CBW (Nat.mul 2 (Q5P7I q))) (Q5CBW (Nat.succ (Nat.mul 2 (Q5P7I q)))))
      (fun q => spanM (Q5CBW (Nat.mul 2 (Q5P7J q))) (Q5CBW (Nat.succ (Nat.mul 2 (Q5P7J q))))) 21 1) =
    true := by quickRfl

theorem q5_cosJ : (ltK Q5RJ 16 4 1 && ltK Q5RJW 16 4 1 && ltK Q5RJT 4 4 1 && ltK Q5RJZ 4 4 1 &&
    neqK (fun q => Q5RJT (Nat.succ q)) Nat.succ 3 1 &&
    eqK (fun _ => Q5U 20) (fun q => Q5J (Q5RJ q)) (fun q => Q5J (Q5RJW q)) (fun _ => Q5U 20) 4 1 &&
    eqK (fun q => Q5J (Q5RJW q)) (fun _ => Q5U 7) (fun q => Q5J (Q5RJ (Q5RJT q)))
      (fun q => Q5U (Q5ZB (Q5RJZ q))) 4 1 &&
    neK (fun q => Q5J (Q5RJ (Q5P4I (Nat.div q 4)))) (fun _ => Q5U 7)
      (fun q => Q5J (Q5RJ (Q5P4J (Nat.div q 4)))) (fun q => Q5U (Q5ZB (Nat.mod q 4))) 24 1) = true := by
  quickRfl

theorem q5_cosA : (ltK Q5RAR 32 4 1 && ltK Q5RAW 32 4 1 && ltK Q5RAT 4 4 1 && ltK Q5RAF 8 4 1 &&
    neqK (fun q => Q5RAT (Nat.succ q)) Nat.succ 3 1 &&
    eqK (fun _ => Q5U 5) (fun q => Q5A (Q5RAR q)) (fun q => Q5A (Q5RAW q)) (fun _ => Q5U 5) 4 1 &&
    eqK (fun q => Q5A (Q5RAW q)) (fun _ => Q5U 7) (fun q => Q5A (Q5RAR (Q5RAT q)))
      (fun q => Q5F (Q5RAF q)) 4 1 &&
    neK (fun q => Q5A (Q5RAR (Q5P4I (Nat.div q 8)))) (fun _ => Q5U 7)
      (fun q => Q5A (Q5RAR (Q5P4J (Nat.div q 8)))) (fun q => Q5F (Nat.mod q 8)) 48 1) = true := by
  quickRfl

theorem q5_f19 : (eqK (fun _ => Q5U 24) (fun q => Q5E (Nat.shiftLeft 1 q)) (fun q => Q5Y (Q5YW q))
    (fun _ => Q5U 24) 3 1 && ltK Q5YW 8 3 1) = true := by quickRfl

theorem q5_nine : (eqK (fun q => Q5U (Q5CE q)) (fun q => Q5E (Q5CEW q)) (fun _ => Q5U 10)
    (fun q => Q5U (Q5CE q)) 9 1 && ltK Q5CEW 8 9 1 &&
    eqK (fun q => Q5U (Q5EDJ q)) (fun q => Q5X (Q5EDD q)) (fun q => Q5U (Q5EDI q)) (fun _ => Q5U 7)
      36 1 && ltK Q5EDD 1344 36 1 && ltK Q5EDW 3 36 1) = true := by quickRfl

theorem q5_nineW : neK (fun q => Q5X (Q5EDD (Nat.div q 8)))
    (fun q => Q5E (Nat.shiftLeft 1 (Q5EDW (Nat.div q 8)))) (fun q => Q5E (Nat.mod q 8))
    (fun q => Q5X (Q5EDD (Nat.div q 8))) 288 5 = true := by quickRfl

theorem q5_sq : (sqInK Q5S Q5F Q5IQ 8 64 1 && ltK Q5XS2 64 1 1 &&
    neK (fun _ => Q5S (Q5XS2 0)) (fun _ => Q5S (Q5XS2 0)) (fun q => Q5F q) (fun _ => Q5U 7) 8 1) =
    true := by quickRfl

end CFSG.KD.G2Three.Sec1

end
