module

public import Certificates.Kernel.TwoHSLe4.TFQ
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw

public section

namespace CertificateChecks.KernelTwoHSLe4.TF

open CFSG.EvenSporadicStandard.TwoHS

theorem ck1T : eqLR (tLd (sLd a1d)) td1 = true := by quickRfl

theorem ck1_1 : allL wfB (sLd a1d) = true := by quickRfl

theorem ck1_2 : allL wfB td1 = true := by quickRfl

theorem ck1_4 : memR R4.one td1 = true := by quickRfl

theorem ck1_5a : allL (fun a => allL (fun g => memK (rmul a g) td1) gl1) td1 = true := by quickRfl

theorem ck1_5b : treeK gl1 tb1 [] = true := by quickRfl

theorem ck1_5c : allL (fun x => anyL (fun e => r4eq e.1 x) tb1) td1 = true := by quickRfl

theorem ck1_7a : subLR ts1 (sLd a1d) = true := by quickRfl

theorem ck1_7b : allL (fun a => memR a ts1) td1 = true := by quickRfl

theorem ck1_8 : allL (fun s => memR s td1) shd = true := by quickRfl

theorem ck1_9 : allL (fun a => r4eq (rpow2 7 a) R4.one) td1 = true := by quickRfl

theorem ck1_10 : starB vd td1 = true := by quickRfl

theorem ck1_11 : allL (fun v => Nat.ble (colV (td1.map fun a => rmv a v)).length 4) fd = true := by
  quickRfl

theorem ck1_12 :
    allL (fun v => Nat.blt 4 (colV (td1.map fun a => rmv a (radd tvd v))).length) fd = true := by
  quickRfl

theorem ck1_13 : allL (fun v => anyL (fun a => rveq (rmv a tvd) (radd tvd v)) td1) fd = true := by
  quickRfl

theorem ck1_14 :
    allL (fun a => !allL (fun v => rveq (rmv a v) v) fd || r4eq (rmul a a) R4.one) td1 = true := by
  quickRfl

theorem ck1_15 : allL (fun a => !allL (fun v => rveq (rmv a v) v) omd || r4eq a R4.one ||
    r4eq a R4.negOne) td1 = true := by
  quickRfl

theorem ck1_16 : allL (fun a => !rveq (rmv a tvd) tvd || memR a shd) td1 = true := by quickRfl

theorem ck1_17a : allL (fun a => memR a td1) td1 = true := by quickRfl

theorem ck1_hm : allL (fun t => bitB hm1 (Nat.mod (keyH t) 4093)) td1 = true := by quickRfl

theorem ck1_17 : nrmK td1 td1 hm1 4093 (sLd a1d) (siLd ai1) = true := by quickRfl

theorem traw1 : TRaw (S (toR4 alpha1)) (T (toR4 alpha1)) (I (toR4 alpha1)) := by
  have hT : T (toR4 alpha1) = td1 := by
    rw [T_eq, ha1]
    exact eqLR_eq _ _ ck1T
  have hS : S (toR4 alpha1) = sLd a1d := by rw [S_eq, ha1]
  change TRaw (S (toR4 alpha1)) (T (toR4 alpha1)) (invPairsR (T (toR4 alpha1)))
  rw [hS, hT]
  exact traw_of hsh hfR homR htRV ckvd ck1_1 ck1_2 ck1_4 ck1_5a ck1_5b ck1_5c ck1_7a ck1_7b ck1_8
    ck1_9 ck1_10 ck1_11 ck1_12 ck1_13 ck1_14 ck1_15 ck1_16 ck1_17a ck1_hm ck1_17

theorem tfR_alpha1 : tfR (toR4 alpha1) = true := tfR_of_traw traw1

end CertificateChecks.KernelTwoHSLe4.TF
