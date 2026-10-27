module

public import Certificates.Kernel.TwoHSLe4.TFQ
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw

public section

namespace CertificateChecks.KernelTwoHSLe4.TF

open CFSG.EvenSporadicStandard.TwoHS

theorem ck2T : eqLR (tLd (sLd a2d)) td2 = true := by quickRfl

theorem ck2_1 : allL wfB (sLd a2d) = true := by quickRfl

theorem ck2_2 : allL wfB td2 = true := by quickRfl

theorem ck2_4 : memR R4.one td2 = true := by quickRfl

theorem ck2_5a : allL (fun a => allL (fun g => memK (rmul a g) td2) gl2) td2 = true := by quickRfl

theorem ck2_5b : treeK gl2 tb2 [] = true := by quickRfl

theorem ck2_5c : allL (fun x => anyL (fun e => r4eq e.1 x) tb2) td2 = true := by quickRfl

theorem ck2_7a : subLR ts2 (sLd a2d) = true := by quickRfl

theorem ck2_7b : allL (fun a => memR a ts2) td2 = true := by quickRfl

theorem ck2_8 : allL (fun s => memR s td2) shd = true := by quickRfl

theorem ck2_9 : allL (fun a => r4eq (rpow2 7 a) R4.one) td2 = true := by quickRfl

theorem ck2_10 : starB vd td2 = true := by quickRfl

theorem ck2_11 : allL (fun v => Nat.ble (colV (td2.map fun a => rmv a v)).length 4) fd = true := by
  quickRfl

theorem ck2_12 :
    allL (fun v => Nat.blt 4 (colV (td2.map fun a => rmv a (radd tvd v))).length) fd = true := by
  quickRfl

theorem ck2_13 : allL (fun v => anyL (fun a => rveq (rmv a tvd) (radd tvd v)) td2) fd = true := by
  quickRfl

theorem ck2_14 :
    allL (fun a => !allL (fun v => rveq (rmv a v) v) fd || r4eq (rmul a a) R4.one) td2 = true := by
  quickRfl

theorem ck2_15 : allL (fun a => !allL (fun v => rveq (rmv a v) v) omd || r4eq a R4.one ||
    r4eq a R4.negOne) td2 = true := by
  quickRfl

theorem ck2_16 : allL (fun a => !rveq (rmv a tvd) tvd || memR a shd) td2 = true := by quickRfl

theorem ck2_17a : allL (fun a => memR a td2) td2 = true := by quickRfl

theorem ck2_hm : allL (fun t => bitB hm2 (Nat.mod (keyH t) 4093)) td2 = true := by quickRfl

theorem ck2_17 : nrmK td2 td2 hm2 4093 (sLd a2d) (siLd ai2) = true := by quickRfl

theorem traw2 : TRaw (S (toR4 alpha2)) (T (toR4 alpha2)) (I (toR4 alpha2)) := by
  have hT : T (toR4 alpha2) = td2 := by
    rw [T_eq, ha2]
    exact eqLR_eq _ _ ck2T
  have hS : S (toR4 alpha2) = sLd a2d := by rw [S_eq, ha2]
  change TRaw (S (toR4 alpha2)) (T (toR4 alpha2)) (invPairsR (T (toR4 alpha2)))
  rw [hS, hT]
  exact traw_of hsh hfR homR htRV ckvd ck2_1 ck2_2 ck2_4 ck2_5a ck2_5b ck2_5c ck2_7a ck2_7b ck2_8
    ck2_9 ck2_10 ck2_11 ck2_12 ck2_13 ck2_14 ck2_15 ck2_16 ck2_17a ck2_hm ck2_17

theorem tfR_alpha2 : tfR (toR4 alpha2) = true := tfR_of_traw traw2

end CertificateChecks.KernelTwoHSLe4.TF
