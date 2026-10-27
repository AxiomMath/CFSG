module

public import Certificates.Kernel.P1L43.FbarGlue
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.K442264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelP1L43 CFSG.ComponentClassification.HarrisLit.P1.L43
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KC.Misc.ArrEnum
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.HarrisLit.P1
open Certificates.Asc82Fbar CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Co2.Native

theorem inner_eq : innerOK 80 100000 l43Sift (tm 11821474) (tm 22222087) (tm 30806896)
    (fbarInner ()) =
    (enumOK 80 100000 360 [tm 22222087, tm 30806896] &&
      CFSG.Sporadic.SmallOddCore.permOK 80 (tm 37301281) && involOK 80 (tm 37301281) &&
      memT 80 (mulClosureH 80 [tm 22222087, tm 30806896].toArray 100000).1 (tm 37301281) &&
      allInvConj 80 (mulClosureH 80 [tm 22222087, tm 30806896].toArray 100000).1 (tm 37301281) &&
      CFSG.Sporadic.SmallOddCore.permOK 80 (tm 38099616) &&
      invOK 80 (tm 38099616) (invT 80 (tm 38099616)) && l43Sift (tm 38099616) &&
      tblEq 80 (compT 80 (tm 38099616) (tm 11821474)) (compT 80 (tm 37301281) (tm 38099616)) &&
      CFSG.Sporadic.SmallOddCore.permOK 80
        (conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 22222087)) &&
      CFSG.Sporadic.SmallOddCore.permOK 80
        (conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 30806896)) &&
      decide (centCount 80 100000 [tm 22222087, tm 30806896]
        [tm 37301281, conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 22222087),
          conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 30806896)] ≤ 2) &&
      [tm 23098396, tm 11712909].all (fun r => CFSG.Sporadic.SmallOddCore.permOK 80 r &&
        involOK 80 r &&
        memT 80 (mulClosureH 80 [tm 22222087, tm 30806896].toArray 100000).1 r &&
        commTT 80 r (tm 37301281)) &&
      enumOK 80 100000 8 [tm 23098396, tm 11712909]) := rfl

theorem inner_true : innerOK 80 100000 l43Sift (tm 11821474) (tm 22222087) (tm 30806896)
    (fbarInner ()) = true := by
  obtain ⟨-, hcI, hhI, hGI, hgjI, hcnI⟩ := rec_facts fb442headI
  obtain ⟨-, hcR, hhR, hGR, hgjR, hcnR⟩ := rec_facts fb442headR
  obtain ⟨b1, b2, -, -, -, -, b7, b8, b9, b10, b11, -, -, -⟩ := fb442binds
  have eL1 := tab_of b1
  have eL2 := tab_of b2
  have eB := tab_of b7
  have eC := tab_of b8
  have eR1 := tab_of b9
  have eR2 := tab_of b10
  have eT := tab_of b11
  have hi := fb442innK
  unfold fb442inn at hi
  simp only [bAnd_iff] at hi
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19⟩ :=
    hi
  have cF : ∀ j < 10, Cn 80 7 (FB j) := fun j hj => allN_spec i1 j hj
  have cB := cF 0 (by norm_num)
  have cC := cF 1 (by norm_num)
  have cCI := cF 2 (by norm_num)
  have cR1 := cF 3 (by norm_num)
  have cR2 := cF 4 (by norm_num)
  have cT := cF 5 (by norm_num)
  have hpI : ∀ i < FI.cnt, penumPtK 80 7 (mask 7) (80 * 7) true FI.G FI.GI 2 FI.cnt FI.T FI.PL
      FI.POS FI.SRT FI.SRI i = true :=
    peAll (L := 120) (K := 3) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exacts [fb442peI0, fb442peI1, fb442peI2]
  have hsI : ∀ i < FI.cnt, hsortPtK 80 7 (mask 7) FI.cnt FI.T FI.HS FI.HSI i = true :=
    slAll (L := 360) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442hsI0
  have hclI : ∀ c < Nat.mul FI.cnt 4, findPtK FI.cnt FI.T
      (prodQK 80 7 (mask 7) 4 FI.T (bothK 2 FI.GI FII)) FICl c = true :=
    slAll (L := 360) (K := 4) (by norm_num) (hcI ▸ (by decide : Nat.mul 360 4 ≤ 360 * 4))
      fun q hq => by
        interval_cases q
        exacts [fb442clI0, fb442clI1, fb442clI2, fb442clI3]
  have hpR : ∀ i < FR.cnt, penumPtK 80 7 (mask 7) (80 * 7) true FR.G FR.GI 2 FR.cnt FR.T FR.PL
      FR.POS FR.SRT FR.SRI i = true :=
    peAll (L := 8) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442peR0
  have hsR : ∀ i < FR.cnt, hsortPtK 80 7 (mask 7) FR.cnt FR.T FR.HS FR.HSI i = true :=
    slAll (L := 8) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442hsR0
  have hclR : ∀ c < Nat.mul FR.cnt 4, findPtK FR.cnt FR.T
      (prodQK 80 7 (mask 7) 4 FR.T (bothK 2 FR.GI FRI)) FRCl c = true :=
    slAll (L := 32) (K := 1) (by norm_num) (hcR ▸ (by decide : Nat.mul 8 4 ≤ 32 * 1))
      fun q hq => by
        interval_cases q
        exact fb442clR0
  have hTI : ∀ i < FI.cnt, Cn 80 7 (FI.T i) := fun i hi => penumPt_canon (hpI i hi)
  have tI : TabsOK 80 7 2 FI.GI [tm 22222087, tm 30806896].toArray := tabs2 eL1 eL2 hcnI
  have tR : TabsOK 80 7 2 FR.GI [tm 23098396, tm 11712909].toArray :=
    tabs2 (by rw [eR1, Nat.eq_of_beq_eq_true i18]) (by rw [eR2, Nat.eq_of_beq_eq_true i19]) hcnR
  have hmI := (mulH_sound fb442sz hGI tI hhI hpI hsI).1
  have eci : invT 80 (tm 38099616) = tb 80 7 (FB 2) := by
    rw [eC]
    exact invT_unpack (by norm_num) (invS_spec i5).2.2
  have ccj0 : Cn 80 7 (fb442cj 0) := cn_pp (cn_pp cC (hcnI 0 (by norm_num))) cCI
  have ccj1 : Cn 80 7 (fb442cj 1) := cn_pp (cn_pp cC (hcnI 1 (by norm_num))) cCI
  have ecj0 : conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 22222087) = tb 80 7 (fb442cj 0) := by
    rw [eci, eC, eL1]
    exact conjT_unpack cC cCI (hcnI 0 (by norm_num))
  have ecj1 : conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 30806896) = tb 80 7 (fb442cj 1) := by
    rw [eci, eC, eL2]
    exact conjT_unpack cC cCI (hcnI 1 (by norm_num))
  have hcount : decide (centCount 80 100000 [tm 22222087, tm 30806896]
      [tm 37301281, conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 22222087),
        conjT 80 (tm 38099616) (invT 80 (tm 38099616)) (tm 30806896)] ≤ 2) = true := by
    rw [ecj0, ecj1, eB]
    have e := centCount_eq (q := fb442qC) (hi := 6) fb442sz hGI tI hhI hpI hsI (by omega)
      (cs := [tm 22222087, tm 30806896]) (gs := [tb 80 7 (FB 0), tb 80 7 (fb442cj 0),
        tb 80 7 (fb442cj 1)]) fun i hi => by
        have et : tabT (unpack 80 7 (FI.T i)) = tb 80 7 (FI.T i) := rfl
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [et, commTT_tb (hTI i hi) cB, commTT_tb (hTI i hi) ccj0, commTT_tb (hTI i hi) ccj1]
        unfold fb442qC
        cases commP 80 7 (FI.T i) (FB 0) <;> cases commP 80 7 (FI.T i) (fb442cj 0) <;>
          cases commP 80 7 (FI.T i) (fb442cj 1) <;> rfl
    rw [e]
    exact decide_eq_true (Nat.le_of_ble_eq_true i9)
  rw [inner_eq, hmI]
  simp only [Bool.and_eq_true, and_assoc, List.all_cons, List.all_nil, Bool.and_true]
  refine ⟨enumOK_of fb442sz hGI tI hgjI hhI hpI hsI hclI hcI, ?_, ?_, ?_, ?_, ?_, ?_,
    sift_of' _ fb442sift.1, ?_, ?_, ?_, hcount, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    enumOK_of fb442sz hGR tR hgjR hhR hpR hsR hclR hcR⟩
  · rw [eB]
    exact perm_tb i2
  · rw [eB]
    exact invol_tb cB i3
  · rw [eB]
    exact memT_rec (Q := fun _ => FB 0) (POS := FIx) (j := 0) cB rfl i4
  · rw [eB]
    exact allInvConj_of hTI cB (slAll (L := 360) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442wtI0)
  · rw [eC]
    exact perm_tb i5
  · rw [eci, eC]
    obtain ⟨x1, x2, x3⟩ := invS_spec i5
    exact invOK_unpack x1 x2 x3
  · rw [eC, eT, eB, compT_tb cC cT, compT_tb cB cC, tblEq_tb (cn_pp cC cT) (cn_pp cB cC)]
    exact i6
  · rw [ecj0]
    exact perm_tb i7
  · rw [ecj1]
    exact perm_tb i8
  · rw [eR1]
    exact perm_tb i10
  · rw [eR1]
    exact invol_tb cR1 i11
  · rw [eR1]
    exact memT_rec (Q := fun _ => FB 3) (POS := FIx) (j := 1) cR1 rfl i13
  · rw [eR1, eB, commTT_tb cR1 cB]
    exact i12
  · rw [eR2]
    exact perm_tb i14
  · rw [eR2]
    exact invol_tb cR2 i15
  · rw [eR2]
    exact memT_rec (Q := fun _ => FB 4) (POS := FIx) (j := 2) cR2 rfl i17
  · rw [eR2, eB, commTT_tb cR2 cB]
    exact i16

end CertificateChecks.K442264

end
