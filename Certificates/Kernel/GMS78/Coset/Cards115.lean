module

public import Certificates.Kernel.GMS78.Coset.Cards
public import Certificates.Data.GMS78RuNECheck
public import Certificates.Kernel.GMS78.Coset.XGRuM1
public import Certificates.Kernel.GMS78.Coset.XGRuP3b
public import Certificates.Kernel.GMS78.Coset.XGRuBb4
public import Certificates.Kernel.GMS78.Coset.XGRuBb3
public import Certificates.Kernel.GMS78.Coset.XGRuBb2
public import Certificates.Kernel.GMS78.Coset.XGRuBb1
public import Certificates.Kernel.GMS78.Coset.XGRuPi7b

public section

namespace CertificateChecks.KernelGMS78.Coset

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ComponentClassification.GMS78.RuNE
  CFSG.ComponentClassification.GMS78.RuPi7

theorem m4_eq : relsM1B.map encW = CFSG.KBRoute.XGRuB4.rels := by rfl

theorem m3_eq : (restrictWords (subsetOf _ [0, 1, 2]) relsM1B).map encW =
    CFSG.KBRoute.XGRuB3.rels := by rfl

theorem m2_eq : (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) relsM1B)).map encW = CFSG.KBRoute.XGRuB2.rels := by
  rfl

theorem m1_eq : (restrictWords (subsetOf _ [0]) (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) relsM1B))).map encW = CFSG.KBRoute.XGRuB1.rels := by
  rfl

theorem card_M1B : Finite (PG sub1B.length relsM1B) ∧ Nat.card (PG sub1B.length relsM1B) ≤ 4096 :=
  card_chainB relsM1B m4_eq m3_eq m2_eq m1_eq

theorem bb4_eq : relsBb.map encW = CFSG.KBRoute.XGRuBb4.rels := by rfl

theorem bb3_eq : (restrictWords (subsetOf _ [0, 1, 2]) relsBb).map encW =
    CFSG.KBRoute.XGRuBb3.rels := by rfl

theorem bb2_eq : (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) relsBb)).map encW = CFSG.KBRoute.XGRuBb2.rels := by
  rfl

theorem bb1_eq : (restrictWords (subsetOf _ [0]) (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) relsBb))).map encW = CFSG.KBRoute.XGRuBb1.rels := by
  rfl

theorem wb4_eq : CFSG.KBRoute.XGRuBb4.T1.words =
    (subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)] := by rfl

theorem wb3_eq : CFSG.KBRoute.XGRuBb3.T1.words =
    (subsetOf 3 [0, 1]).map fun x => [(x.val, true)] := by rfl

theorem wb2_eq : CFSG.KBRoute.XGRuBb2.T1.words =
    (subsetOf 2 [0]).map fun x => [(x.val, true)] := by rfl

theorem wb1_eq : CFSG.KBRoute.XGRuBb1.T1.words = [] := by rfl

theorem card_Bb : Finite (PG subB.length relsBb) ∧ Nat.card (PG subB.length relsBb) ≤ 4096 := by
  have t1 := CertificateChecks.KernelMiscCoset.XGRuBb1.t1
  unfold CFSG.KBRoute.XGRuBb1.T1.ok at t1
  obtain ⟨f1, c1⟩ := card_le_of_tableOk _ bb1_eq t1 (by decide) CFSG.KBRoute.XGRuBb1.top wb1_eq
  have t2 := CertificateChecks.KernelMiscCoset.XGRuBb2.t1
  unfold CFSG.KBRoute.XGRuBb2.T1.ok at t2
  obtain ⟨fi2, ix2⟩ := genSub_index_le_of_tableOk _ bb2_eq t2 (by decide)
    CFSG.KBRoute.XGRuBb2.top _ wb2_eq
  obtain ⟨f2, c2⟩ := @card_le_of_genSub_index _ _ _ _ fi2 ix2 f1
  have t3 := CertificateChecks.KernelMiscCoset.XGRuBb3.t1
  unfold CFSG.KBRoute.XGRuBb3.T1.ok at t3
  obtain ⟨fi3, ix3⟩ := genSub_index_le_of_tableOk _ bb3_eq t3 (by decide)
    CFSG.KBRoute.XGRuBb3.top _ wb3_eq
  obtain ⟨f3, c3⟩ := @card_le_of_genSub_index _ _ _ _ fi3 ix3 f2
  have t4 := CertificateChecks.KernelMiscCoset.XGRuBb4.t1
  unfold CFSG.KBRoute.XGRuBb4.T1.ok at t4
  obtain ⟨fi4, ix4⟩ := genSub_index_le_of_tableOk _ bb4_eq t4 (by decide)
    CFSG.KBRoute.XGRuBb4.top _ wb4_eq
  obtain ⟨f4, c4⟩ := @card_le_of_genSub_index _ _ _ _ fi4 ix4 f3
  refine ⟨f4, c4.trans ?_⟩
  calc 16 * Nat.card _ ≤ 16 * (32 * (2 * 4)) :=
        Nat.mul_le_mul_left _ (c3.trans (Nat.mul_le_mul_left _ (c2.trans
          (Nat.mul_le_mul_left _ c1))))
    _ = 4096 := by norm_num

theorem pm1_eq : relsM1.map encW = CFSG.KBRoute.XGRuM1.rels := by rfl

theorem wm1_eq : CFSG.KBRoute.XGRuM1.T1.words =
    (subsetOf 6 [0, 1, 2, 3]).map fun x => [(x.val, true)] := by rfl

theorem card_M1 : Finite (PG sub1.length relsM1) ∧ Nat.card (PG sub1.length relsM1) ≤ 245760 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuM1.t1
  unfold CFSG.KBRoute.XGRuM1.T1.ok at t
  obtain ⟨fi, ix⟩ := genSub_index_le_of_tableOk _ pm1_eq t (by decide) CFSG.KBRoute.XGRuM1.top _
    wm1_eq
  obtain ⟨f, c⟩ := @card_le_of_genSub_index _ relsM1 _ _ fi ix card_M1B.1
  exact ⟨f, c.trans ((Nat.mul_le_mul_left 60 card_M1B.2).trans (by norm_num))⟩

theorem p3b_eq : relsP3b.map encW = CFSG.KBRoute.XGRuP3b.rels := by rfl

theorem wp3b_eq : CFSG.KBRoute.XGRuP3b.T1.words =
    (subsetOf 6 [0, 1, 2, 3]).map fun x => [(x.val, true)] := by rfl

theorem card_P3b : Finite (PG sub3.length relsP3b) ∧
    Nat.card (PG sub3.length relsP3b) ≤ 189 * 4096 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuP3b.t1
  unfold CFSG.KBRoute.XGRuP3b.T1.ok at t
  obtain ⟨fi, ix⟩ := genSub_index_le_of_tableOk _ p3b_eq t (by decide) CFSG.KBRoute.XGRuP3b.top _
    wp3b_eq
  obtain ⟨f, c⟩ := @card_le_of_genSub_index _ relsP3b _ _ fi ix card_Bb.1
  exact ⟨f, c.trans (Nat.mul_le_mul_left 189 card_Bb.2)⟩

theorem pi7b_eq : pi7bRels.map encW = CFSG.KBRoute.XGRuPi7b.rels := by rfl

theorem wpi7b_eq : CFSG.KBRoute.XGRuPi7b.T1.words =
    (subsetOf 7 pi7Sub).map fun x => [(x.val, true)] := by rfl

theorem card_pi7b : Finite (PG 7 pi7bRels) ∧ Nat.card (PG 7 pi7bRels) ≤ 145926144000 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuPi7b.t1
  unfold CFSG.KBRoute.XGRuPi7b.T1.ok at t
  obtain ⟨fi, ix⟩ := genSub_index_le_of_tableOk _ pi7b_eq t (by decide) CFSG.KBRoute.XGRuPi7b.top _
    wpi7b_eq
  obtain ⟨f, c⟩ := @card_le_of_genSub_index _ pi7bRels _ _ fi ix card_P3b.1
  exact ⟨f, c.trans ((Nat.mul_le_mul_left 188500 card_P3b.2).trans (by norm_num))⟩

end CertificateChecks.KernelGMS78.Coset

end
