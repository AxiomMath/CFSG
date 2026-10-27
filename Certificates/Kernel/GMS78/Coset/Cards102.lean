module

public import Certificates.Kernel.GMS78.Coset.Cards
public import Certificates.Data.GMS78RuPi7Check
public import Certificates.Kernel.GMS78.Coset.XGRuP3
public import Certificates.Kernel.GMS78.Coset.XGRuPi7

public section

namespace CertificateChecks.KernelGMS78.Coset

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ComponentClassification.GMS78.RuPi7

theorem rb4_eq : relsB.map encW = CFSG.KBRoute.XGRuB4.rels := by rfl

theorem rb3_eq : (restrictWords (subsetOf _ [0, 1, 2]) relsB).map encW =
    CFSG.KBRoute.XGRuB3.rels := by rfl

theorem rb2_eq : (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) relsB)).map encW = CFSG.KBRoute.XGRuB2.rels := by
  rfl

theorem rb1_eq : (restrictWords (subsetOf _ [0]) (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) relsB))).map encW = CFSG.KBRoute.XGRuB1.rels := by
  rfl

theorem card_relsB : Finite (PG subB.length relsB) ∧ Nat.card (PG subB.length relsB) ≤ 4096 :=
  card_chainB relsB rb4_eq rb3_eq rb2_eq rb1_eq

theorem p3_eq : relsP3.map encW = CFSG.KBRoute.XGRuP3.rels := by rfl

theorem wp3_eq : CFSG.KBRoute.XGRuP3.T1.words =
    (subsetOf 6 [0, 1, 2, 3]).map fun x => [(x.val, true)] := by rfl

theorem card_relsP3 : Finite (PG sub3.length relsP3) ∧
    Nat.card (PG sub3.length relsP3) ≤ 189 * 4096 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuP3.t1
  unfold CFSG.KBRoute.XGRuP3.T1.ok at t
  obtain ⟨fi, ix⟩ := genSub_index_le_of_tableOk _ p3_eq t (by decide) CFSG.KBRoute.XGRuP3.top _
    wp3_eq
  obtain ⟨f, c⟩ := @card_le_of_genSub_index _ relsP3 _ _ fi ix card_relsB.1
  exact ⟨f, c.trans (Nat.mul_le_mul_left 189 card_relsB.2)⟩

theorem pi7_eq : pi7Rels.map encW = CFSG.KBRoute.XGRuPi7.rels := by rfl

theorem wpi7_eq : CFSG.KBRoute.XGRuPi7.T1.words =
    (subsetOf 7 pi7Sub).map fun x => [(x.val, true)] := by rfl

theorem card_pi7 : Finite (PG 7 pi7Rels) ∧ Nat.card (PG 7 pi7Rels) ≤ 145926144000 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuPi7.t1
  unfold CFSG.KBRoute.XGRuPi7.T1.ok at t
  obtain ⟨fi, ix⟩ := genSub_index_le_of_tableOk _ pi7_eq t (by decide) CFSG.KBRoute.XGRuPi7.top _
    wpi7_eq
  obtain ⟨f, c⟩ := @card_le_of_genSub_index _ pi7Rels _ _ fi ix card_relsP3.1
  exact ⟨f, c.trans ((Nat.mul_le_mul_left 188500 card_relsP3.2).trans (by norm_num))⟩

end CertificateChecks.KernelGMS78.Coset

end
