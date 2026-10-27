module

public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.CosetTableColumns
public import Certificates.Data.GMS78RuAsmNA
public import Certificates.Kernel.GMS78.Coset.XGRuP2
public import Certificates.Kernel.GMS78.Coset.XGRuB4
public import Certificates.Kernel.GMS78.Coset.XGRuB3
public import Certificates.Kernel.GMS78.Coset.XGRuB2
public import Certificates.Kernel.GMS78.Coset.XGRuB1

public section

namespace CertificateChecks.KernelGMS78.Coset

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ComponentClassification.GMS78.RuAsm

theorem b4_eq : ruRels2B.map encW = CFSG.KBRoute.XGRuB4.rels := by rfl

theorem b3_eq : (restrictWords (subsetOf _ [0, 1, 2]) ruRels2B).map encW =
    CFSG.KBRoute.XGRuB3.rels := by rfl

theorem b2_eq : (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) ruRels2B)).map encW = CFSG.KBRoute.XGRuB2.rels := by
  rfl

theorem b1_eq : (restrictWords (subsetOf _ [0]) (restrictWords (subsetOf _ [0, 1])
    (restrictWords (subsetOf _ [0, 1, 2]) ruRels2B))).map encW = CFSG.KBRoute.XGRuB1.rels := by
  rfl

theorem w4_eq : CFSG.KBRoute.XGRuB4.T1.words =
    (subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)] := by rfl

theorem w3_eq : CFSG.KBRoute.XGRuB3.T1.words =
    (subsetOf 3 [0, 1]).map fun x => [(x.val, true)] := by rfl

theorem w2_eq : CFSG.KBRoute.XGRuB2.T1.words =
    (subsetOf 2 [0]).map fun x => [(x.val, true)] := by rfl

theorem w1_eq : CFSG.KBRoute.XGRuB1.T1.words = [] := by rfl

theorem card_chainB (ws : List (List (Fin 4 × Bool))) (h4 : ws.map encW = CFSG.KBRoute.XGRuB4.rels)
    (h3 : (restrictWords (subsetOf 4 [0, 1, 2]) ws).map encW = CFSG.KBRoute.XGRuB3.rels)
    (h2 : (restrictWords (subsetOf 3 [0, 1]) (restrictWords (subsetOf 4 [0, 1, 2]) ws)).map encW =
      CFSG.KBRoute.XGRuB2.rels)
    (h1 : (restrictWords (subsetOf 2 [0]) (restrictWords (subsetOf 3 [0, 1])
      (restrictWords (subsetOf 4 [0, 1, 2]) ws))).map encW = CFSG.KBRoute.XGRuB1.rels) :
    Finite (PG 4 ws) ∧ Nat.card (PG 4 ws) ≤ 4096 := by
  have t1 := CertificateChecks.KernelMiscCoset.XGRuB1.t1
  unfold CFSG.KBRoute.XGRuB1.T1.ok at t1
  obtain ⟨f1, c1⟩ := card_le_of_tableOk _ h1 t1 (by decide) CFSG.KBRoute.XGRuB1.top w1_eq
  have t2 := CertificateChecks.KernelMiscCoset.XGRuB2.t1
  unfold CFSG.KBRoute.XGRuB2.T1.ok at t2
  obtain ⟨fi2, ix2⟩ := genSub_index_le_of_tableOk _ h2 t2 (by decide) CFSG.KBRoute.XGRuB2.top _
    w2_eq
  obtain ⟨f2, c2⟩ := @card_le_of_genSub_index _ _ _ _ fi2 ix2 f1
  have t3 := CertificateChecks.KernelMiscCoset.XGRuB3.t1
  unfold CFSG.KBRoute.XGRuB3.T1.ok at t3
  obtain ⟨fi3, ix3⟩ := genSub_index_le_of_tableOk _ h3 t3 (by decide) CFSG.KBRoute.XGRuB3.top _
    w3_eq
  obtain ⟨f3, c3⟩ := @card_le_of_genSub_index _ _ _ _ fi3 ix3 f2
  have t4 := CertificateChecks.KernelMiscCoset.XGRuB4.t1
  unfold CFSG.KBRoute.XGRuB4.T1.ok at t4
  obtain ⟨fi4, ix4⟩ := genSub_index_le_of_tableOk _ h4 t4 (by decide) CFSG.KBRoute.XGRuB4.top _
    w4_eq
  obtain ⟨f4, c4⟩ := @card_le_of_genSub_index _ _ _ _ fi4 ix4 f3
  refine ⟨f4, c4.trans ?_⟩
  calc 16 * Nat.card _ ≤ 16 * (32 * (2 * 4)) :=
        Nat.mul_le_mul_left _ (c3.trans (Nat.mul_le_mul_left _ (c2.trans
          (Nat.mul_le_mul_left _ c1))))
    _ = 4096 := by norm_num

theorem card_B : Finite (PG ruSub2B.length ruRels2B) ∧ Nat.card (PG ruSub2B.length ruRels2B) ≤ 4096 :=
  card_chainB ruRels2B b4_eq b3_eq b2_eq b1_eq

theorem p2_eq : ruRels2.map encW = CFSG.KBRoute.XGRuP2.rels := by rfl

theorem wp2_eq : CFSG.KBRoute.XGRuP2.T1.words =
    (subsetOf 6 [0, 1, 2, 3]).map fun x => [(x.val, true)] := by rfl

theorem card_P2 : Finite (PG ruSub2.length ruRels2) ∧
    Nat.card (PG ruSub2.length ruRels2) ≤ 344064 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuP2.t1
  unfold CFSG.KBRoute.XGRuP2.T1.ok at t
  obtain ⟨fi, ix⟩ := genSub_index_le_of_tableOk _ p2_eq t (by decide) CFSG.KBRoute.XGRuP2.top _
    wp2_eq
  obtain ⟨f, c⟩ := @card_le_of_genSub_index _ ruRels2 _ _ fi ix card_B.1
  exact ⟨f, c.trans ((Nat.mul_le_mul_left 84 card_B.2).trans (by norm_num))⟩

end CertificateChecks.KernelGMS78.Coset

end
