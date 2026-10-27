module

public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.GMS78.Coset.XGRuE1
public import Certificates.Kernel.GMS78.Coset.XGRuE2
public import Certificates.Kernel.GMS78.Coset.XGRuE3
public import Certificates.Kernel.GMS78.Coset.XGRuJ6
public import Certificates.Kernel.GMS78.Coset.XGRuP12t
public import Certificates.Kernel.GMS78.Coset.XGRuPi0
public import Certificates.Kernel.GMS78.Coset.XGRuPi7M1
public import Certificates.Data.GMS78RuCzRigidCheck

public section

namespace CertificateChecks.KernelGMS78.Coset

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ComponentClassification.GMS78.RuCz

theorem e1_eq : czEps1Rels.map encW = CFSG.KBRoute.XGRuE1.rels := by rfl

theorem e2_eq : czEps2Rels.map encW = CFSG.KBRoute.XGRuE2.rels := by rfl

theorem e3_eq : czEps3Rels.map encW = CFSG.KBRoute.XGRuE3.rels := by rfl

theorem we1_eq : CFSG.KBRoute.XGRuE1.T1.words = [] := by rfl

theorem we2_eq : CFSG.KBRoute.XGRuE2.T1.words = [] := by rfl

theorem we3_eq : CFSG.KBRoute.XGRuE3.T1.words = [] := by rfl

theorem card_eps1 : Finite (PG 10 czEps1Rels) ∧ Nat.card (PG 10 czEps1Rels) ≤ 122880 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuE1.t1
  unfold CFSG.KBRoute.XGRuE1.T1.ok at t
  exact card_le_of_tableOk _ e1_eq t (by decide) CFSG.KBRoute.XGRuE1.top we1_eq

theorem card_eps2 : Finite (PG 10 czEps2Rels) ∧ Nat.card (PG 10 czEps2Rels) ≤ 122880 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuE2.t1
  unfold CFSG.KBRoute.XGRuE2.T1.ok at t
  exact card_le_of_tableOk _ e2_eq t (by decide) CFSG.KBRoute.XGRuE2.top we2_eq

theorem card_eps3 : Finite (PG 10 czEps3Rels) ∧ Nat.card (PG 10 czEps3Rels) ≤ 122880 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuE3.t1
  unfold CFSG.KBRoute.XGRuE3.T1.ok at t
  exact card_le_of_tableOk _ e3_eq t (by decide) CFSG.KBRoute.XGRuE3.top we3_eq

theorem j6_eq : czRelsJW.map encW = CFSG.KBRoute.XGRuJ6.rels := by rfl

theorem wj6_eq : CFSG.KBRoute.XGRuJ6.T1.words = [] := by rfl

theorem card_J6 : Finite (PG 6 czRelsJW) ∧ Nat.card (PG 6 czRelsJW) ≤ 2048 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuJ6.t1
  unfold CFSG.KBRoute.XGRuJ6.T1.ok at t
  exact card_le_of_tableOk _ j6_eq t (by decide) CFSG.KBRoute.XGRuJ6.top wj6_eq

theorem p12t_eq : p12Rels.map encW = CFSG.KBRoute.XGRuP12t.rels := by rfl

theorem wp12t_eq : CFSG.KBRoute.XGRuP12t.T1.words = [] := by rfl

theorem card_P12 : Finite (PG sub9.length p12Rels) ∧ Nat.card (PG sub9.length p12Rels) ≤ 49152 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuP12t.t1
  unfold CFSG.KBRoute.XGRuP12t.T1.ok at t
  exact card_le_of_tableOk _ p12t_eq t (by decide) CFSG.KBRoute.XGRuP12t.top wp12t_eq

theorem pi0_eq : czRels.map encW = CFSG.KBRoute.XGRuPi0.rels := by rfl

theorem wpi0_eq : CFSG.KBRoute.XGRuPi0.T1.words =
    (subsetOf 10 [0, 1, 2, 3, 4, 5, 6, 7, 8]).map fun x => [(x.val, true)] := by rfl

theorem pi0_index :
    (genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9).index ≤ 5 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuPi0.t1
  unfold CFSG.KBRoute.XGRuPi0.T1.ok at t
  exact genSub_index_le_of_tableOk _ pi0_eq t (by decide) CFSG.KBRoute.XGRuPi0.top _ wpi0_eq

theorem pi7m1_eq : CFSG.ComponentClassification.GMS78.RuPi7.pi7Rels.map encW =
    CFSG.KBRoute.XGRuPi7M1.rels := by rfl

theorem wpi7m1_eq : CFSG.KBRoute.XGRuPi7M1.T1.words =
    (subsetOf 7 [0, 1, 2, 3, 4, 5]).map fun x => [(x.val, true)] := by rfl

theorem pi7m1_index :
    (genSub {r : FreeGroup (Fin 7) | r ∈ CFSG.ComponentClassification.GMS78.RuPi7.pi7Rels.map
      FreeGroup.mk} (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 7) | r ∈ CFSG.ComponentClassification.GMS78.RuPi7.pi7Rels.map
      FreeGroup.mk} (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 593775 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuPi7M1.t1
  unfold CFSG.KBRoute.XGRuPi7M1.T1.ok at t
  exact genSub_index_le_of_tableOk _ pi7m1_eq t (by decide) CFSG.KBRoute.XGRuPi7M1.top _ wpi7m1_eq

end CertificateChecks.KernelGMS78.Coset

end
