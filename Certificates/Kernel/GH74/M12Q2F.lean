module

public import Certificates.Kernel.GH74.M12Q2
public import Certificates.Kernel.GH74.Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.M12Q2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.GH74.Generic.S45.EvSpor Certificates.IvkCent CertificateChecks.KernelGH74

theorem bIf_true_right (c t : Bool) : bIf(c, t, true) = (!c || t) := by cases c <;> rfl

theorem bIf_true_mid (c e : Bool) : bIf(c, true, e) = (c || e) := by cases c <;> rfl

theorem base : szOK 24 5 = true ∧ cK idK = true ∧ CFSG.KS.Prim.idK 24 5 (mask 5) = true ∧
    (∀ j < 5, cK (Q2.GI j) = true) ∧ (∀ j < 5, cK (Q2I j) = true) ∧ (∀ j < 3, cK (M12X j) = true) ∧
    (∀ j < 5, invEqK 24 5 (mask 5) (24 * 5) (Q2.GI j) (Q2I j) = true) ∧
    (∀ j < 5, Q2.G j = pidn 24 5) ∧ Q2.cnt = 384 ∧ penumHdK idK Q2.cnt 3000 Q2.T Q2.PL = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  exact ⟨a1, a2, a3, allN_spec a4, allN_spec a5, allN_spec a6, allN_spec a7,
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec a8 j hj), Nat.eq_of_beq_eq_true a9, a10⟩

theorem hidc : canonK 24 5 (mask 5) (24 * 5) (pidn 24 5) = true := base.2.1

theorem hid : idT 24 = tabT (unpack 24 5 (pidn 24 5)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem x_tab {j : Nat} (hj : j < 3) {x : Table}
    (hx : natArr x = unpack 24 5 (M12X j)) : x = tabT (unpack 24 5 (M12X j)) := by
  rw [← hx, tabT_natArr]

theorem x_tabs : m12KaB = tabT (unpack 24 5 (M12X 0)) ∧ m12ZT = tabT (unpack 24 5 (M12X 1)) ∧
    m12ST = tabT (unpack 24 5 (M12X 2)) := by
  have h := tabs_eq.2
  simp only [List.cons.injEq, and_true] at h
  exact ⟨x_tab (by norm_num) h.1, x_tab (by norm_num) h.2.1, x_tab (by norm_num) h.2.2⟩

theorem g_tabs : TabsOK 24 5 5 Q2.GI m12Q2Gens.toArray :=
  tabsOK_of_map tabs_eq.1 base.2.2.2.1

theorem g_invs : ∀ j < 5, invEqK 24 5 (mask 5) (24 * 5) (Q2.GI j) (Q2I j) = true ∧
    canonK 24 5 (mask 5) (24 * 5) (Q2I j) = true :=
  fun j hj => ⟨base.2.2.2.2.2.2.1 j hj, base.2.2.2.2.1 j hj⟩

theorem s_pe : ∀ i < Q2.cnt, penumPtK 24 5 (mask 5) (24 * 5) true Q2.G Q2.GI 5 Q2.cnt
    Q2.T Q2.PL Q2.POS Q2.SRT Q2.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < Q2.cnt, hsortPtK 24 5 (mask 5) Q2.cnt Q2.T Q2.HS Q2.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < Q2.cnt * (5 + 5), findPtK Q2.cnt Q2.T
    (prodQK 24 5 (mask 5) (5 + 5) Q2.T (bothK 5 Q2.GI Q2I)) Q2Cl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul Q2.cnt 10; omega)
    (by change c < Nat.mul Q2.cnt 10; omega)

theorem enum_ok : enumOK 24 cap m12Q2Gens 384 = true := by
  refine KernelSpor.M12Syl.evEnum_of (enumOK_of base.1 base.2.2.2.2.2.2.2.1 g_tabs g_invs
    base.2.2.2.2.2.2.2.2.2 s_pe s_hs s_cl base.2.2.2.2.2.2.2.2.1) ?_
  rw [List.all_eq_true]
  intro g hgm
  obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list g_tabs hgm
  exact permOK_unpack hc (g_invs j hj).1

theorem T_canon : ∀ i < Q2.cnt, canonK 24 5 (mask 5) (24 * 5) (Q2.T i) = true :=
  fun i hi => penumPt_canon (s_pe i hi)

theorem m12CentKa_ok : m12CentKaOK = true := by
  obtain ⟨xa, xz, xs⟩ := x_tabs
  have c0 := base.2.2.2.2.2.1 0 (by norm_num)
  have c1 := base.2.2.2.2.2.1 1 (by norm_num)
  have c2 := base.2.2.2.2.2.1 2 (by norm_num)
  have hinv : invsOK 24 m12C2B = true := invsOK_of_enumOK (by norm_num) enum_ok
  unfold m12CentKaOK
  rw [enum_ok, hinv, Bool.true_and, Bool.true_and]
  unfold m12C2B
  rw [closArr_eq (cap := cap) base.1 base.2.2.2.2.2.2.2.1 g_tabs base.2.2.2.2.2.2.2.2.2 s_pe s_hs, all_hRec_iff]
  intro i hi
  have hT := T_canon i hi
  have h := allN_spec q2_cent i hi
  unfold centAt at h
  simp only [bIf_true_right, bIf_true_mid] at h
  rw [xa, xz, xs, hid, CFSG.KS.MulH.commTT_unpack hT c0, tblEq_unpack hT hidc,
    tblEq_unpack hT c1, tblEq_unpack hT c2, compT_unpack c2 c1,
    tblEq_unpack hT (CFSG.KC.BfsPin.canonK_pcomp c2 c1)]
  simp only [Bool.or_assoc]
  exact h

end CertificateChecks.KernelGH74.M12Q2

end
