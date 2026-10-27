module

public import Certificates.Kernel.Misc.KGroups.M11Checks
public import Certificates.Kernel.Misc.KGroups.M11Valid
public import CFSG.Certificates.Kernel.Misc.KGrpProof

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M11K

open Equiv CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT.P
open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem hA : ∀ a < [m11gA, m11gB].length, AG a = pcode ([m11gA, m11gB].getD a 1) := by
  decide +kernel

theorem hX : pcode m11x0 = X0 := by decide +kernel

theorem hGA : pcode m11gA = AG 0 := (hA 0 (by norm_num)).symm

theorem hGB : pcode m11gB = AG 1 := (hA 1 (by norm_num)).symm

theorem hn : 11 ≤ 32 := by norm_num

theorem G_eq : NativeSporadic.M11 = Subgroup.closure {g | g ∈ [m11gA, m11gB]} := by
  rw [m11_eq]
  congr 1
  ext g
  simp

theorem treeAll : ∀ k < 7920, treeAt (mul 11) (one 11) AG 2 E PA k = true :=
  forall_of_chunks 1980 4 _ fun c hc => by
    interval_cases c
    · exact tree0
    · exact tree1
    · exact tree2
    · exact tree3

theorem closedAll : ∀ k < 7920, closedAt (mul 11) AG 2 7920 E CT k = true :=
  forall_of_chunks 1980 4 _ fun c hc => by
    interval_cases c
    · exact closed0
    · exact closed1
    · exact closed2
    · exact closed3

theorem listM : ExactList pcode NativeSporadic.M11 7920 E := by
  have clos := clos_card_proved (pcode_enc_proved hn) [m11gA, m11gB] hA (by norm_num) treeAll
    ((allN_iff _ _).1 sortB)
  rw [G_eq]
  exact ⟨clos.1, (clos.2.2 closedAll).2, sort_distinct_proved ((allN_iff _ _).1 sortB)⟩

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

theorem ordsF : orderOf m11gA = 2 ∧ orderOf m11gB = 4 ∧ PairInv ws m11gA m11gB := by
  obtain ⟨h1, h2⟩ := andB_iff.1 ordAB
  obtain ⟨h2, h3⟩ := andB_iff.1 h2
  rw [← hGA] at h1 h3
  rw [← hGB] at h2 h3
  exact ⟨(ordK_iff_proved hn _ (by norm_num)).1 h1, (ordK_iff_proved hn _ (by norm_num)).1 h2,
    (pairK_iff_proved hn _ _ ws ws_pos).1 h3⟩

theorem x0F : m11x0 ∈ NativeSporadic.M11 ∧ orderOf m11x0 = 3 := by
  obtain ⟨h4, h5⟩ := andB_iff.1 x0B
  rw [← hX] at h5
  exact ⟨exact_mem_proved hn listM (by unfold ix0; norm_num)
    (hX.trans (Nat.eq_of_beq_eq_true h4).symm), (ordK_iff_proved hn _ (by norm_num)).1 h5⟩

theorem c2F : Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 2} = 165 :=
  (cnt_ord_proved hn listM (by norm_num)).symm.trans (Nat.eq_of_beq_eq_true c2B)

theorem cAF : centCard NativeSporadic.M11 m11gA = 48 :=
  (cnt_cent_proved hn listM hGA).symm.trans (Nat.eq_of_beq_eq_true cAB)

theorem cFF : Nat.card {y // y ∈ NativeSporadic.M11 ∧ orderOf y = 4 ∧ PairInv ws m11gA y} = 48 :=
  (fib_card_proved hn listM hGA (by norm_num) ws_pos).symm.trans (Nat.eq_of_beq_eq_true cFB)

theorem c3F : Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 3} = 440 :=
  (cnt_ord_proved hn listM (by norm_num)).symm.trans (Nat.eq_of_beq_eq_true c3B)

theorem cXF : centCard NativeSporadic.M11 m11x0 = 18 :=
  (cnt_cent_proved hn listM hX).symm.trans (Nat.eq_of_beq_eq_true cXB)

open Certificates in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M11 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem facts : (Q.check = true ∧ Q.orderCertificate = 7920)
    ∧ (orderOf m11gA = 2 ∧ orderOf m11gB = 4 ∧ PairInv ws m11gA m11gB)
    ∧ (m11x0 ∈ NativeSporadic.M11 ∧ orderOf m11x0 = 3)
    ∧ Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 2} = 165
    ∧ centCard NativeSporadic.M11 m11gA = 48
    ∧ Nat.card {y // y ∈ NativeSporadic.M11 ∧ orderOf y = 4 ∧ PairInv ws m11gA y} = 48
    ∧ (∀ σ ∈ NativeSporadic.M11, σ * m11gA = m11gA * σ → σ * m11gB = m11gB * σ → σ = 1)
    ∧ Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 3} = 440
    ∧ centCard NativeSporadic.M11 m11x0 = 18
    ∧ E9At NativeSporadic.M11 m11gA
    ∧ Cent3At NativeSporadic.M11 m11x0 :=
  ⟨⟨M11C.valid, M11C.order⟩, ordsF, x0F, c2F, cAF, cFF,
    cent_sound_proved hn listM hGA hGB ((allN_iff _ _).1 centB), c3F, cXF,
    e9_sound_proved hn listM hGA ((allN_iff _ _).1 inAB) e9B,
    cent3_sound_proved hn listM hX ((allN_iff _ _).1 inXB) cent3B⟩

end CertificateChecks.KernelMisc.M11K

end
