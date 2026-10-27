module

public import Certificates.Kernel.HSStd.U43I4Slices
public import Certificates.Kernel.HSStd.U43I4Grp
public import Certificates.Kernel.CU43Aut.CentGlue
public import Certificates.Kernel.CU43Aut.ModelFacts
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43I4

open Subgroup CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CFSG.KC.U43Case CFSG.KC.U43Wit CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelCU43Aut CertificateChecks.KernelCU43Aut.CentG CertificateChecks.KernelU43B

theorem hpid : PR (pidn 820 10) 1 := Raw.Orb.prep_pidn (by norm_num) (by norm_num)

theorem cK_pid : cK (pidn 820 10) = true := by decide +kernel

theorem perm_of_inv {g g' : Nat} (h : invEqK 820 10 (mask 10) (820 * 10) g g' = true) :
    ∃ G : Equiv.Perm (Fin 820), PR g G ∧ PR g' G⁻¹ :=
  ⟨permOfArr 820 (unpack 820 10 g), Raw.Orb.prep_of_rep (rep_permOfArr (invEqK_sound h).2).1,
    Raw.Orb.prep_of_rep (rep_permOfArr (invEqK_sound h).2).2⟩

theorem pk_eq {p q : Nat} {g : Equiv.Perm (Fin 820)} (hp : PR p g) (hq : PR q g)
    (cp : cK p = true) (cq : cK q = true) : p = q :=
  CFSG.KS.PF.eq_of_fields (by norm_num) (CFSG.KS.PF.canon_facts cp).2.2.1
    (CFSG.KS.PF.canon_facts cq).2.2.1 fun i hi => by rw [hp ⟨i, hi⟩, hq ⟨i, hi⟩]

theorem cmK_spec {a b : Nat} {A B : Equiv.Perm (Fin 820)} (hA : PR a A) (hB : PR b B)
    (h : cmK a b = true) : A * B = B * A :=
  pr_eq (pr_pc hA hB) (pr_pc hB hA) (Nat.eq_of_beq_eq_true h)

theorem pr_ppw {p : Nat} {g : Equiv.Perm (Fin 820)} (hp : PR p g) (e : Nat) :
    PR (ppw 820 10 p e) (g ^ e) :=
  prep_ppw (by norm_num) (by norm_num) hp e

theorem ord3_spec {x : Nat} {X : Equiv.Perm (Fin 820)} (hx : PR x X) (cx : cK x = true)
    (h : ord3P 820 10 x = true) : X ^ 3 = 1 ∧ X ≠ 1 := by
  unfold ord3P at h
  simp only [CFSG.KLie.CT.andB, CFSG.KLie.CT.notB] at h
  cases h3 : Nat.beq (ppw 820 10 x 3) (pidn 820 10) <;>
    cases h1 : Nat.beq (ppw 820 10 x 1) (pidn 820 10) <;> rw [h3, h1] at h <;>
    try exact absurd h (by decide)
  refine ⟨pr_eq (pr_ppw hx 3) hpid (Nat.eq_of_beq_eq_true h3), fun hX1 => ?_⟩
  have e1 : PR (ppw 820 10 x 1) 1 := by
    have := pr_ppw hx 1
    rwa [pow_one, hX1] at this
  have hx1 : PR x 1 := by rw [← hX1]; exact hx
  have := pk_eq hx1 hpid cx (by decide)
  have e2 : ppw 820 10 x 1 = pidn 820 10 := by rw [this]; rfl
  rw [e2] at h1
  exact absurd h1 (by rw [Nat.beq_refl]; decide)

section Model

theorem el_spec {g g' k : Nat} (h : elOK g g' k = true) :
    ∃ G : Equiv.Perm (Fin 820), PR g G ∧ PR g' G⁻¹ ∧ G ∈ R := by
  unfold elOK inRK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, hinv, hk8, hP⟩ := h
  obtain ⟨G, hG, hG'⟩ := perm_of_inv hinv
  have hk : k < 8 := Nat.blt_eq.mp hk8
  have e : I4TD k = TKI k := Nat.eq_of_beq_eq_true (allN_spec kTD k hk)
  rw [e] at hP
  have hrep : Rep 820 (unpack 820 10 (pc g (TKI k))) (G * (tP k)⁻¹) :=
    rep_pc (Raw.Orb.rep_unpack hG) (rep_TKI hk)
  exact ⟨G, hG, hG', mem_R_iff.2 ⟨G * (tP k)⁻¹, mem_of_inPK hrep hP, k, hk, by group⟩⟩

theorem el_cK {g g' k : Nat} (h : elOK g g' k = true) : cK g = true := by
  unfold elOK at h
  exact ((bAnd_iff _ _).1 h).1

theorem u5_facts : ∃ u ∈ R, rP 5 = u * rP 4 * u⁻¹ := by
  have h := kU5
  rw [bAnd_iff] at h
  obtain ⟨u, hu, -, huR⟩ := el_spec h.1
  have e := pr_eq (pr_pc hu (pr_rP (j := 4) (by norm_num))) (pr_pc (pr_rP (j := 5) (by norm_num)) hu)
    (Nat.eq_of_beq_eq_true h.2)
  exact ⟨u, huR, by rw [e]; group⟩

theorem tree_facts {y₀ : Equiv.Perm (Fin 820)} (hy : PR (I4G 1) y₀) : ∀ i, i < 648 →
    cK (I4Y i) = true ∧ ∃ g, PR (I4Y i) g ∧ g ∈ R ⊓ centralizer ({y₀} : Set (Equiv.Perm (Fin 820))) := by
  have hG : ∀ l < 4, cK (I4YG l) = true ∧ ∃ g, PR (I4YG l) g ∧
      g ∈ R ⊓ centralizer ({y₀} : Set (Equiv.Perm (Fin 820))) := by
    intro l hl
    have h := allN_spec kYG l hl
    rw [bAnd_iff] at h
    obtain ⟨g, hg, -, hgR⟩ := el_spec h.1
    exact ⟨el_cK h.1, g, hg, mem_inf.2 ⟨hgR, mem_centralizer_singleton_iff.2 (cmK_spec hg hy h.2)⟩⟩
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      rw [Nat.eq_of_beq_eq_true kY0e]
      exact ⟨cK_pid, 1, hpid, one_mem _⟩
    · obtain ⟨hp, hl, he⟩ := tree_all i (Nat.pos_of_ne_zero h0) hi
      obtain ⟨cp, g, hg, hgD⟩ := ih (I4YP i) hp (by omega)
      obtain ⟨cl, g', hg', hg'D⟩ := hG (I4YL i) hl
      rw [he]
      exact ⟨canonK_pcomp cl cp, g' * g, pr_pc hg' hg, mul_mem hg'D hgD⟩

theorem i4_false {y c k : Equiv.Perm (Fin 820)}
    (hs : SigRel (rP 4) y c k) (hy : y ∈ R) (hc : c ∈ R) (hk : k ∈ R) : False := by
  have hT := pr_rP (j := 4) (by norm_num)
  obtain ⟨u, hu, h5⟩ := u5_facts
  have hY0 := kY0
  simp only [bAnd_iff] at hY0
  obtain ⟨y₀, hy₀, -, -⟩ := el_spec hY0.1
  have hy₀1 := (ord3_spec hy₀ (el_cK hY0.1) hY0.2.1).2
  have hex : ∀ l, ∃ g : Equiv.Perm (Fin 820), l < 5 →
      PR (I4H l) g ∧ g ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))) := by
    intro l
    by_cases hl : l < 5
    · have h := allN_spec kH l hl
      rw [bAnd_iff] at h
      obtain ⟨g, hg, -, hgR⟩ := el_spec h.1
      exact ⟨g, fun _ => ⟨hg, mem_inf.2 ⟨hgR, mem_centralizer_singleton_iff.2 (cmK_spec hg hT h.2)⟩⟩⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose hgen hhgen using hex
  have hTw := kTw
  rw [bAnd_iff] at hTw
  have hlow := towerProdK_sound (h := hgen) (fun l hl => (hhgen l hl).1) hTw.1
  rw [Nat.eq_of_beq_eq_true hTw.2] at hlow
  have hcl : closure (hgen '' {l | l < 5}) ≤ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact (hhgen l hl).2
  have hC := hlow.trans (Subgroup.card_le_of_le hcl)
  have hS := kS
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at hS
  obtain ⟨hA, h12, -, -⟩ := hS
  have hA2 := allN_spec hA 0 (by norm_num)
  have hA3 := allN_spec hA 1 (by norm_num)
  simp only [bAnd_iff] at hA2 hA3
  have e2 : elOK (I4G 2) (I4GI 2) (I4GK 2) = true := hA2.1
  have e3 : elOK (I4G 3) (I4GI 3) (I4GK 3) = true := hA3.1
  obtain ⟨s₁, hs₁, -, hs₁R⟩ := el_spec e2
  obtain ⟨s₂, hs₂, -, hs₂R⟩ := el_spec e3
  have o2 : ord3P 820 10 (I4G 2) = true := hA2.2.1
  have o3 : ord3P 820 10 (I4G 3) = true := hA3.2.1
  have m2 : cmK (I4G 2) (CU43T 6) = true := hA2.2.2
  have m3 : cmK (I4G 3) (CU43T 6) = true := hA3.2.2
  have hs₁C : s₁ ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))) :=
    mem_inf.2 ⟨hs₁R, mem_centralizer_singleton_iff.2 (cmK_spec hs₁ hT m2)⟩
  have hs₂C : s₂ ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))) :=
    mem_inf.2 ⟨hs₂R, mem_centralizer_singleton_iff.2 (cmK_spec hs₂ hT m3)⟩
  have hh : ∀ a < 3, ∀ b < 3, a ≠ 0 ∨ b ≠ 0 → ∃ h ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))),
      h * y₀ * h⁻¹ = s₁ ^ a * s₂ ^ b := by
    intro a ha b hb hab
    have hq : a + 3 * b - 1 < 8 := by omega
    have h := allN_spec kQ (a + 3 * b - 1) hq
    simp only [bAnd_iff] at h
    obtain ⟨hel, hcm, heq⟩ := h
    obtain ⟨g, hg, -, hgR⟩ := el_spec hel
    have hsq : PR (sQ (a + 3 * b - 1)) (s₁ ^ ((a + 3 * b - 1 + 1) % 3) * s₂ ^ ((a + 3 * b - 1 + 1) / 3)) := by
      unfold sQ
      exact pr_pc (pr_ppw hs₁ _) (pr_ppw hs₂ _)
    rw [show (a + 3 * b - 1 + 1) % 3 = a by omega, show (a + 3 * b - 1 + 1) / 3 = b by omega] at hsq
    have e := pr_eq (pr_pc hg hy₀) (pr_pc hsq hg) (Nat.eq_of_beq_eq_true heq)
    refine ⟨g, mem_inf.2 ⟨hgR, mem_centralizer_singleton_iff.2 (cmK_spec hg hT hcm)⟩, ?_⟩
    rw [e]
    group
  have hUb := kUb
  simp only [bAnd_iff] at hUb
  obtain ⟨-, -, inv4, inP4, -, -, inv5, heq5, hub⟩ := hUb
  obtain ⟨h₀, hh₀, -⟩ := perm_of_inv inv4
  obtain ⟨r₀, hr₀, -⟩ := perm_of_inv inv5
  have hh₀P : h₀ ∈ P := mem_of_inPK (Raw.Orb.rep_unpack hh₀) inP4
  have er : r₀ = h₀ * y₀ * h₀⁻¹ := by
    have e := pr_eq (pr_pc hr₀ hh₀) (pr_pc hh₀ hy₀) (Nat.eq_of_beq_eq_true heq5)
    calc r₀ = r₀ * h₀ * h₀⁻¹ := by group
      _ = h₀ * y₀ * h₀⁻¹ := by rw [e]
  unfold ubOK at hub
  have hu1 : ubOkK 820 10 (mask 10) C.S C.SI 7 C.BP 3 (I4G 5) I4O = true := by
    revert hub
    cases ubOkK 820 10 (mask 10) C.S C.SI 7 C.BP 3 (I4G 5) I4O <;> simp
  have hu2 : Nat.beq (ubProdK 820 10 (mask 10) (820 * 10) C.LR C.TRI 3 (I4G 5) I4O) 81 = true := by
    revert hub
    cases ubOkK 820 10 (mask 10) C.S C.SI 7 C.BP 3 (I4G 5) I4O <;>
      cases Nat.beq (ubProdK 820 10 (mask 10) (820 * 10) C.LR C.TRI 3 (I4G 5) I4O) 81 <;> simp
  have hup := ubProdK_sound (NS := 13) (CH := 64) KernelU43B.binds C.head C.hl (by norm_num) C.hs
    P_eq_Gen hr₀ hu1
  rw [Nat.eq_of_beq_eq_true hu2, er] at hup
  have hex2 : ∀ i, ∃ g : Equiv.Perm (Fin 820), i < 648 → cK (I4Y i) = true ∧ PR (I4Y i) g ∧
      g ∈ R ⊓ centralizer ({y₀} : Set (Equiv.Perm (Fin 820))) := by
    intro i
    by_cases hi : i < 648
    · obtain ⟨hc', g, hg, hgD⟩ := tree_facts hy₀ i hi
      exact ⟨g, fun _ => ⟨hc', hg, hgD⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose Yp hYp using hex2
  have hYinj : ∀ i < 648, ∀ j < 648, Yp i = Yp j → i = j := by
    intro i hi j hj e
    have hj' := (hYp j hj).2.1
    rw [← e] at hj'
    exact sortK_inj kSort i hi j hj (pk_eq (hYp i hi).2.1 hj' (hYp i hi).1 (hYp j hj).1)
  have hsol : ∀ i < 648, ∀ j < 648, ¬ SigRel (rP 4) y₀ (Yp i) (Yp j) := by
    intro i hi j hj hs'
    have hy3 : y₀ ^ 3 = 1 := by rw [← hs'.y3]; exact pow_orderOf_eq_one y₀
    have hc3 : Yp i ^ 3 = 1 := by rw [← hs'.c3]; exact pow_orderOf_eq_one (Yp i)
    have hcp3 : (rP 4 * Yp i * (rP 4)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hc3, mul_one, mul_inv_cancel]
    exact cFailK_sound (by norm_num) (by norm_num) hT (rP_mul_self (j := 4) (by norm_num)) hy₀
      (hYp i hi).2.1 (fun j hj => (hYp j hj).2.1) (ns_all i hi) hs'.c3 hs'.ccp hs'.ycp
      (relFree_of_card_27 hy3 hc3 hcp3 hs'.yc hs'.ycp hs'.ccp hs'.card27) hj hs'.kk hs'.k1
      hs'.kcp hs'.kkp hs'.kc
  exact false_of_facts hu h5 hC hs₁C hs₂C (ord3_spec hs₁ (el_cK e2) o2).1
    (ord3_spec hs₂ (el_cK e3) o3).1 (cmK_spec hs₁ hs₂ h12) hy₀1 hh hh₀P hup
    (fun i hi => (hYp i hi).2.2) hYinj hsol hs hy hc hk

end Model

end CertificateChecks.KernelHSStd.U43I4

end
