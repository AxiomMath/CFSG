module

public import Certificates.Kernel.HS799102.GlueBasic
public import Certificates.Kernel.HS799102.InvChecks
public import Certificates.Kernel.HS799102.InvSet
public import CFSG.Certificates.Kernel.PCentSetCheck
public import CFSG.RankThree.Native.HSMcLAut
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (pp_of_permB)
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open scoped Pointwise

theorem pp_rG : ∀ k < 6, PP 100 7 (rG k) := fun k hk =>
  pp_of_permB gl_sz (Orb.allN_iff.1 (band ch799102_ibind).2 k hk)

theorem closure_rG : Subgroup.closure (gens 100 7 rG 6) = hs100R := by
  have h := (band ch799102_ibind).1
  unfold rGBind at h
  obtain ⟨h01234, h5⟩ := band h
  obtain ⟨h0123, h4⟩ := band h01234
  obtain ⟨h012, h3⟩ := band h0123
  obtain ⟨h01, h2⟩ := band h012
  obtain ⟨h0, h1⟩ := band h01
  have hE : ∀ j (hj : j < 16) (k : Nat) (hk : k < 6),
      Nat.beq (rG k) (CertificateChecks.KernelHS100.HP.F j) = true →
      toPerm 100 7 (rG k) = permOfArr 100 (hs100Arr j) := fun j hj k hk e => by
    rw [CertificateChecks.KernelHS100.hs100Arr_eq j hj, ← Nat.eq_of_beq_eq_true e,
      permOfArr_unpack (pp_rG k hk)]
  have hA : toPerm 100 7 (rG 0) = hs100A := hE 0 (by norm_num) 0 (by norm_num) h0
  have hB : toPerm 100 7 (rG 1) = hs100B := hE 1 (by norm_num) 1 (by norm_num) h1
  have hU : toPerm 100 7 (rG 2) = hs100U := hE 15 (by norm_num) 2 (by norm_num) h2
  have hI : ∀ k (hk : k < 3), Nat.beq (rG (k + 3))
      (pinvS 100 7 (mask 7) (rG k)) = true → toPerm 100 7 (rG (k + 3)) = (toPerm 100 7 (rG k))⁻¹ :=
    fun k hk e => by rw [Nat.eq_of_beq_eq_true e, toPerm_inv (pp_rG k (by omega))]
  have e0 : rG 0 = CertificateChecks.KernelHS100.HP.F 0 := Nat.eq_of_beq_eq_true h0
  have e1 : rG 1 = CertificateChecks.KernelHS100.HP.F 1 := Nat.eq_of_beq_eq_true h1
  have e2 : rG 2 = CertificateChecks.KernelHS100.HP.F 15 := Nat.eq_of_beq_eq_true h2
  have hA' : toPerm 100 7 (rG 3) = hs100A⁻¹ := by
    rw [hI 0 (by norm_num) (by rw [e0]; exact h3), hA]
  have hB' : toPerm 100 7 (rG 4) = hs100B⁻¹ := by
    rw [hI 1 (by norm_num) (by rw [e1]; exact h4), hB]
  have hU' : toPerm 100 7 (rG 5) = hs100U⁻¹ := by
    rw [hI 2 (by norm_num) (by rw [e2]; exact h5), hU]
  have ha : hs100A ∈ hs100R := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : hs100B ∈ hs100R := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hu : hs100U ∈ hs100R :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    interval_cases k
    · rw [hA]; exact ha
    · rw [hB]; exact hb
    · rw [hU]; exact hu
    · rw [hA']; exact hs100R.inv_mem ha
    · rw [hB']; exact hs100R.inv_mem hb
    · rw [hU']; exact hs100R.inv_mem hu
  · rw [hs100R, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · rw [← hA]; exact gen_mem (by norm_num)
    · rw [← hB]; exact gen_mem (by norm_num)
    · rw [← hU]; exact gen_mem (by norm_num)

theorem words_mem {G : Nat → Nat} {W : List (List Nat)} {m : Nat} (h : wordsK G W m = true) :
    ∀ k < m, PP 100 7 (G k) ∧ toPerm 100 7 (G k) ∈ hs100R := fun k hk => by
  have e := Orb.allN_iff.1 h k hk
  unfold wordsK at e
  obtain ⟨e1, e2⟩ := band e
  have hw := wordK_sound gl_sz pp_rG (W.getD k []) fun c hc => by
    have := allL_iff.1 e2 c hc
    rwa [Nat.blt_eq] at this
  rw [Nat.eq_of_beq_eq_true e1, ← closure_rG]
  exact hw

theorem memP_of_siftB {g : Nat} (hg : PP 100 7 g) (h : siftB g = true) :
    toPerm 100 7 g ∈ hs100P :=
  mem_hs100P_of_sift (rep_toPerm hg) (CertificateChecks.KernelHS100.siftP rfl h)


theorem card_R0_le : Nat.card (hs100R ⊓ MulAction.stabilizer (Equiv.Perm (Fin 100)) (0 : Fin 100) :
    Subgroup (Equiv.Perm (Fin 100))) ≤ 887040 := by
  obtain ⟨hp, hl⟩ := band ch799102_ip0
  obtain ⟨hx, h⟩ := card_stab_le_of_pointOrbK (H := hs100R) pp_rG
    (fun k hk => closure_rG ▸ gen_mem hk) hp
  rw [Nat.eq_of_beq_eq_true hl, card_hs100R] at h
  exact Nat.le_of_mul_le_mul_left (h.trans (by norm_num)) (by norm_num : 0 < 100)

theorem card_N_le : Nat.card (hs100R ⊓ MulAction.stabilizer (Equiv.Perm (Fin 100)) (0 : Fin 100) ⊓
    MulAction.stabilizer (Equiv.Perm (Fin 100)) (ptsM 100 SM) :
    Subgroup (Equiv.Perm (Fin 100))) ≤ 144 := by
  obtain ⟨hw, hf⟩ := band ch799102_ihg
  have hG := words_mem hw
  have h := card_stab_le_of_setOrbK (H := hs100R ⊓ MulAction.stabilizer (Equiv.Perm (Fin 100))
    (0 : Fin 100)) (fun k hk => (hG k hk).1) (fun k hk => Subgroup.mem_inf.2 ⟨(hG k hk).2,
      MulAction.mem_stabilizer_iff.2 (Fin.ext (by
        rw [Equiv.Perm.smul_def, toPerm_apply (hG k hk).1]
        exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hf k hk)))⟩) ch799102_isr
  have hl : SR.length = 6160 := Nat.eq_of_beq_eq_true (band ch799102_inl).2
  rw [hl] at h
  have := card_R0_le
  omega

theorem pp_nG : ∀ k < 3, PP 100 7 (nG k) := fun k hk => (words_mem (band ch799102_ing).1 k hk).1

theorem mem_NL {h : Equiv.Perm (Fin 100)}
    (hh : h ∈ hs100R ⊓ MulAction.stabilizer (Equiv.Perm (Fin 100)) (0 : Fin 100) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 100)) (ptsM 100 SM)) :
    ∃ r ∈ NL, PP 100 7 r.1 ∧ toPerm 100 7 r.1 = h := by
  obtain ⟨hw, hf⟩ := band ch799102_ing
  have hG := words_mem hw
  obtain ⟨hnl12, -⟩ := band ch799102_inl
  obtain ⟨hnl, hlen⟩ := band hnl12
  have hle : Subgroup.closure (gens 100 7 nG 3) ≤
      hs100R ⊓ MulAction.stabilizer (Equiv.Perm (Fin 100)) (0 : Fin 100) ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 100)) (ptsM 100 SM) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨f0, fS⟩ := band (Orb.allN_iff.1 hf k hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨(hG k hk).2,
      MulAction.mem_stabilizer_iff.2 (Fin.ext ?_)⟩, MulAction.mem_stabilizer_iff.2 ?_⟩
    · rw [Equiv.Perm.smul_def, toPerm_apply (hG k hk).1]
      exact Nat.eq_of_beq_eq_true f0
    · rw [← ptsM_imgM (hG k hk).1, Nat.eq_of_beq_eq_true fS]
  have hl : NL.length = 144 := Nat.eq_of_beq_eq_true hlen
  have hge := le_card_of_mulRecK gl_sz pp_nG hnl
  have heq := Subgroup.eq_of_le_of_card_ge hle (card_N_le.trans (hl ▸ hge))
  exact mem_of_mulRecK gl_sz pp_nG hnl (heq ▸ card_N_le.trans hl.ge) h (heq ▸ hh)

theorem comm_of_commI {x y : Nat} (hx : PP 100 7 x) (hy : PP 100 7 y) :
    commI x y = true ↔ toPerm 100 7 x * toPerm 100 7 y = toPerm 100 7 y * toPerm 100 7 x := by
  unfold commI mulI
  rw [Nat.beq_eq, ← toPerm_mul hx hy, ← toPerm_mul hy hx]
  exact ⟨fun e => by rw [e], fun e => toPerm_injective (hx.mul hy) (hy.mul hx) e⟩

theorem toPerm_one : toPerm 100 7 (pidn 100 7) = 1 := toPerm_pidn gl_sz

theorem invol_eq_toPerm {x : Equiv.Perm (Fin 100)} (hxR : x ∈ hs100R) (hx2 : x ^ 2 = 1)
    (h1 : x * toPerm 100 7 (TH.F 0) = toPerm 100 7 (TH.F 0) * x)
    (h2 : x * toPerm 100 7 (TH.F 1) = toPerm 100 7 (TH.F 1) * x) :
    x = 1 ∨ x = toPerm 100 7 (TH.F 2) ∨ x = toPerm 100 7 (TH.F 3) ∨
      x = toPerm 100 7 (TH.F 4) := by
  have p := fun k (hk : k < 9) => pp_TH k hk
  obtain ⟨hiv12, hsm⟩ := band ch799102_iv
  obtain ⟨hiv, hfix⟩ := band hiv12
  unfold ivK at hiv
  obtain ⟨hiv12, hs3⟩ := band hiv
  obtain ⟨hiv1, hs2⟩ := band hiv12
  obtain ⟨hiv0, hs1⟩ := band hiv1
  have hv := fun j (hj : j < 3) => Orb.allN_iff.1 hiv0 j hj
  have ht : ∀ j < 4, PP 100 7 (tV j) ∧ toPerm 100 7 (tV j) ∈ hs100R ∧
      toPerm 100 7 (tV j) * toPerm 100 7 (tV j) = 1 ∧
      toPerm 100 7 (tV j) * toPerm 100 7 (TH.F 0) = toPerm 100 7 (TH.F 0) * toPerm 100 7 (tV j) ∧
      toPerm 100 7 (tV j) * toPerm 100 7 (TH.F 1) =
        toPerm 100 7 (TH.F 1) * toPerm 100 7 (tV j) := by
    have hvj : ∀ j (hj : j < 3), toPerm 100 7 (TH.F (2 + j)) * toPerm 100 7 (TH.F (2 + j)) = 1 ∧
        toPerm 100 7 (TH.F (2 + j)) * toPerm 100 7 (TH.F 0) =
          toPerm 100 7 (TH.F 0) * toPerm 100 7 (TH.F (2 + j)) ∧
        toPerm 100 7 (TH.F (2 + j)) * toPerm 100 7 (TH.F 1) =
          toPerm 100 7 (TH.F 1) * toPerm 100 7 (TH.F (2 + j)) := fun j hj => by
      obtain ⟨e12, e3⟩ := band (hv j hj)
      obtain ⟨e1, e2⟩ := band e12
      refine ⟨?_, (comm_of_commI (p _ (by omega)) (p 0 (by norm_num))).1 e2,
        (comm_of_commI (p _ (by omega)) (p 1 (by norm_num))).1 e3⟩
      have e1' : mulI (TH.F (2 + j)) (TH.F (2 + j)) = pidn 100 7 := Nat.eq_of_beq_eq_true e1
      rw [← toPerm_mul (p _ (by omega)) (p _ (by omega))]
      change toPerm 100 7 (mulI (TH.F (2 + j)) (TH.F (2 + j))) = 1
      rw [e1', toPerm_one]
    have hu5 : toPerm 100 7 (rG 5) ∈ hs100R := closure_rG ▸ gen_mem (by norm_num)
    have hmemv : ∀ k (hk : k < 2), siftB (mulI (TH.F (2 + k)) (rG 5)) = true →
        toPerm 100 7 (TH.F (2 + k)) ∈ hs100R := fun k hk e => by
      have hm := hs100P_le_R (memP_of_siftB ((p _ (by omega)).mul (pp_rG 5 (by norm_num))) e)
      rw [toPerm_mul (p _ (by omega)) (pp_rG 5 (by norm_num))] at hm
      have := hs100R.mul_mem hm (hs100R.inv_mem hu5)
      rwa [mul_inv_cancel_right] at this
    intro j hj
    have t0 : tV 0 = pidn 100 7 := rfl
    have t1 : tV 1 = TH.F 2 := rfl
    have t2 : tV 2 = TH.F 3 := rfl
    have t3 : tV 3 = TH.F 4 := rfl
    interval_cases j
    · rw [t0, toPerm_one]
      exact ⟨PP.id gl_sz, hs100R.one_mem, mul_one 1, by rw [one_mul, mul_one],
        by rw [one_mul, mul_one]⟩
    · rw [t1]
      exact ⟨p 2 (by norm_num), hmemv 0 (by norm_num) hs1, hvj 0 (by norm_num)⟩
    · rw [t2]
      exact ⟨p 3 (by norm_num), hmemv 1 (by norm_num) hs2, hvj 1 (by norm_num)⟩
    · rw [t3]
      exact ⟨p 4 (by norm_num), hs100P_le_R (memP_of_siftB (p 4 (by norm_num)) hs3),
        hvj 2 (by norm_num)⟩
  unfold fixK at hfix
  obtain ⟨hf01, hfa⟩ := band hfix
  obtain ⟨hf0, hf1⟩ := band hf01
  have fix0 : ∀ k (hk : k < 2), Nat.beq (pg 7 (mask 7) (TH.F k) 0) 0 = true →
      toPerm 100 7 (TH.F k) 0 = 0 := fun k hk e => Fin.ext (by
    rw [toPerm_apply (p k (by omega))]
    exact Nat.eq_of_beq_eq_true e)
  have hfx : ∀ k (hk : k < 2), toPerm 100 7 (TH.F k) 0 = 0 →
      x * toPerm 100 7 (TH.F k) = toPerm 100 7 (TH.F k) * x →
      pg 7 (mask 7) (TH.F k) (x 0 : Nat) = (x 0 : Nat) := fun k hk e hc => by
    rw [← toPerm_apply (p k (by omega))]
    have := congrArg (fun g : Equiv.Perm (Fin 100) => (g 0 : Nat)) hc
    simp only [Equiv.Perm.mul_apply, e] at this
    exact this.symm
  have hy := Orb.allN_iff.1 hfa (x 0 : Nat) (x 0).2
  rw [hfx 0 (by norm_num) (fix0 0 (by norm_num) hf0) h1,
    hfx 1 (by norm_num) (fix0 1 (by norm_num) hf1) h2] at hy
  simp only [Nat.beq_refl, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Nat.beq_eq] at hy
  have hj : ∃ j < 4, x 0 = toPerm 100 7 (tV j) 0 := by
    have ev : ∀ j (hj : j < 4), (toPerm 100 7 (tV j) 0 : Nat) = pg 7 (mask 7) (tV j) 0 :=
      fun j hj => toPerm_apply (ht j hj).1 0
    rcases hy with ((h0 | h0) | h0) | h0
    · refine ⟨0, by norm_num, Fin.ext ?_⟩
      have e : toPerm 100 7 (tV 0) = 1 := toPerm_one
      rw [e, h0]
      rfl
    · exact ⟨1, by norm_num, Fin.ext (by rw [ev 1 (by norm_num), h0]; rfl)⟩
    · exact ⟨2, by norm_num, Fin.ext (by rw [ev 2 (by norm_num), h0]; rfl)⟩
    · exact ⟨3, by norm_num, Fin.ext (by rw [ev 3 (by norm_num), h0]; rfl)⟩
  obtain ⟨j, hj4, hxj⟩ := hj
  obtain ⟨htp, htR, htt, htc1, htc2⟩ := ht j hj4
  set t := toPerm 100 7 (tV j)
  set c1 := toPerm 100 7 (TH.F 0)
  set c2 := toPerm 100 7 (TH.F 1)
  have hc1 : t * x * c1 = c1 * (t * x) := by rw [mul_assoc, h1, ← mul_assoc, htc1, mul_assoc]
  have hc2 : t * x * c2 = c2 * (t * x) := by rw [mul_assoc, h2, ← mul_assoc, htc2, mul_assoc]
  have hS : ∀ i : Fin 100, i ∈ ptsM 100 SM ↔ c1 i = i := fun i => by
    have e := Orb.allN_iff.1 hsm i i.2
    simp only [ptsM, Set.mem_setOf_eq]
    have e' : Nat.testBit SM i = Nat.beq (pg 7 (mask 7) (TH.F 0) i) i := by
      generalize Nat.testBit SM i = a at e
      generalize Nat.beq (pg 7 (mask 7) (TH.F 0) i) i = b at e
      cases a <;> cases b <;> first | rfl | exact absurd e (by decide)
    rw [e', Nat.beq_eq, ← toPerm_apply (p 0 (by norm_num))]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hmem : t * x ∈ hs100R ⊓ MulAction.stabilizer (Equiv.Perm (Fin 100)) (0 : Fin 100) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 100)) (ptsM 100 SM) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hs100R.mul_mem htR hxR,
      MulAction.mem_stabilizer_iff.2 ?_⟩, MulAction.mem_stabilizer_iff.2 ?_⟩
    · rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, hxj, ← Equiv.Perm.mul_apply, htt]
      rfl
    · ext i
      rw [Set.mem_smul_set_iff_inv_smul_mem, hS, hS, Equiv.Perm.smul_def]
      have e : (t * x)⁻¹ * c1 = c1 * (t * x)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc1, mul_inv_cancel_right]
      constructor
      · intro h
        have := congrArg (t * x) h
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, mul_assoc, ← e, ← mul_assoc,
          mul_inv_cancel, one_mul, ← Equiv.Perm.mul_apply, mul_inv_cancel] at this
        exact this
      · intro h
        rw [← Equiv.Perm.mul_apply, ← e, Equiv.Perm.mul_apply, h]
  obtain ⟨r, hr, hrp, hre⟩ := mem_NL hmem
  have hsc := allL_iff.1 ch799102_iscan r.1 (List.mem_map_of_mem hr)
  rw [(comm_of_commI hrp (p 0 (by norm_num))).2 (by rw [hre]; exact hc1),
    (comm_of_commI hrp (p 1 (by norm_num))).2 (by rw [hre]; exact hc2)] at hsc
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hsc
  have hiv := Orb.allN_iff.1 hsc j hj4
  have hyp : PP 100 7 (mulI (tV j) r.1) := htp.mul hrp
  have hyx : toPerm 100 7 (mulI (tV j) r.1) = x := by
    change toPerm 100 7 (pcomp 100 7 (mask 7) (tV j) r.1) = x
    rw [toPerm_mul htp hrp, hre, ← mul_assoc, htt, one_mul]
  unfold invT at hiv
  have hsq : Nat.beq (mulI (mulI (tV j) r.1) (mulI (tV j) r.1)) (pidn 100 7) = true := by
    rw [Nat.beq_eq]
    refine toPerm_injective (hyp.mul hyp) (PP.id gl_sz) ?_
    change toPerm 100 7 (pcomp 100 7 (mask 7) _ _) = _
    rw [toPerm_mul hyp hyp, hyx, toPerm_one, ← sq, hx2]
  rw [hsq, Bool.not_true, Bool.false_or] at hiv
  unfold isV at hiv
  simp only [Bool.or_eq_true, Nat.beq_eq] at hiv
  rw [← hyx]
  rcases hiv with ((e | e) | e) | e
  · left
    rw [e, toPerm_one]
  · exact Or.inr (Or.inl (by rw [e]))
  · exact Or.inr (Or.inr (Or.inl (by rw [e])))
  · exact Or.inr (Or.inr (Or.inr (by rw [e])))

theorem invol_eq {x : Equiv.Perm (Fin 100)} (hxR : x ∈ hs100R) (hx2 : x ^ 2 = 1)
    (h1 : x * permOfArr 100 hsThC1 = permOfArr 100 hsThC1 * x)
    (h2 : x * permOfArr 100 hsThC2 = permOfArr 100 hsThC2 * x) :
    x = 1 ∨ x = permOfArr 100 hsThV1 ∨ x = permOfArr 100 hsThV2 ∨ x = permOfArr 100 hsThV3 := by
  have e := fun k (hk : k < 9) => toPerm_v k hk
  have h := invol_eq_toPerm hxR hx2 (by rw [e 0 (by norm_num)]; exact h1)
    (by rw [e 1 (by norm_num)]; exact h2)
  rwa [e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num)] at h

end CertificateChecks.KernelHS799102

end
