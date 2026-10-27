module

public import Certificates.Kernel.McL.Words
public import Certificates.Kernel.McL.Facts
import CFSG.Certificates.Kernel.McLLabSound
import CFSG.Certificates.Kernel.McLModelSound
import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelMcL

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.Certificates CFSG.Certificates.LCE
  CFSG.Certificates.McLS CFSG.Certificates.McLD TauCeti
open CertificateChecks.KernelHe CertificateChecks.KernelRu

noncomputable abbrev gP : ℕ → Sporadic.mclPresentation.Group := KB.tcGen Sporadic.mclPresentation

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem mlab_append (FB WT SL : Nat → Nat) (INV rw d lw lm nC L : Nat) :
    ∀ (l1 l2 : List Nat) (x : Nat),
    McL.Lab.runFacts FB WT SL INV rw d lw lm nC L (List.append l1 l2) x =
      McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l2
        (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (McL.Lab.runChunk FB WT SL INV rw d lw lm nC L C x)
        (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L (List.append l1 l2)) =
      McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l2
        (strictN (McL.Lab.runChunk FB WT SL INV rw d lw lm nC L C x)
          (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l1))
    rw [strictN_eq', strictN_eq']
    exact mlab_append FB WT SL INV rw d lw lm nC L l1 l2 _

theorem mlab_join {FB WT SL : Nat → Nat} {INV rw d lw lm nC L : Nat} {l1 l2 : List Nat}
    {x y z : Nat} (h1 : Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l1 x) y = true)
    (h2 : Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l2 y) z = true) :
    Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [mlab_append, h1, h2]

theorem nr1_eq {r : ℕ} (hr : r < 78) : McL.Rels.NR1 r = McL.Rels.QR r := by
  have h : Nat.blt r 78 = true := by rw [Nat.blt_eq]; exact hr
  unfold McL.Rels.NR1
  rw [h]

theorem nr1_78 : McL.Rels.NR1 78 = McL.Rels.K1W := rfl

theorem nr1_letters : ∀ r < 79, ∀ i < LceS.wLen (McL.Rels.NR1 r),
    wLet (LceS.wWord (McL.Rels.NR1 r)) i < 6 :=
  entsBelow_sound let_NR1

theorem qr_letters {r : ℕ} (hr : r < 78) : ∀ i < LceS.wLen (McL.Rels.QR r),
    wLet (LceS.wWord (McL.Rels.QR r)) i < 6 := by
  rw [← nr1_eq hr]
  exact nr1_letters r (by omega)

theorem a_sq : gP 0 * gP 0 = 1 := by
  have h := (tc_ok 0 (by norm_num)).2
  rw [bval_eq_list _ _ _ [0, 0] (by decide)] at h
  simpa [letV] using h

theorem cq_bound : ∀ (H : Type) [Group H] (z : ℕ → H),
    (∀ r < 78, bval z (LceS.wWord (McL.Rels.QR r)) (LceS.wLen (McL.Rels.QR r)) = 1) →
      Nat.card (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
        Nat.card (Subgroup.closure (z '' {i | i < 3})) ≤ 161280 := by
  intro H _ z hz
  have hQ := lceOk_sound CQ.ok z (fun r hr => hz r hr)
  have hsub : (fun j => bval z (LceS.wWord (McL.Rels.STQ j)) (LceS.wLen (McL.Rels.STQ j))) ''
      {j | j < 65536} = {z 0 * z 1} := by
    have e : (fun j => bval z (LceS.wWord (McL.Rels.STQ j)) (LceS.wLen (McL.Rels.STQ j))) =
        fun _ => z 0 * z 1 := by
      funext j
      have hs : McL.Rels.STQ j = McL.Rels.SQ := rfl
      rw [hs, bval_eq_list z _ _ [0, 2] (by decide)]
      simp [letV]
    rw [e]
    exact Set.Nonempty.image_const ⟨0, by norm_num⟩ _
  have h6 : {g : ℕ | 2 * g < 6} = {i | i < 3} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    omega
  have hQ' : (Subgroup.closure ({z 0 * z 1} : Set H)).relIndex
      (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
      (Subgroup.closure ({z 0 * z 1} : Set H)).relIndex
      (Subgroup.closure (z '' {i | i < 3})) ≤ CFSG.KD.McL.CQ.nAlive := by
    rw [← hsub, ← h6]
    exact hQ
  have h5 : (z 0 * z 1) ^ 5 = 1 := by
    have h := hz 3 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KD.McL.Bind.p5,
      bval_eq_list z _ _ [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] (by decide)] at h
    simpa [letV, pow_succ, mul_assoc] using h
  have hc : Nat.card (Subgroup.closure ({z 0 * z 1} : Set H)) ≠ 0 ∧
      Nat.card (Subgroup.closure ({z 0 * z 1} : Set H)) ≤ 5 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    have hd : orderOf (z 0 * z 1) ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    exact ⟨(Nat.pos_of_dvd_of_pos hd (by norm_num)).ne', Nat.le_of_dvd (by norm_num) hd⟩
  have c := card_le_step' hQ' hc
  have e5 : CFSG.KD.McL.CQ.nAlive * 5 = 161280 := by
    rw [Nat.mul_comm]
    exact Nat.eq_of_beq_eq_true CFSG.KD.McL.Bind.cQ
  rw [e5] at c
  exact c

theorem qrel : ∀ r < 78, bval (yv gP) (LceS.wWord (McL.Rels.QR r)) (LceS.wLen (McL.Rels.QR r)) =
    1 := by
  have hF := smallTab_of small_XT
  have hRT : ∀ r < 15, LceS.wWord (McL.TC.sel r) < 2 ^ (8 * LceS.wLen (McL.TC.sel r)) ∧
      bval gP (LceS.wWord (McL.TC.sel r)) (LceS.wLen (McL.TC.sel r)) = 1 := fun r hr => tc_ok r hr
  have hA1 := McLLab.targets_sound gP hRT (wtPer0_sound per_A1) CFSG.KD.McL.A1.wd
    CFSG.KD.McL.A1.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.A1.one)
    (by decide) CFSG.KD.McL.A1.anc (by decide) rfl CFSG.KD.McL.A1.f0 rfl (by decide)
    CFSG.KD.McL.A1.tg rfl rfl rfl
  have hA2 := McLLab.targets_sound gP hRT (wtPer0_sound per_A2) CFSG.KD.McL.A2.wd
    CFSG.KD.McL.A2.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.A2.one)
    (by decide) CFSG.KD.McL.A2.anc (by decide) rfl CFSG.KD.McL.A2.f0 rfl (by decide)
    CFSG.KD.McL.A2.tg rfl rfl rfl
  have hA3 := McLLab.targets_sound gP hRT (wtPer0_sound per_A3) CFSG.KD.McL.A3.wd
    CFSG.KD.McL.A3.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.A3.one)
    (by decide) CFSG.KD.McL.A3.anc (by decide) rfl CFSG.KD.McL.A3.f0 rfl (by decide)
    CFSG.KD.McL.A3.tg rfl rfl rfl
  have hA4 := McLLab.targets_sound gP hRT (wtPer0_sound per_A4) CFSG.KD.McL.A4.wd
    CFSG.KD.McL.A4.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.A4.one)
    (by decide) CFSG.KD.McL.A4.anc (by decide) rfl CFSG.KD.McL.A4.f0 rfl (by decide)
    CFSG.KD.McL.A4.tg rfl rfl rfl
  have hA5 := McLLab.targets_sound gP hRT (wtPer0_sound per_A5) CFSG.KD.McL.A5.wd
    CFSG.KD.McL.A5.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.A5.one)
    (by decide) CFSG.KD.McL.A5.anc (by decide) rfl CFSG.KD.McL.A5.f0 rfl (by decide)
    CFSG.KD.McL.A5.tg rfl rfl rfl
  have hb1 := bindRun_sound gP hF CFSG.KD.McL.Bind.qA1
  have hb2 := bindRun_sound gP hF CFSG.KD.McL.Bind.qA2
  have hb3 := bindRun_sound gP hF CFSG.KD.McL.Bind.qA3
  have hb4 := bindRun_sound gP hF CFSG.KD.McL.Bind.qA4
  have hb5 := bindRun_sound gP hF CFSG.KD.McL.Bind.qA5
  have hcov : ∀ r < 78, 0xf8000000000000003ff / 2 ^ (r + 1) % 2 = 1 ∨
      0x70000000000000000001 / 2 ^ (r + 1) % 2 = 1 ∨ 0x1ffffc01 / 2 ^ (r + 1) % 2 = 1 ∨
      0x28c207ea0000001 / 2 ^ (r + 1) % 2 = 1 ∨ 0x7ffd73df8140000001 / 2 ^ (r + 1) % 2 = 1 := by
    decide
  intro r hr
  rw [← fval_XT gP (fun i hi => by have := qr_letters hr i hi; omega)]
  rcases hcov r hr with h | h | h | h | h
  · obtain ⟨-, k, hk, hl, he⟩ := hb1 r h
    rw [he]
    exact hA1 k hk (by rcases hl with hl | hl <;> exact hl)
  · obtain ⟨-, k, hk, hl, he⟩ := hb2 r h
    rw [he]
    exact hA2 k hk (by rcases hl with hl | hl <;> exact hl)
  · obtain ⟨-, k, hk, hl, he⟩ := hb3 r h
    rw [he]
    exact hA3 k hk (by rcases hl with hl | hl <;> exact hl)
  · obtain ⟨-, k, hk, hl, he⟩ := hb4 r h
    rw [he]
    exact hA4 k hk (by rcases hl with hl | hl <;> exact hl)
  · obtain ⟨-, k, hk, hl, he⟩ := hb5 r h
    rw [he]
    exact hA5 k hk (by rcases hl with hl | hl <;> exact hl)

@[expose] def orbM (l : ℕ) : ℕ := [13, 5, 4, 3, 2, 1, 15].getD l 0
@[expose] def orbN (l : ℕ) : ℕ := [14, 6, 5, 4, 3, 2, 16].getD l 0
@[expose] noncomputable def orbJ (l : ℕ) : ℕ :=
  [CFSG.KD.McL.M.OJ0, CFSG.KD.McL.M.OJ1, CFSG.KD.McL.M.OJ2, CFSG.KD.McL.M.OJ3, CFSG.KD.McL.M.OJ4,
    CFSG.KD.McL.M.OJ5, CFSG.KD.McL.M.OJ6].getD l 0

theorem model : ∃ (ψ : ℕ → Sporadic.mclPresentation.Group) (I : Set ℕ),
    (McL.pid 44 ∈ I ∧ ψ (McL.pid 44) = 1) ∧
    (∀ p ∈ I, ∀ q ∈ I, McL.pmul 44 p q ∈ I ∧ ψ (McL.pmul 44 p q) = ψ p * ψ q) ∧
    (∀ p ∈ I, McL.Sub.pinv 44 p ∈ I ∧ ψ (McL.Sub.pinv 44 p) = (ψ p)⁻¹) ∧
    (∀ p ∈ I, McL.pairOK 44 p (McL.Sub.pinv 44 p) = true) ∧
    (∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :=
  McLM.model_sound (yv gP) (by norm_num) CFSG.KD.McL.Bind.mGens CFSG.KD.McL.Bind.mRels
    (fun r hr i hi => qr_letters hr i hi) CFSG.KD.McL.M.ents (epWrap_sound ep_M)
    (OM := orbM) (OJ := orbJ) (ON := orbN) (nLev := 7)
    (by
      intro l hl
      interval_cases l
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb0, by
          have h := CFSG.KD.McL.M.bp0
          rwa [Nat.blt_eq] at h⟩
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb1, by
          have h := CFSG.KD.McL.M.bp1
          rwa [Nat.blt_eq] at h⟩
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb2, by
          have h := CFSG.KD.McL.M.bp2
          rwa [Nat.blt_eq] at h⟩
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb3, by
          have h := CFSG.KD.McL.M.bp3
          rwa [Nat.blt_eq] at h⟩
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb4, by
          have h := CFSG.KD.McL.M.bp4
          rwa [Nat.blt_eq] at h⟩
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb5, by
          have h := CFSG.KD.McL.M.bp5
          rwa [Nat.blt_eq] at h⟩
      · exact ⟨Nat.eq_of_beq_eq_true CFSG.KD.McL.M.orb6, by
          have h := CFSG.KD.McL.M.bp6
          rwa [Nat.blt_eq] at h⟩)
    (by simp [Finset.prod_range_succ, orbN]) cq_bound qrel

theorem t_sq : pval gP (McL.Rels.XT 6) * pval gP (McL.Rels.XT 6) = 1 := by
  rw [pval_XT gP 6 (by norm_num)]
  have h3 := (yv_eq gP).2.2.2
  have e : letV (yv gP) 6 = yv gP 3 := by simp [letV]
  rw [e, h3]
  calc gP 1 * gP 0 * (gP 1)⁻¹ * (gP 1 * gP 0 * (gP 1)⁻¹) = gP 1 * (gP 0 * gP 0) * (gP 1)⁻¹ := by
        group
    _ = 1 := by
        rw [a_sq]
        group

end CertificateChecks.KernelMcL

end
