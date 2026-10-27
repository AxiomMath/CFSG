module

public import Certificates.Kernel.McL.Relators
import CFSG.Certificates.Kernel.McLLabSound

public section

namespace CertificateChecks.KernelMcL

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.Certificates CFSG.Certificates.LCE
  CFSG.Certificates.McLS CFSG.Certificates.McLD TauCeti
open CertificateChecks.KernelHe CertificateChecks.KernelRu

theorem tcRT : ∀ r < 15, LceS.wWord (McL.TC.sel r) < 2 ^ (8 * LceS.wLen (McL.TC.sel r)) ∧
    bval gP (LceS.wWord (McL.TC.sel r)) (LceS.wLen (McL.TC.sel r)) = 1 := fun r hr => tc_ok r hr

theorem am_t : ∀ k < CFSG.KD.McL.AM.nT, CFSG.KD.McL.AM.TL k = McL.pid CFSG.KD.McL.AM.d →
    bval gP (LceS.wWord (CFSG.KD.McL.AM.TW k)) (LceS.wLen (CFSG.KD.McL.AM.TW k)) = 1 :=
  McLLab.targets_sound gP tcRT (wtPer0_sound per_AM) CFSG.KD.McL.AM.wd
    CFSG.KD.McL.AM.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.AM.one)
    (by decide) CFSG.KD.McL.AM.anc (by decide) rfl CFSG.KD.McL.AM.f0 rfl (by decide)
    CFSG.KD.McL.AM.tg rfl rfl rfl

theorem as_t : ∀ k < CFSG.KD.McL.AS.nT, CFSG.KD.McL.AS.TL k = McL.pid CFSG.KD.McL.AS.d →
    bval gP (LceS.wWord (CFSG.KD.McL.AS.TW k)) (LceS.wLen (CFSG.KD.McL.AS.TW k)) = 1 :=
  McLLab.targets_sound gP tcRT (wtPer0_sound per_AS) CFSG.KD.McL.AS.wd
    CFSG.KD.McL.AS.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.AS.one)
    (by decide) CFSG.KD.McL.AS.anc (by decide) rfl CFSG.KD.McL.AS.f0 rfl (by decide)
    CFSG.KD.McL.AS.tg rfl rfl rfl

theorem ai_t : ∀ k < CFSG.KD.McL.AI.nT, CFSG.KD.McL.AI.TL k = McL.pid CFSG.KD.McL.AI.d →
    bval gP (LceS.wWord (CFSG.KD.McL.AI.TW k)) (LceS.wLen (CFSG.KD.McL.AI.TW k)) = 1 :=
  McLLab.targets_sound gP tcRT (wtPer0_sound per_AI) CFSG.KD.McL.AI.wd
    CFSG.KD.McL.AI.inv (by decide) (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.McL.AI.one)
    (by decide) CFSG.KD.McL.AI.anc (by decide) rfl CFSG.KD.McL.AI.f0 rfl (by decide)
    CFSG.KD.McL.AI.tg rfl rfl rfl

section Model

variable (ψ : ℕ → Sporadic.mclPresentation.Group) (I : Set ℕ)

theorem hW_fval
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ W n, (∀ i < n, wLet W i < 6) → McL.evalW McL.Rels.MG 44 W n ∈ I ∧
      ψ (McL.evalW McL.Rels.MG 44 W n) = fval gP McL.Rels.XT W n := by
  intro W n h
  obtain ⟨h1, h2⟩ := hW W n h
  exact ⟨h1, h2.trans (fval_XT gP (fun i hi => by have := h i hi; omega)).symm⟩

theorem sl_BM
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ j < CFSG.KD.McL.BM.K, CFSG.KD.McL.BM.SL j ∈ I ∧ ψ (CFSG.KD.McL.BM.SL j) =
      bval gP (LceS.wWord (CFSG.KD.McL.BM.ST j)) (LceS.wLen (CFSG.KD.McL.BM.ST j)) := by
  have hs := subsOK_sound gP (smallTab_of small_XT) lt_XT norm_STBM am_t CFSG.KD.McL.Bind.sBM
  intro j hj
  obtain ⟨e1, e2⟩ := hs j hj
  rw [e1, e2]
  exact hW_fval ψ I hW _ _ (entsBelow_sound let_BM j hj)

theorem sl_BI
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ j < CFSG.KD.McL.BI.K, CFSG.KD.McL.BI.SL j ∈ I ∧ ψ (CFSG.KD.McL.BI.SL j) =
      bval gP (LceS.wWord (CFSG.KD.McL.BI.ST j)) (LceS.wLen (CFSG.KD.McL.BI.ST j)) := by
  have hs := subsOK_sound gP (smallTab_of small_XT) lt_XT norm_STBI am_t CFSG.KD.McL.Bind.sBI
  intro j hj
  obtain ⟨e1, e2⟩ := hs j hj
  rw [e1, e2]
  exact hW_fval ψ I hW _ _ (entsBelow_sound let_BI j hj)

theorem sl_BR
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ j < CFSG.KD.McL.BR.K, CFSG.KD.McL.BR.SL j ∈ I ∧ ψ (CFSG.KD.McL.BR.SL j) =
      bval gP (LceS.wWord (CFSG.KD.McL.BR.ST j)) (LceS.wLen (CFSG.KD.McL.BR.ST j)) := by
  have hs := subsOK_sound gP (smallTab_of small_XT) lt_XT norm_STBR am_t CFSG.KD.McL.Bind.sBR
  intro j hj
  obtain ⟨e1, e2⟩ := hs j hj
  rw [e1, e2]
  exact hW_fval ψ I hW _ _ (entsBelow_sound let_BR j hj)

set_option exponentiation.threshold 1000 in
theorem t_BM (hid : McL.pid 44 ∈ I ∧ ψ (McL.pid 44) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul 44 p q ∈ I ∧ ψ (McL.pmul 44 p q) = ψ p * ψ q)
    (hinv : ∀ p ∈ I, McL.Sub.pinv 44 p ∈ I ∧ ψ (McL.Sub.pinv 44 p) = (ψ p)⁻¹)
    (hval : ∀ p ∈ I, McL.pairOK 44 p (McL.Sub.pinv 44 p) = true)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ k < CFSG.KD.McL.BM.nT, CFSG.KD.McL.BM.TL k ∈ I ∧
      bval gP (LceS.wWord (CFSG.KD.McL.BM.TW k)) (LceS.wLen (CFSG.KD.McL.BM.TW k)) =
        ψ (CFSG.KD.McL.BM.TL k) :=
  McLLab.targetsB_sound gP ψ I hid hmul hinv hval (sl_BM ψ I hW) tcRT (wtPer0_sound per_BM)
    CFSG.KD.McL.BM.wd CFSG.KD.McL.BM.inv (by decide) (by decide) (by decide) rfl
    CFSG.KD.McL.BM.f0 rfl (by decide) CFSG.KD.McL.BM.tg rfl rfl rfl

set_option exponentiation.threshold 1000 in
theorem t_BI (hid : McL.pid 44 ∈ I ∧ ψ (McL.pid 44) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul 44 p q ∈ I ∧ ψ (McL.pmul 44 p q) = ψ p * ψ q)
    (hinv : ∀ p ∈ I, McL.Sub.pinv 44 p ∈ I ∧ ψ (McL.Sub.pinv 44 p) = (ψ p)⁻¹)
    (hval : ∀ p ∈ I, McL.pairOK 44 p (McL.Sub.pinv 44 p) = true)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ k < CFSG.KD.McL.BI.nT, CFSG.KD.McL.BI.TL k ∈ I ∧
      bval gP (LceS.wWord (CFSG.KD.McL.BI.TW k)) (LceS.wLen (CFSG.KD.McL.BI.TW k)) =
        ψ (CFSG.KD.McL.BI.TL k) :=
  McLLab.targetsB_sound gP ψ I hid hmul hinv hval (sl_BI ψ I hW) tcRT (wtPer0_sound per_BI)
    CFSG.KD.McL.BI.wd CFSG.KD.McL.BI.inv (by decide) (by decide) (by decide) rfl
    CFSG.KD.McL.BI.f0 rfl (by decide) CFSG.KD.McL.BI.tg rfl rfl rfl

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
theorem t_BR (hid : McL.pid 44 ∈ I ∧ ψ (McL.pid 44) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul 44 p q ∈ I ∧ ψ (McL.pmul 44 p q) = ψ p * ψ q)
    (hinv : ∀ p ∈ I, McL.Sub.pinv 44 p ∈ I ∧ ψ (McL.Sub.pinv 44 p) = (ψ p)⁻¹)
    (hval : ∀ p ∈ I, McL.pairOK 44 p (McL.Sub.pinv 44 p) = true)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ k < CFSG.KD.McL.BR.nT, CFSG.KD.McL.BR.TL k ∈ I ∧
      bval gP (LceS.wWord (CFSG.KD.McL.BR.TW k)) (LceS.wLen (CFSG.KD.McL.BR.TW k)) =
        ψ (CFSG.KD.McL.BR.TL k) := by
  have hj := mlab_join (mlab_join (mlab_join CFSG.KD.McL.BR.f0 CFSG.KD.McL.BR.f1)
    CFSG.KD.McL.BR.f2) CFSG.KD.McL.BR.f3
  exact McLLab.targetsB_sound (d := CFSG.KD.McL.BR.d) gP ψ I hid hmul hinv hval
    (sl_BR ψ I hW) tcRT (wtPer0_sound per_BR)
    CFSG.KD.McL.BR.wd CFSG.KD.McL.BR.inv (by decide) (by decide) (by decide)
    (Eq.refl (McL.Lab.mkS (nat_lit 0) (nat_lit 1))) hj rfl (by decide) CFSG.KD.McL.BR.tg rfl rfl rfl

theorem k1_trivial (hid : McL.pid 44 ∈ I ∧ ψ (McL.pid 44) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul 44 p q ∈ I ∧ ψ (McL.pmul 44 p q) = ψ p * ψ q)
    (hinv : ∀ p ∈ I, McL.Sub.pinv 44 p ∈ I ∧ ψ (McL.Sub.pinv 44 p) = (ψ p)⁻¹)
    (hval : ∀ p ∈ I, McL.pairOK 44 p (McL.Sub.pinv 44 p) = true)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ψ (McL.evalW McL.Rels.MG 44 (LceS.wWord McL.Rels.K1W) (LceS.wLen McL.Rels.K1W)) = 1 :=
  McLS.k1Run_sound gP ψ I (smallTab_of small_XT) (pval_XT_inv gP) hid hmul hinv
    (hW_fval ψ I hW) (t_BR ψ I hid hmul hinv hval hW)
    (fun i hi => ⟨entsBelow_sound let_KS i hi, entsBelow_sound let_KQ i hi⟩) t_sq
    CFSG.KD.McL.Bind.k1

theorem gr_rel (hid : McL.pid 44 ∈ I ∧ ψ (McL.pid 44) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul 44 p q ∈ I ∧ ψ (McL.pmul 44 p q) = ψ p * ψ q)
    (hinv : ∀ p ∈ I, McL.Sub.pinv 44 p ∈ I ∧ ψ (McL.Sub.pinv 44 p) = (ψ p)⁻¹)
    (hval : ∀ p ∈ I, McL.pairOK 44 p (McL.Sub.pinv 44 p) = true)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW McL.Rels.MG 44 W n ∈ I ∧ ψ (McL.evalW McL.Rels.MG 44 W n) = bval (yv gP) W n) :
    ∀ r < 34, ival (yv gP) (LceS.wWord (McL.Rels.GR r)) (LceS.wLen (McL.Rels.GR r)) = 1 := by
  have hk := k1_trivial ψ I hid hmul hinv hval hW
  have hBI := t_BI ψ I hid hmul hinv hval hW
  have hBM := t_BM ψ I hid hmul hinv hval hW
  have hFD := smallTab_of small_XD
  have hbAI := bindRun_sound gP hFD CFSG.KD.McL.Bind.gAI
  have hbAS := bindRun_sound gP hFD CFSG.KD.McL.Bind.gAS
  have hbBI := bindRun_sound gP hFD CFSG.KD.McL.Bind.gBI
  have hbBM := bindRun_sound gP hFD CFSG.KD.McL.Bind.gBM
  have hb0 := conjSubst_sound gP hFD tcRT CFSG.KD.McL.Bind.g0
  have hcov : ∀ r < 34, r = 0 ∨ 0xbf7f8001 / 2 ^ (r + 1) % 2 = 1 ∨
      0x7400071fd / 2 ^ (r + 1) % 2 = 1 ∨ 0x800001 / 2 ^ (r + 1) % 2 = 1 ∨
      0xe01 / 2 ^ (r + 1) % 2 = 1 := by
    decide
  have hNR : CFSG.KD.McL.D.NR = 34 := Nat.eq_of_beq_eq_true CFSG.KD.McL.D.xNR
  intro r hr
  have hlet := relsOK_sound CFSG.KD.McL.D.xRel r (by rw [hNR]; exact hr)
  rw [← fval_XD gP hlet]
  rcases hcov r hr with h | h | h | h | h
  · subst h
    exact hb0
  · obtain ⟨-, k, hk', hl, he⟩ := hbAI r h
    rw [he]
    exact ai_t k hk' (by rcases hl with hl | hl <;> exact hl)
  · obtain ⟨-, k, hk', hl, he⟩ := hbAS r h
    rw [he]
    exact as_t k hk' (by rcases hl with hl | hl <;> exact hl)
  · obtain ⟨-, k, hk', hl, he⟩ := hbBI r h
    rw [he, (hBI k hk').2]
    rcases hl with hl | hl
    · rw [hl]
      exact hid.2
    · rw [hl]
      exact hk
  · obtain ⟨-, k, hk', hl, he⟩ := hbBM r h
    rw [he, (hBM k hk').2]
    rcases hl with hl | hl
    · rw [hl]
      exact hid.2
    · rw [hl]
      exact hk

end Model

theorem relsP : (∀ r < 79, bval (yv gP) (LceS.wWord (McL.Rels.NR1 r))
      (LceS.wLen (McL.Rels.NR1 r)) = 1) ∧
    (∀ r < 34, ival (yv gP) (LceS.wWord (McL.Rels.GR r)) (LceS.wLen (McL.Rels.GR r)) = 1) := by
  obtain ⟨ψ, I, hid, hmul, hinv, hval, hW⟩ := model
  refine ⟨?_, gr_rel ψ I hid hmul hinv hval hW⟩
  have hk1 : bval (yv gP) (LceS.wWord McL.Rels.K1W) (LceS.wLen McL.Rels.K1W) = 1 := by
    have hl : ∀ i < LceS.wLen McL.Rels.K1W, wLet (LceS.wWord McL.Rels.K1W) i < 6 :=
      nr1_letters 78 (by norm_num)
    rw [← (hW _ _ hl).2]
    exact k1_trivial ψ I hid hmul hinv hval hW
  intro r hr
  rcases Nat.lt_or_ge r 78 with h | h
  · rw [nr1_eq h]
    exact qrel r h
  · have : r = 78 := by omega
    subst this
    exact hk1

end CertificateChecks.KernelMcL

end
