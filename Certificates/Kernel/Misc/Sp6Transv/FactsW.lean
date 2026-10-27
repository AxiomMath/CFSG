module

public import Certificates.Kernel.Misc.Sp6Transv.FactsN

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6Transv.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6Transv

variable {z : Fin 3 → H6} {t s f0 f2 : H6} {q : Fin 5 → H6}

@[expose] noncomputable def ltr (z : Fin 3 → H6) (t s f0 f2 : H6) : ℕ → H6
  | 0 => f0
  | 1 => s
  | 2 => f2
  | 3 => t
  | 4 => z 0
  | 5 => z 1
  | 6 => z 2
  | _ => gT

@[expose] noncomputable def rep (z : Fin 3 → H6) : ℕ → H6
  | 0 => z 1
  | 1 => z 0 * z 1
  | _ => z 0 * z 1 * z 2

theorem Hyp.t_inv (H : Hyp z t s f0 f2 q) : t⁻¹ = t * t :=
  inv_eq_of_mul_eq_one_right (eq_of_enc (by rw [← mul_assoc, emul, emul, H.et, enc_one]; decide +kernel))

theorem Hyp.enc_L (H : Hyp z t s f0 f2 q) : ∀ l < 8, L l = enc6 (ltr z t s f0 f2 l) := by
  intro l hl
  interval_cases l
  · exact H.ef0.symm
  · rw [ltr, H.es]; decide +kernel
  · exact H.ef2.symm
  · rw [ltr, H.et]; decide +kernel
  · rw [ltr, H.ez0]; decide +kernel
  · rw [ltr, H.ez1]; decide +kernel
  · rw [ltr, H.ez2]; decide +kernel
  · exact enc_gT.1.symm

theorem Hyp.enc_LI (H : Hyp z t s f0 f2 q) : ∀ l < 8, LI l = enc6 (ltr z t s f0 f2 l)⁻¹ := by
  intro l hl
  have i0 : f0⁻¹ = f0 := inv_eq_of_mul_eq_one_right H.f0_sq
  have i2 : f2⁻¹ = f2 := inv_eq_of_mul_eq_one_right H.f2_sq
  interval_cases l
  · rw [ltr, i0, H.ef0]; decide +kernel
  · rw [ltr, H.s_inv, H.es]; decide +kernel
  · rw [ltr, i2, H.ef2]; decide +kernel
  · rw [ltr, H.t_inv, emul, H.et]; decide +kernel
  · rw [ltr, H.z_inv0, emul, H.ez0]; decide +kernel
  · rw [ltr, H.z_inv1, emul, H.ez1]; decide +kernel
  · rw [ltr, H.z_inv2, emul, H.ez2]; decide +kernel
  · exact enc_gT.2.symm

theorem Hyp.enc_rep (H : Hyp z t s f0 f2 q) : ∀ r < 3, REP r = enc6 (rep z r) := by
  intro r hr
  interval_cases r
  · rw [rep, H.ez1]; decide +kernel
  · rw [rep, emul, H.ez0, H.ez1]; decide +kernel
  · change REP 2 = enc6 (z 0 * z 1 * z 2)
    rw [emul, emul, H.ez0, H.ez1, H.ez2]; decide +kernel

@[expose] noncomputable def welt (z : Fin 3 → H6) (t : H6) (w : ℕ) : H6 :=
  z 0 ^ Nat.div w 27 * z 1 ^ Nat.mod (Nat.div w 9) 3 * z 2 ^ Nat.mod (Nat.div w 3) 3 *
    t ^ Nat.mod w 3

theorem Hyp.enc_welt (H : Hyp z t s f0 f2 q) (w : ℕ) :
    enc6 (welt z t w) = wElt (KS 1) (KS 2) (KS 3) (KS 4) w := by
  rw [welt, emul, emul, emul, enc6_pow, enc6_pow, enc6_pow, enc6_pow, H.ez0, H.ez1, H.ez2, H.et]
  rfl

theorem w_parts : ∀ w < 81, wordAt (KS 1) (KS 2) (KS 3) (KS 4) L LI REP WR w = true := by
  have h : wB 0 = true := WK.all 0 (by norm_num)
  unfold wB at h
  obtain ⟨h1, -⟩ := andB_eq_true h
  exact fun w hw => (allR_iff _ _ _).1 h1 w (Nat.zero_le _) (by omega)

theorem z_recs : WR 27 % 4 = 1 ∧ WR 54 % 4 = 1 ∧ WR 9 % 4 = 1 ∧ WR 18 % 4 = 1 ∧ WR 3 % 4 = 1 ∧
    WR 6 % 4 = 1 := by
  decide +kernel

theorem Hyp.word_conj (H : Hyp z t s f0 f2 q) {w : ℕ} (hw : w < 81)
    (h3 : welt z t w ^ 3 = 1) (h1 : welt z t w ≠ 1) :
    ∃ r < 3, (r = 0 ∨ WR w % 4 ≠ 1) ∧ ∃ g : H6, welt z t w = g * rep z r * g⁻¹ := by
  have h := w_parts w hw
  unfold wordAt at h
  rw [letB_eq, letB_eq, ← H.enc_welt] at h
  cases hr : WR w with
  | zero =>
    rw [hr] at h
    change CFSG.KC.Ord.orB _ _ = true at h
    rcases orB_true h with e | e
    · have e3 : MULF (MULF (enc6 (welt z t w)) (enc6 (welt z t w))) (enc6 (welt z t w)) = ONE := by
        rw [← emul, ← emul, ← pow_three', h3, enc_one]
      rw [e3] at e
      exact absurd e (by decide)
    · exact absurd (eq_of_enc (by rw [enc_one]; exact Nat.eq_of_beq_eq_true e)) h1
  | succ r' =>
    rw [hr] at h
    change CFSG.KC.LQT.P.letB (r' % 4) _ = true at h
    rw [letB_eq, letB_eq, letB_eq, letB_eq] at h
    obtain ⟨hri, he⟩ := andB_eq_true h
    have hri' : r' % 4 < 3 := Nat.blt_eq.mp hri
    rw [wordI_enc H.enc_LI, wordF_enc H.enc_L, ← emul, ← emul, H.enc_rep _ hri'] at he
    obtain ⟨g, hg⟩ : ∃ g : H6, g⁻¹ * welt z t w * g = rep z (r' % 4) :=
      ⟨_, eq_of_enc (Nat.eq_of_beq_eq_true he)⟩
    refine ⟨r' % 4, hri', ?_, g, by rw [← hg]; group⟩
    by_cases h0 : r' % 4 = 0
    · exact Or.inl h0
    · right
      omega

end CertificateChecks.KernelMisc.Sp6Transv.Facts

end
