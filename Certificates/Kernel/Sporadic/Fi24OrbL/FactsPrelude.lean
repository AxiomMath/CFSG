module

public import Certificates.Kernel.Sporadic.Fi24OrbL.FactsBase
import all Certificates.Kernel.Sporadic.Fi24OrbL.FactsBase

public import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
public import Certificates.Kernel.Sporadic.Fi24Form.Final
import Certificates.Kernel.Sporadic.Fi24Orb.Small

public section

namespace CertificateChecks.KernelFi24OrbL

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.KC.Fi24Orb CFSG.KD.Fi24Net CFSG.KS.Fi24Net
  CertificateChecks.KernelFi24Orb

theorem core_facts_proved : CoreFacts where
  A_sq := CertificateChecks.KernelFi24Form.A_sq
  B_cube := CertificateChecks.KernelFi24Form.B_cube
  AB_pow := by
    obtain ⟨c, e⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c23 c24
    rw [← uA_val, ← uB_val, uA_mat, uB_mat, ← e, ← pow29_mat c,
      Nat.eq_of_beq_eq_true CFSG.KD.Fi24Orb.ab_pow, mat_ONE]
  A_ne := by
    rw [← uA_val, uA_mat]
    exact ne_one_of c23 CFSG.KD.Fi24Orb.a_ne
  B_ne := by
    rw [← uB_val, uB_mat]
    exact ne_one_of c24 CFSG.KD.Fi24Orb.b_ne
  AB_ne := by
    obtain ⟨c, e⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ c23 c24
    rw [← uA_val, ← uB_val, uA_mat, uB_mat, ← e]
    exact ne_one_of c CFSG.KD.Fi24Orb.ab_ne
  A_form := CertificateChecks.KernelFi24Form.form_A
  B_form := CertificateChecks.KernelFi24Form.form_B
  card := card_Jc
  alpha := fun k hk => by
    have hlt : α k < N := α_lt hk
    refine ⟨by rw [orb_alpha_orbL k hk]; exact hlt, ?_⟩
    rw [ptSub_eq k hk, orb_alpha_orbL k hk]
    change _ = ptSub (α k)
    rw [ptSub_eq _ hlt, f_α hk, act_uA]
  beta := fun k hk => by
    have hlt : β k < N := β_lt hk
    refine ⟨by rw [orb_beta_orbL.2 k hk]; exact hlt, ?_⟩
    rw [ptSub_eq k hk, orb_beta_orbL.2 k hk]
    change _ = ptSub (β k)
    rw [ptSub_eq _ hlt, f_β hk, act_uB]
  inj := fun i hi j hj h => f_inj hi hj (by rwa [ptSub_eq i hi, ptSub_eq j hj] at h)
  tree := fun k hk hpos => by
    obtain ⟨hp, hl⟩ := fi24_core.2.2.2.2.2.2.1 k hk hpos
    refine ⟨by rw [orb_par_orbL k hk]; exact hp, ?_⟩
    rw [orb_lab_orbL k hk, orb_par_orbL k hk, orb_alpha_orbL _ (by omega),
      orb_beta_orbL.2 _ (by omega)]
    exact hl
  beta_inv := fun k hk => by
    have hT : CFSG.KS.TW.TR 306936 orb.beta β :=
      ⟨orb_beta_orbL.1, fun i hi => ⟨orb_beta_orbL.2 i hi, β_lt hi⟩⟩
    have hI := CFSG.KS.TW.invT_TR (g := fun i => β (β i)) (by norm_num) hT
      fun i hi => ⟨β_lt (β_lt hi), β_β_β hi, β_β_β hi⟩
    rw [(hI.2 _ (by rw [orb_beta_orbL.2 k hk]; exact β_lt hk)).1, orb_beta_orbL.2 k hk]
    exact β_β_β hk
  slp_ok := by
    have hs : chainWords.size = 13 := by decide
    unfold CFSG.Sporadic.Fi23.Native.slpOK
    refine allIn_eq_true.2 fun j _ hj => ?_
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨h1, h2⟩ := words_ok j (by omega) z hz
    beta_reduce
    rw [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  letters_size := letters_facts.1
  letters := fun j hj x hx => by
    have h1 : LN NW (2 * j) x < 306936 := by rw [LN_even]; exact (nets hj hx).1
    rw [letters_LN (2 * j) (by omega) x hx, letters_LN (2 * j + 1) (by omega) _ h1, LN_even,
      LN_odd]
    rw [LN_even] at h1
    exact ⟨h1, (nets hj hx).2.2.1⟩
  orbits := chain_orbits
  sub_orbit := sub_orbit

end CertificateChecks.KernelFi24OrbL
