
module

public import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
public import Certificates.Kernel.Sporadic.Fi24Form.Final
import Certificates.Kernel.Sporadic.Fi24Orb.Small
public import CFSG.Perm.ChainOrbits
public import CFSG.Sporadic.Fi24.SimpleBase
public import Certificates.Kernel.Sporadic.Fi24Orb.Core

public section

namespace CertificateChecks.KernelFi24OrbL

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.KC.Fi24Orb CFSG.KD.Fi24Net CFSG.KS.Fi24Net
  CertificateChecks.KernelFi24Orb

theorem ptSub_eq : ∀ k < 306936, ptSub k = f k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [f_zero]
      rfl
    · obtain ⟨hp, hl⟩ := CertificateChecks.KernelFi24Orb.tree hk (by omega)
      have hpar := orb_par_orbL k hk
      have hlab := orb_lab_orbL k hk
      have hp' : ap orb.par k < k := by rw [hpar]; exact hp
      have ih' := ih _ hp' (by omega)
      have hpN : oPar (CFSG.KD.Fi24Orb.OL k) < N := lt_trans hp hk
      obtain ⟨hs, hw⟩ := formAt_facts orb (ap orb.par k)
      change rowSpan 253 (formAt gensT orb rootForm k).rows = _
      rw [formAt_pos _ _ _ hpos hp', hlab]
      rcases hl with ⟨h1, he⟩ | ⟨h2, he⟩
      · rw [h1, gensT_get_one, rowSpan_stepForm rowsWF_matAT matAT_size hw hs, matW_matAT_T]
        change (ptSub (ap orb.par k)).map _ = _
        rw [ih', hpar]
        conv_rhs => rw [← he]
        rw [f_α hpN, act_uA]
      · rw [h2, gensT_get_two, rowSpan_stepForm rowsWF_matBT matBT_size hw hs, matW_matBT_T]
        change (ptSub (ap orb.par k)).map _ = _
        rw [ih', hpar]
        conv_rhs => rw [← he]
        rw [f_β hpN, act_uB]

theorem pt_sp_rank : ∀ k < 306936, (pt k).sp = CertificateChecks.KernelFi24Orb.f k := by
  intro k hk
  rw [pt_sp, ptSub_eq k hk]

end CertificateChecks.KernelFi24OrbL
