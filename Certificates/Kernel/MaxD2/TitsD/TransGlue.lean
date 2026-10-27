module

public import Certificates.Kernel.MaxD2.TitsD.Glue
public import Certificates.Kernel.MaxD2.TitsD.Trans
public import Certificates.Kernel.MaxD2.TitsD.Inv0
public import Certificates.Kernel.MaxD2.TitsD.Inv1
public import CFSG.Certificates.Kernel.MaxD2.Trans

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum Certificates.MaxD2Perm

theorem inv_all {k : Nat} (hk : k < NE.cnt) : r32 INV k < NE.cnt ∧
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T k) (NE.T (r32 INV k)) = true := by
  have e : NE.cnt = 1200 := rfl
  have sl : ∀ lo, lo < 12 → allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add (100 * lo) d)) NE.cnt,
      permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add (100 * lo) d))
        (NE.T (r32 INV (Nat.add (100 * lo) d))))) = true := by
    intro lo hlo
    interval_cases lo
    exacts [inv_sl0, inv_sl100, inv_sl200, inv_sl300, inv_sl400, inv_sl500, inv_sl600, inv_sl700,
      inv_sl800, inv_sl900, inv_sl1000, inv_sl1100]
  have h := (PK.allN_iff.1 (sl (k / 100) (by omega))) (k % 100) (by omega)
  have ek : Nat.add (100 * (k / 100)) (k % 100) = k := by
    change 100 * (k / 100) + k % 100 = k
    omega
  rw [ek] at h
  obtain ⟨h1, h2⟩ := band_e h
  exact ⟨Nat.blt_eq.mp h1, h2⟩

theorem titsD_trans : checkTrans titsDData = true := by
  refine checkTrans_of hyps (INV := r32 INV) (CJ := r32 CJ) (fun k hk => inv_all hk)
    fun r hr => ?_
  have h := (PK.allN_iff.1 k_cj) r hr
  by_cases e : Nat.beq (RE.T r) (pidn 1755 11) = true
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · obtain ⟨h1, h2⟩ := band_e (bif_f (Bool.eq_false_iff.2 e) h)
    exact Or.inr ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem titsD_nonComm : checkNonComm titsDData = true := by
  have k : (Nat.blt (r32 NC 0) NE.k && (Nat.blt (r32 NC 1) NE.k && notInK RE.cnt RE.T
      (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11)
        (pcomp 1755 11 (mask 11) (NE.G (r32 NC 0)) (NE.G (r32 NC 1))) (NGI (r32 NC 0)))
        (NGI (r32 NC 1))))) = true := k_nc
  simp only [Bool.and_eq_true] at k
  obtain ⟨h1, h2, h3⟩ := k
  exact checkNonComm_of hyps (Nat.blt_eq.mp h1) (Nat.blt_eq.mp h2) h3

end CertificateChecks.KernelMaxD2.TitsD

end
