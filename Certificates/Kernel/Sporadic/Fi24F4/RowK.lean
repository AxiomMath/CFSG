module

public import Certificates.Kernel.Sporadic.Fi24F4.RowKC
public import Certificates.Kernel.Sporadic.Fi24F4.Let
public import Certificates.Kernel.LocalComp.Fi24TwoB.H15027
public import CFSG.Sporadic.Fi24I301.Words

public section

namespace CertificateChecks.KernelSpor.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.Fi24F4 CFSG.KS.Fi24F4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24I301 CertificateChecks.KernelSpor
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.KS.Raw.Orb (PRep)

theorem wdD4_eq : wdD4 = dWord ++ dWord ++ dWord ++ dWord := rfl

theorem wordG_dWord4 {G : Type*} [Group G] (L : ℤ → G) :
    CFSG.Sporadic.Th.wordG L wdD4 = CFSG.Sporadic.Th.wordG L dWord ^ 4 := by
  rw [wdD4_eq, wordG_append', wordG_append', wordG_append']
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem prep_Y : PRep 504 9 Y (CFSG.Sporadic.Th.wordG kLet dWord ^ 4) ∧
    canonK 504 9 (mask 9) (504 * 9) Y = true := by
  rw [← wordG_dWord4]
  exact prep_kWord (by decide) yRec

theorem card_N_centralizer :
    Nat.card ↥(fi24N ⊓ Subgroup.centralizer
      ({CFSG.Sporadic.Th.wordG kLet dWord ^ 4} : Set (Equiv.Perm (Fin 504)))) = 256 := by
  obtain ⟨hmem, hcard, hvalid⟩ := fi24N_spec CertificateChecks.KernelLC.Fi24B.nOK
  rw [CertificateChecks.KernelLC.Fi24B.pts_size] at hmem hcard hvalid
  rw [card_inf_eq_length_filter (fun i => permOfArr 504 fi24NCert.pts[i]!) hmem hcard
    (fun i => pcomp 504 9 (mask 9) (CertificateChecks.KernelLC.Fi24BN.T i) Y ==
      pcomp 504 9 (mask 9) Y (CertificateChecks.KernelLC.Fi24BN.T i)) ?_]
  · rw [← Nat.eq_of_beq_eq_true cnt, cntComm_eq, List.range_eq_range']
  · intro i hi
    have hr := CFSG.RankThree.Native.rep_of_validA (hvalid i hi)
    rw [CertificateChecks.KernelLC.Fi24B.pt_get hi] at hr ⊢
    have hP : PRep 504 9 (CertificateChecks.KernelLC.Fi24BN.T i)
        (permOfArr 504 (unpack 504 9 (CertificateChecks.KernelLC.Fi24BN.T i))) := prep_of_rep hr
    rw [Subgroup.mem_centralizer_singleton_iff, beq_iff_eq,
      ← comm_iff (by norm_num) (by norm_num) hP prep_Y.1]

end CertificateChecks.KernelSpor.Fi24F4

end
