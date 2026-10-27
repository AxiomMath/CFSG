module

public import Certificates.Kernel.Fin76bOm.Rec
public import Certificates.Kernel.Fin76bOm.Checks
public import CFSG.Certificates.Kernel.Fin76bOm.TwinSound

public section

namespace CertificateChecks.KernelC24608

open CFSG.KC.YoshQ CFSG.KC.Fin76bOm CFSG.EvenSporadicStandard.Fin76b
open CFSG.EvenSporadicStandard.Fin76b.W16

theorem j2Om_recs : OmRecs 32 6 j2Og (J2OmT 4) J2W.GS J2W.RL J2W.cnt J2W.EP J2W.PL J2W.POS J2W.SM
    J2W.SF J2E.GS J2E.RL J2E.cnt J2E.EP J2E.PL J2E.POS J2E.SM J2E.SF where
  dims := ⟨by decide, by decide, by decide, by decide⟩
  recW := ⟨by rw [j2Og, ← j2_gs.1], j2W_rec.1, j2W_rec.2⟩
  recE := ⟨rfl, j2E_rec.1, j2E_rec.2⟩
  roots := j2_gs.2
  cntW := j2Om_facts.1
  cntE := j2Om_facts.2.1
  permT := j2Om_perm.1
  permW := j2Om_perm.2.1
  permE := j2Om_perm.2.2

theorem j3Om_recs : OmRecs 80 7 j3Og (J3OmT 5) J3W.GS J3W.RL J3W.cnt J3W.EP J3W.PL J3W.POS J3W.SM
    J3W.SF J3E.GS J3E.RL J3E.cnt J3E.EP J3E.PL J3E.POS J3E.SM J3E.SF where
  dims := ⟨by decide, by decide, by decide, by decide⟩
  recW := ⟨by rw [j3Og, ← j3_gs.1], j3W_rec.1, j3W_rec.2⟩
  recE := ⟨rfl, j3E_rec.1, j3E_rec.2⟩
  roots := j3_gs.2
  cntW := j3Om_facts.1
  cntE := j3Om_facts.2.1
  permT := j3Om_perm.1
  permW := j3Om_perm.2.1
  permE := j3Om_perm.2.2

theorem tbl_of {n w : Nat} {L : List Nat} {M : Nat → Nat → Nat}
    (h : ((List.range 32).all fun a => (List.range 32).all fun b => mulIdxN n w L a b == M a b) =
      true) : ∀ a < 32, ∀ b < 32, mulIdxN n w L a b = M a b := by
  intro a ha b hb
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb

theorem j2Om_wCheck : wCheck 32 32 2000 (tabN 32 6 (J2OmT 4)) j2Og = true :=
  wCheck_of j2Om_recs j2Om_facts.2.2.1 j2Om_facts.2.2.2.1 j2Om_facts.2.2.2.2.1 j2Om_ord
    j2Om_facts.2.2.2.2.2.1

theorem j3Om_wCheck : wCheck 80 80 2000 (tabN 80 7 (J3OmT 5)) j3Og = true :=
  wCheck_of j3Om_recs j3Om_facts.2.2.1 j3Om_facts.2.2.2.1 j3Om_facts.2.2.2.2.1 j3Om_ord
    j3Om_facts.2.2.2.2.2.1

end CertificateChecks.KernelC24608

end
