module

public import Certificates.Kernel.J3Coset.Defs
public import CFSG.Certificates.Kernel.J3Coset.Sound
import Certificates.Kernel.J3Coset.ChecksSmall
import Certificates.Kernel.J3Coset.ChecksPerm
import Certificates.Kernel.J3Coset.ChecksRel0
import Certificates.Kernel.J3Coset.ChecksRel1
import Certificates.Kernel.J3Coset.ChecksRel2
import Certificates.Kernel.J3Coset.ChecksRel3
import Certificates.Kernel.J3Coset.ChecksFor0
import Certificates.Kernel.J3Coset.ChecksFor1
import Certificates.Kernel.J3Coset.ChecksRec
import Certificates.Kernel.Sporadic.ON.Gen

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.Enum CFSG.KC.J3C CFSG.KS CFSG.KS.Raw.Orb CFSG.KD.J3C

end CertificateChecks.KernelJ3C

#kon_join CertificateChecks.KernelJ3C.permAll CertificateChecks.KernelJ3C.permSl 80
#kon_join CertificateChecks.KernelJ3C.kAll CertificateChecks.KernelJ3C.kSl 80
#kon_join CertificateChecks.KernelJ3C.pAll CertificateChecks.KernelJ3C.pSl 80
#kon_join CertificateChecks.KernelJ3C.sAll CertificateChecks.KernelJ3C.sSl 80
#kon_join CertificateChecks.KernelJ3C.relAll CertificateChecks.KernelJ3C.relSl 80
#kon_join CertificateChecks.KernelJ3C.forAll CertificateChecks.KernelJ3C.forChk 40
#kon_join CertificateChecks.KernelJ3C.recAll CertificateChecks.KernelJ3C.recChk 31

namespace CertificateChecks.KernelJ3C

open CFSG.KC.Enum CFSG.KC.J3C CFSG.KS CFSG.KS.Raw.Orb CFSG.KD.J3C

abbrev nn : ℕ := 25840

theorem slice_all {f : Nat → Bool} (h : ∀ s < 80, slice f s = true) : ∀ y < nn, f y = true := by
  intro y hy
  have hy' : y < 25840 := hy
  have hs := h (y / 323) (by omega)
  unfold slice at hs
  rw [strictB_eq, allN_iff] at hs
  have h1 := hs (y % 323) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (y / 323) 323) (y % 323) = y := by
    change (y / 323) * 323 + y % 323 = y
    omega
  rwa [e] at h1

theorem beq_iff' {a b : Nat} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem perm_facts : ∀ y < nn, tb 0 y < nn ∧ tb 0 (tb 0 y) = y ∧ tb 2 y < nn ∧ tb 3 y < nn ∧
    tb 3 (tb 2 y) = y ∧ tb 2 (tb 3 y) = y ∧ tb 8 y < nn ∧ tb 9 y < nn ∧ tb 9 (tb 8 y) = y ∧
    tb 8 (tb 9 y) = y := by
  intro y hy
  have h := slice_all (fun s hs => permAll s hs) y hy
  unfold permPt at h
  simp only [bAnd_iff, Nat.blt_eq, beq_iff'] at h
  exact h

theorem rel_facts : ∀ y < nn, ∀ r ∈ rels, wv tb r y = y := fun y hy =>
  relPt_spec (slice_all (fun s hs => relAll s hs) y hy)

theorem k_facts : ∀ y < nn, tb 4 y = wv tb wK1 y ∧ tb 5 y = wv tb wK2 y := by
  intro y hy
  have h := slice_all (fun s hs => kAll s hs) y hy
  unfold kPt at h
  simp only [bAnd_iff, beq_iff'] at h
  exact h

theorem p_facts : ∀ y < nn, tb 6 y = wv tb wP1 y ∧ tb 7 y = wv tb wP2 y := by
  intro y hy
  have h := slice_all (fun s hs => pAll s hs) y hy
  unfold pPt at h
  simp only [bAnd_iff, beq_iff'] at h
  exact h

theorem s_facts : ∀ y < nn, tb 8 (tb 0 y) = wv tb phiA (tb 8 y) ∧
    tb 8 (tb 2 y) = wv tb phiB (tb 8 y) := by
  intro y hy
  have h := slice_all (fun s hs => sAll s hs) y hy
  unfold sPt at h
  simp only [bAnd_iff, beq_iff'] at h
  exact h

theorem forest_facts {f : ℕ} (hf : f < 40) : ∀ p < nn,
    fOK nn (fun q => e64 FT (Nat.add (Nat.mul f 25856) q)) (fun j q => wv tb (fgw f j) q)
      (rf f) p = true := by
  have h := forAll f hf
  unfold forChk at h
  exact allN_iff.1 h

theorem rec_facts : ∀ r ∈ Oc.flatten, recOK r = true := by
  intro r hr
  obtain ⟨l, hl, hrl⟩ := List.mem_flatten.1 hr
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
  have hc31 : c < 31 := by
    have h := idx_ok
    simp only [idxChk, Bool.and_eq_true, beq_iff_eq] at h
    have h31 : Oc.length = 31 := h.1.2
    omega
  have h := recAll c hc31
  unfold recChk at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some,
    List.all_eq_true] at h
  exact h r hrl

end CertificateChecks.KernelJ3C

end
