module

public import Certificates.Kernel.Sporadic.Fi22.HypW
public import Certificates.Kernel.Sporadic.Fi22.HypCBGlue
public import CFSG.Monster.B.Fischer.Fi22ModelBase1

public section

namespace CertificateChecks.KernelSpor.Fi22W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem prep_GO : PRep 3510 12 Fi22X.GO fi22U := by
  have h := rep_fi22U
  rw [Fi22X.go_eq] at h
  exact prep_of_rep h

private theorem prep_c {P Q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g)
    (hQ : PRep 3510 12 Q h) : PRep 3510 12 (Fi22X.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem exists_of_zOK
    {P T : ℕ}
    {t : Equiv.Perm (Fin 3510)} (ht : PRep 3510 12 T t) (h : zOK P T = true) :
    ∃ c ∈ fi22R, c ∉ fi22P ∧ c * t = t * c := by
  simp only [zOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hc, hp, hs, e⟩ := h
  obtain ⟨g, hg, rg⟩ := Fi22R1.exists_mem_P hc hp hs
  have rz : PRep 3510 12 (Fi22X.c P Fi22X.GO) (g * fi22U) := prep_c rg prep_GO
  refine ⟨g * fi22U, fi22R.mul_mem (fi22P_le_R hg) fi22U_mem_R, fun hm => fi22U_not_mem ?_,
    prep_unique (prep_c rz ht) (by rw [e]; exact prep_c ht rz)⟩
  simpa using fi22P.mul_mem (fi22P.inv_mem hg) hm

theorem orderOf_of_invoOK {C : ℕ} {g : Equiv.Perm (Fin 3510)} (hg : PRep 3510 12 C g)
    (h : invoOK C = true) : orderOf g = 2 := by
  simp only [invoOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hm, hsq⟩ := h
  have h2 : g ^ 2 = 1 := by
    have hgg := prep_c hg hg
    rw [hsq] at hgg
    rw [sq]
    exact prep_unique hgg (prep_pidn (by norm_num) (by norm_num))
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [h1] at hg
  have hf := notB_true hm
  rw [allN_iff.2 fun x hx => ?_] at hf
  · exact Bool.noConfusion hf
  · simpa [Nat.beq_eq] using hg ⟨x, hx⟩

theorem exists_of_foursOK
    {L T : ℕ} {t : Equiv.Perm (Fin 3510)} (ht : PRep 3510 12 T t) (h : foursOK L T = true) :
    ∃ l ∈ fi22P, orderOf (l * t * l⁻¹ * t⁻¹) = 2 := by
  simp only [foursOK, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hp, hpt, hs, hi⟩ := h
  obtain ⟨l, hl, rl⟩ := Fi22R1.exists_mem_P hc hp hs
  exact ⟨l, hl, orderOf_of_invoOK (prep_c (prep_c (prep_c rl ht) (prep_inv_of_permOK rl hp))
    (prep_inv_of_permOK ht hpt)) hi⟩

theorem exists_comm_not_mem
    {k : ℕ} (hk : k < 6) :
    ∃ c ∈ fi22R, c ∉ fi22P ∧ c * fi22ExtRep k = fi22ExtRep k * c :=
  exists_of_zOK (Fi22CB.prep_ext hk) (allN_spec zAll k hk)

theorem exists_fours
    {k : ℕ} (h3 : 3 ≤ k) (hk : k < 6) :
    ∃ l ∈ fi22P, orderOf (l * fi22ExtRep k * l⁻¹ * (fi22ExtRep k)⁻¹) = 2 := by
  obtain ⟨i, hi, rfl⟩ : ∃ i < 3, k = 3 + i := ⟨k - 3, by omega, by omega⟩
  have h : foursOK (Fi22WT (6 + i)) (Fi22ExtT.L (21 + (3 + i))) = true := by
    rw [show 21 + (3 + i) = 24 + i by omega]
    exact allN_spec foursAll i hi
  exact exists_of_foursOK (Fi22CB.prep_ext hk) h

end CertificateChecks.KernelSpor.Fi22W

end
