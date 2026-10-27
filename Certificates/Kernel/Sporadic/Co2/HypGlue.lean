module

public import Certificates.Kernel.Sporadic.Co2.HypZ
public import Certificates.Kernel.Sporadic.Co2.HypT
public import Certificates.Kernel.Sporadic.Co2.HypU
public import Certificates.Kernel.Sporadic.Co2.HypE8
public import Certificates.Kernel.Co2Smith.ChainCard
public import Certificates.Kernel.SporSch.Co2M.FratG
public import CFSG.Certificates.Kernel.Spor.CommBaseSound
public import CFSG.Sporadic.Co2Schreier.ThirdOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.Co2HG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.CommBase
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.Co2Cert
open CFSG.Sporadic.Co2Schreier CFSG.EvenSporadicStandard.HypOne
open CertificateChecks.KernelCo2Smith (permK prep_of_permOK mem_P_of_sift comm_of_pcomp)

theorem band (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem prep_c {P Q : ℕ} {g h : Equiv.Perm (Fin 2300)} (hP : PRep 2300 12 P g)
    (hQ : PRep 2300 12 Q h) : PRep 2300 12 (Co2H.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_one : PRep 2300 12 (pidn 2300 12) 1 := prep_pidn (by norm_num) (by norm_num)

theorem pow5_eq_one {P : ℕ} {g : Equiv.Perm (Fin 2300)} (hP : PRep 2300 12 P g)
    (h : Co2H.pow5 P = pidn 2300 12) : g ^ 5 = 1 := by
  have h5 : PRep 2300 12 (Co2H.pow5 P) (g * (g * (g * (g * g)))) :=
    prep_c hP (prep_c hP (prep_c hP (prep_c hP hP)))
  rw [h] at h5
  have e := CFSG.KC.CommBase.prep_unique h5 prep_one
  rw [← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem letOK_facts {L : ℕ → ℕ} {R m : ℕ} (h : Co2H.letOK L R m = true) {z : ℕ} (hz : z < m) :
    Co2H.perm (L z) (L (m + 1 + z)) = true ∧ Co2H.siftP (L z) = true ∧
      Nat.beq (Co2H.c (L z) R) (Co2H.c R (L z)) = true ∧ Co2H.pow5 (L z) = pidn 2300 12 := by
  have h1 := CFSG.KS.allN_spec h z hz
  simp only [band, Bool.and_eq_true] at h1
  obtain ⟨a, b, c, d⟩ := h1
  exact ⟨a, b, c, Nat.eq_of_beq_eq_true d⟩

@[expose] noncomputable def ell (L : ℕ → ℕ) (x : Equiv.Perm (Fin 2300)) (m z : ℕ) :
    Equiv.Perm (Fin 2300) :=
  if z < m then permK (L z) else if z = m then x else (permK (L (z - (m + 1))))⁻¹

theorem fourClassesLarge_of_letters
    {L : ℕ → ℕ} {R m : ℕ} {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 R x) (hm : L m = R)
    (hl : Co2H.letOK L R m = true) {B : List BaseRec} {PF ZF DF : ℕ}
    (hb : commBaseOK 2300 12 (mask 12) L (2 * m + 1) B PF ZF DF = true) :
    FourClassesLarge ↥(centralizerIn co2P x) := by
  have hP : ∀ z < m, PRep 2300 12 (L z) (permK (L z)) := fun z hz =>
    prep_of_permOK (letOK_facts hl hz).1
  have hmem : ∀ z < m, permK (L z) ∈ centralizerIn co2P x ∧ permK (L z) ^ 5 = 1 := by
    intro z hz
    obtain ⟨-, h2, h3, h4⟩ := letOK_facts hl hz
    exact ⟨mem_centralizerIn.2 ⟨mem_P_of_sift (hP z hz) h2, comm_of_pcomp (hP z hz) hx h3⟩,
      pow5_eq_one (hP z hz) h4⟩
  refine fourClassesLarge_of_commBase (ℓ := ell L x m) _ (fun z hz => ?_) (fun z hz => ?_) hb
  · unfold ell
    split_ifs with h1 h2
    · exact hP z h1
    · rw [h2, hm]
      exact hx
    · have hi : z - (m + 1) < m := by omega
      have e : m + 1 + (z - (m + 1)) = z := by omega
      have h := CFSG.KC.CommBase.prep_inv_of_permOK (hP _ hi) (letOK_facts hl hi).1
      rw [e] at h
      exact h
  · unfold ell
    split_ifs with h1 h2
    · exact Or.inl (hmem z h1)
    · exact Or.inr fun k hk => (mem_centralizerIn.1 hk).2
    · have hi : z - (m + 1) < m := by omega
      obtain ⟨h5, h6⟩ := hmem _ hi
      exact Or.inl ⟨(centralizerIn co2P x).inv_mem h5, by rw [inv_pow, h6, inv_one]⟩

theorem prep_z :
    PRep 2300 12 Co2HZ.R locZ := by
  have hz : unpack 2300 12 (KernelSporSch.Co2M.WE 0) = zArr := by
    have e : KernelSporSch.Co2M.ztP 0 = KernelSporSch.Co2M.zP := by
      simp [KernelSporSch.Co2M.ztP]
    exact KernelSporSch.Co2M.unpack_eq KernelSporSch.Co2M.zRep
      (e ▸ CFSG.KS.allN_spec KernelSporSch.Co2M.bind_e 0 (by norm_num))
  have h := KernelSporSch.Co2M.repK_z
  rw [← hz] at h
  exact prep_of_rep h

theorem prep_t :
    PRep 2300 12 Co2HT.R locT := by
  have ht : unpack 2300 12 (KernelSporSch.Co2M.WE 1) = tArr := by
    have e : KernelSporSch.Co2M.ztP 1 = KernelSporSch.Co2M.tP := by
      simp [KernelSporSch.Co2M.ztP]
    exact KernelSporSch.Co2M.unpack_eq KernelSporSch.Co2M.tRep
      (e ▸ CFSG.KS.allN_spec KernelSporSch.Co2M.bind_e 1 (by norm_num))
  have h := KernelSporSch.Co2M.repK_t
  rw [← ht] at h
  exact prep_of_rep h

theorem prep_s
    {j : ℕ} (hj : j < 15) :
    PRep 2300 12 (KernelSporSch.Co2LS.S j) (sTuple.getD j 1) := by
  refine prep_of_rep ?_
  rw [← KernelSporSch.Co2M.s_eq hj]
  exact repTuple_s.rep (by rw [sTuple_length]; exact hj)

theorem prep_u :
    PRep 2300 12 Co2HU.R locU :=
  prep_c (prep_s (by norm_num)) (prep_s (by norm_num))

theorem fourClassesLarge_z :
    FourClassesLarge ↥(centralizerIn co2P locZ) :=
  fourClassesLarge_of_letters (L := Co2HZ.L) prep_z rfl Co2HZ.lettersAll Co2HZ.baseAll

theorem fourClassesLarge_t :
    FourClassesLarge ↥(centralizerIn co2P locT) :=
  fourClassesLarge_of_letters (L := Co2HT.L) prep_t rfl Co2HT.lettersAll Co2HT.baseAll

theorem fourClassesLarge_u :
    FourClassesLarge ↥(centralizerIn co2P locU) :=
  fourClassesLarge_of_letters (L := Co2HU.L) prep_u rfl Co2HU.lettersAll Co2HU.baseAll

theorem ne_of_neqP {P Q : ℕ} {g h : Equiv.Perm (Fin 2300)} (hg : PRep 2300 12 P g)
    (hh : PRep 2300 12 Q h) (hn : Co2H.neqP P Q = true) : g ≠ h := by
  rintro rfl
  have hall : allN 2300 (fun i => Nat.beq (pg 12 (mask 12) P i) (pg 12 (mask 12) Q i)) = true :=
    CFSG.KS.Raw.allN_of_forall fun i hi => by
      have e1 : pg 12 (mask 12) P i = (g ⟨i, hi⟩ : ℕ) := hg ⟨i, hi⟩
      have e2 : pg 12 (mask 12) Q i = (g ⟨i, hi⟩ : ℕ) := hh ⟨i, hi⟩
      rw [e1, e2]
      exact Nat.beq_refl _
  have h2 := notB_true hn
  rw [hall] at h2
  exact Bool.noConfusion h2

theorem sq_of_perm {P : ℕ} (h : Co2H.perm P P = true) : permK P * permK P = 1 := by
  have h1 := prep_of_permOK h
  have hi := CFSG.KC.CommBase.prep_inv_of_permOK h1 h
  exact mul_eq_one_iff_eq_inv.2 (CFSG.KC.CommBase.prep_unique h1 hi)

theorem orderOf_two {g : Equiv.Perm (Fin 2300)} (h : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem hasElemAbelianEight_co2P :
    HasElemAbelianEight ↥co2P := by
  have h := Co2HE.e8All
  simp only [Co2H.e8OK, band, Bool.and_eq_true] at h
  obtain ⟨pa, pb, pd, sa, sb, sd, cab, cad, cbd, na, nb, nd, nab, nad, nbd, ndab⟩ := h
  have ra := prep_of_permOK pa
  have rb := prep_of_permOK pb
  have rd := prep_of_permOK pd
  have a2 := sq_of_perm pa
  have b2 := sq_of_perm pb
  have d2 := sq_of_perm pd
  have hab : Commute (permK (Co2HE.E.getD 0 0)) (permK (Co2HE.E.getD 1 0)) :=
    comm_of_pcomp ra rb cab
  have had : Commute (permK (Co2HE.E.getD 0 0)) (permK (Co2HE.E.getD 2 0)) :=
    comm_of_pcomp ra rd cad
  have hbd : Commute (permK (Co2HE.E.getD 1 0)) (permK (Co2HE.E.getD 2 0)) :=
    comm_of_pcomp rb rd cbd
  have a1 := ne_of_neqP ra prep_one na
  have b1 := ne_of_neqP rb prep_one nb
  have d1 := ne_of_neqP rd prep_one nd
  have eab := ne_of_neqP ra rb nab
  have ead := ne_of_neqP ra rd nad
  have ebd := ne_of_neqP rb rd nbd
  have edab := ne_of_neqP rd (prep_c ra rb) ndab
  set a := permK (Co2HE.E.getD 0 0)
  set b := permK (Co2HE.E.getD 1 0)
  set d := permK (Co2HE.E.getD 2 0)
  have ia : a⁻¹ = a := (eq_inv_of_mul_eq_one_left a2).symm
  have ib : b⁻¹ = b := (eq_inv_of_mul_eq_one_left b2).symm
  have idd : d⁻¹ = d := (eq_inv_of_mul_eq_one_left d2).symm
  have sq2 : ∀ {g h : Equiv.Perm (Fin 2300)}, Commute g h → g * g = 1 → h * h = 1 →
      g * h * (g * h) = 1 := fun c hg hh => by
    rw [← pow_two, c.mul_pow, pow_two, pow_two, hg, hh, one_mul]
  have ne2 : ∀ {g h : Equiv.Perm (Fin 2300)}, h⁻¹ = h → g ≠ h → g * h ≠ 1 := fun ih hne e =>
    hne ((eq_inv_of_mul_eq_one_left e).trans ih)
  have ab2 := sq2 hab a2 b2
  obtain ⟨E, hE, hEe, hEc⟩ := exists_elemAbelian_eight a b d hab had hbd
    (orderOf_two a2 a1) (orderOf_two b2 b1) (orderOf_two d2 d1)
    (orderOf_two ab2 (ne2 ib eab)) (orderOf_two (sq2 had a2 d2) (ne2 idd ead))
    (orderOf_two (sq2 hbd b2 d2) (ne2 idd ebd))
    (orderOf_two (sq2 (had.mul_left hbd) ab2 d2) fun e =>
      edab ((eq_inv_of_mul_eq_one_left e).trans idd).symm)
  refine HasElemAbelianEight.of_le (hE.trans ?_) hEe hEc
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr (mem_P_of_sift ra sa))
    (Subgroup.zpowers_le.mpr (mem_P_of_sift rb sb))) (Subgroup.zpowers_le.mpr (mem_P_of_sift rd sd))

end CertificateChecks.KernelSpor.Co2HG

end
