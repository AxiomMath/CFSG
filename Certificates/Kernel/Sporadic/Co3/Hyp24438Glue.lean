module

public import Certificates.Kernel.Sporadic.Co3.Hyp24438Z
public import Certificates.Kernel.Sporadic.Co3.Hyp24438T
public import Certificates.Kernel.Sporadic.Co3.Hyp24438E8
public import CFSG.Certificates.Kernel.Spor.CommBaseSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.Sporadic.Schreier.Co3Sylow
public import CFSG.Sporadic.Schreier.Co3Centralizers
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.Co3HG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.CommBase
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.EvenSporadicStandard.HypOne

abbrev Sym : Type := Equiv.Perm (Fin 276)

theorem band (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem prep_c {P Q : ℕ} {g h : Sym} (hP : PRep 276 9 P g) (hQ : PRep 276 9 Q h) :
    PRep 276 9 (Co3H.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_one : PRep 276 9 (pidn 276 9) 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_z : PRep 276 9 Co3Z co3Z := by
  have h := rep_co3Z
  rw [CertificateChecks.KernelSpor.Co3Single.z_eq] at h
  exact prep_of_rep h

theorem prep_t : PRep 276 9 Co3Tt co3Tt := by
  have h := rep_co3Tt
  rw [CertificateChecks.KernelSpor.Co3Single.tt_eq] at h
  exact prep_of_rep h

open scoped Classical in
@[expose] noncomputable def permS (P : ℕ) : Sym :=
  if h : ∃ g : Sym, PRep 276 9 P g then h.choose else 1

theorem prep_permS {P Q : ℕ} (h : Co3H.perm P Q = true) : PRep 276 9 P (permS P) := by
  obtain ⟨g, hg, -⟩ := CFSG.KC.EnumSound.permOK_perm h
  have hex : ∃ g : Sym, PRep 276 9 P g := ⟨g, hg⟩
  rw [permS, dif_pos hex]
  exact hex.choose_spec

theorem mem_P {a : ℕ} {g : Sym}
    (hg : PRep 276 9 a g) (hc : Co3H.cn a = true) (hs : Co3H.msift a = true) : g ∈ co3P := by
  unfold Co3H.msift at hs
  rw [band, Bool.and_eq_true] at hs
  exact CFSG.Sporadic.Schreier.Co3.mem_co3P_of_sift (rep_unpack hg)
    (siftK_soundR CertificateChecks.KernelSpor.Co3C.binds CertificateChecks.KernelSpor.Co3C.perm
      CertificateChecks.KernelSpor.Co3C.hl rfl (Nat.eq_of_beq_eq_true hs.1) (range_of_canonK hc)
      hs.2)

theorem comm_of_beq {P X : ℕ} {g x : Sym} (hg : PRep 276 9 P g) (hx : PRep 276 9 X x)
    (h : Nat.beq (Co3H.c P X) (Co3H.c X P) = true) : Commute g x := by
  have h1 := prep_c hg hx
  have h2 := prep_c hx hg
  rw [Nat.eq_of_beq_eq_true h] at h1
  exact prep_unique h1 h2

theorem pow5_eq_one {P : ℕ} {g : Sym} (hP : PRep 276 9 P g)
    (h : Co3H.pow5 P = pidn 276 9) : g ^ 5 = 1 := by
  have h5 : PRep 276 9 (Co3H.pow5 P) (g * (g * (g * (g * g)))) :=
    prep_c hP (prep_c hP (prep_c hP (prep_c hP hP)))
  rw [h] at h5
  have e := prep_unique h5 prep_one
  rw [← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem letOK_facts {L : ℕ → ℕ} {R m : ℕ} (h : Co3H.letOK L R m = true) {z : ℕ} (hz : z < m) :
    Co3H.cn (L z) = true ∧ Co3H.perm (L z) (L (m + 1 + z)) = true ∧
      Co3H.msift (L z) = true ∧ Nat.beq (Co3H.c (L z) R) (Co3H.c R (L z)) = true ∧
      Co3H.pow5 (L z) = pidn 276 9 := by
  have h1 := allN_spec h z hz
  simp only [band, Bool.and_eq_true] at h1
  obtain ⟨a, b, c, d, e⟩ := h1
  exact ⟨a, b, c, d, Nat.eq_of_beq_eq_true e⟩

@[expose] noncomputable def ell (L : ℕ → ℕ) (t : Sym) (m z : ℕ) : Sym :=
  if z < m then permS (L z) else if z = m then t else (permS (L (z - (m + 1))))⁻¹

theorem hL_of_letters {L : ℕ → ℕ} {R m : ℕ} {t : Sym} (hR : PRep 276 9 R t) (hm : L m = R)
    (hl : Co3H.letOK L R m = true) : ∀ z < 2 * m + 1, PRep 276 9 (L z) (ell L t m z) := by
  intro z hz
  unfold ell
  split_ifs with h1 h2
  · exact prep_permS (letOK_facts hl h1).2.1
  · rw [h2, hm]
    exact hR
  · have hi : z - (m + 1) < m := by omega
    have e : m + 1 + (z - (m + 1)) = z := by omega
    have h := prep_inv_of_permOK (prep_permS (letOK_facts hl hi).2.1) (letOK_facts hl hi).2.1
    rw [e] at h
    exact h

theorem hK_of_letters
    {L : ℕ → ℕ} {R m : ℕ} {t : Sym} (hR : PRep 276 9 R t) (hl : Co3H.letOK L R m = true) :
    ∀ z < 2 * m + 1, (ell L t m z ∈ centralizerIn co3P t ∧ ell L t m z ^ 5 = 1) ∨
      ∀ k ∈ centralizerIn co3P t, Commute k (ell L t m z) := by
  have hmem : ∀ z < m, permS (L z) ∈ centralizerIn co3P t ∧ permS (L z) ^ 5 = 1 := by
    intro z hz
    obtain ⟨hc, hp, hs, hct, h5⟩ := letOK_facts hl hz
    have hP := prep_permS hp
    exact ⟨mem_centralizerIn.2 ⟨mem_P hP hc hs, comm_of_beq hP hR hct⟩, pow5_eq_one hP h5⟩
  intro z hz
  unfold ell
  split_ifs with h1 h2
  · exact Or.inl (hmem z h1)
  · exact Or.inr fun k hk => (mem_centralizerIn.1 hk).2
  · have hi : z - (m + 1) < m := by omega
    obtain ⟨h5, h6⟩ := hmem _ hi
    exact Or.inl ⟨(centralizerIn co3P t).inv_mem h5, by rw [inv_pow, h6, inv_one]⟩

theorem fourClassesLarge_base
    {L : ℕ → ℕ} {R m : ℕ} {t : Sym} (hR : PRep 276 9 R t) (hm : L m = R)
    (hl : Co3H.letOK L R m = true) {B : List BaseRec} {PF ZF DF : ℕ}
    (hb : commBaseOK 276 9 (mask 9) L (2 * m + 1) B PF ZF DF = true) :
    FourClassesLarge ↥(centralizerIn co3P t) :=
  fourClassesLarge_of_commBase _ (hL_of_letters hR hm hl) (hK_of_letters hR hl) hb

theorem fourClassesLarge_z :
    FourClassesLarge ↥(centralizerIn co3P co3Z) :=
  fourClassesLarge_base (L := Co3HZ.L) prep_z rfl Co3HZ.lettersAll Co3HZ.baseAll

theorem fourClassesLarge_t :
    FourClassesLarge ↥(centralizerIn co3P co3Tt) :=
  fourClassesLarge_base (L := Co3HT.L) prep_t rfl Co3HT.lettersAll Co3HT.baseAll

theorem ne_of_neqP {P Q : ℕ} {g h : Sym} (hg : PRep 276 9 P g) (hh : PRep 276 9 Q h)
    (hn : Co3H.neqP P Q = true) : g ≠ h := by
  rintro rfl
  have hall : allN 276 (fun i => Nat.beq (pg 9 (mask 9) P i) (pg 9 (mask 9) Q i)) = true :=
    allN_of_forall fun i hi => by
      have e1 : pg 9 (mask 9) P i = (g ⟨i, hi⟩ : ℕ) := hg ⟨i, hi⟩
      have e2 : pg 9 (mask 9) Q i = (g ⟨i, hi⟩ : ℕ) := hh ⟨i, hi⟩
      rw [e1, e2]
      exact Nat.beq_refl _
  have h2 := notB_true hn
  rw [hall] at h2
  exact Bool.noConfusion h2

theorem sq_of_perm {P : ℕ} (h : Co3H.perm P P = true) : permS P * permS P = 1 := by
  have h1 := prep_permS h
  have hi := prep_inv_of_permOK h1 h
  exact mul_eq_one_iff_eq_inv.2 (prep_unique h1 hi)

theorem orderOf_two {g : Sym} (h : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem hasElemAbelianEight_co3P :
    HasElemAbelianEight ↥co3P := by
  have h := Co3HE.e8All
  simp only [Co3H.e8OK, band, Bool.and_eq_true] at h
  obtain ⟨ca, cb, cd, pa, pb, pd, sa, sb, sd, cab, cad, cbd, na, nb, nd, nab, nad, nbd, ndab⟩ := h
  have ra := prep_permS pa
  have rb := prep_permS pb
  have rd := prep_permS pd
  have a2 := sq_of_perm pa
  have b2 := sq_of_perm pb
  have d2 := sq_of_perm pd
  have hab := comm_of_beq ra rb cab
  have had := comm_of_beq ra rd cad
  have hbd := comm_of_beq rb rd cbd
  have a1 := ne_of_neqP ra prep_one na
  have b1 := ne_of_neqP rb prep_one nb
  have d1 := ne_of_neqP rd prep_one nd
  have eab := ne_of_neqP ra rb nab
  have ead := ne_of_neqP ra rd nad
  have ebd := ne_of_neqP rb rd nbd
  have edab := ne_of_neqP rd (prep_c ra rb) ndab
  have ma := mem_P ra ca sa
  have mb := mem_P rb cb sb
  have md := mem_P rd cd sd
  set a := permS (Co3HE.E.getD 0 0)
  set b := permS (Co3HE.E.getD 1 0)
  set d := permS (Co3HE.E.getD 2 0)
  have ib : b⁻¹ = b := (eq_inv_of_mul_eq_one_left b2).symm
  have idd : d⁻¹ = d := (eq_inv_of_mul_eq_one_left d2).symm
  have sq2 : ∀ {g h : Sym}, Commute g h → g * g = 1 → h * h = 1 → g * h * (g * h) = 1 :=
    fun c hg hh => by rw [← pow_two, c.mul_pow, pow_two, pow_two, hg, hh, one_mul]
  have ne2 : ∀ {g h : Sym}, h⁻¹ = h → g ≠ h → g * h ≠ 1 := fun ih hne e =>
    hne ((eq_inv_of_mul_eq_one_left e).trans ih)
  have ab2 := sq2 hab a2 b2
  obtain ⟨E, hE, hEe, hEc⟩ := exists_elemAbelian_eight a b d hab had hbd
    (orderOf_two a2 a1) (orderOf_two b2 b1) (orderOf_two d2 d1)
    (orderOf_two ab2 (ne2 ib eab)) (orderOf_two (sq2 had a2 d2) (ne2 idd ead))
    (orderOf_two (sq2 hbd b2 d2) (ne2 idd ebd))
    (orderOf_two (sq2 (had.mul_left hbd) ab2 d2) fun e =>
      edab ((eq_inv_of_mul_eq_one_left e).trans idd).symm)
  refine HasElemAbelianEight.of_le (hE.trans ?_) hEe hEc
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr ma) (Subgroup.zpowers_le.mpr mb))
    (Subgroup.zpowers_le.mpr md)

end CertificateChecks.KernelSpor.Co3HG

end
