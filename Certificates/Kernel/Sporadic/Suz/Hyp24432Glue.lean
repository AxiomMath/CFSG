module

public import Certificates.Kernel.Sporadic.Suz.Hyp24432T0
public import Certificates.Kernel.Sporadic.Suz.Hyp24432T1
public import Certificates.Kernel.Sporadic.Suz.Hyp24432T2
public import Certificates.Kernel.Sporadic.Suz.Hyp24432T3
public import Certificates.Kernel.Sporadic.Suz.Hyp24432E8
public import CFSG.Certificates.Kernel.Spor.CommEnumSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
public import CFSG.Sporadic.SuzOddCore.SmallChain
public import CFSG.Sporadic.SuzOddCore.InvPerms
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.SuzHG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.CommBase
open CFSG.KC.CommEnum CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.HypOne

abbrev Sym : Type := Equiv.Perm (Fin 1782)

theorem band (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem prep_c {P Q : ℕ} {g h : Sym} (hP : PRep 1782 11 P g) (hQ : PRep 1782 11 Q h) :
    PRep 1782 11 (SuzH.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_one : PRep 1782 11 (pidn 1782 11) 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_tP {i : ℕ} (hi : i < 4) :
    PRep 1782 11 (SuzTP i) (suzInv i) := by
  have h := rep_suzInv hi
  rw [(OddCore.rep_facts hi).1] at h
  exact prep_of_rep h

theorem prep_V : PRep 1782 11 Suz2306.V suzV := by
  have h := rep_v
  rw [Suz2306.vArr_eq] at h
  exact prep_of_rep h

theorem suzInv_sq {i : ℕ} (hi : i < 4) :
    suzInv i * suzInv i = 1 := by
  have h := allN_spec OddCore.reps i hi
  unfold OddCore.repK at h
  rw [OddCore.strictB_app] at h
  simp only [bAnd_iff] at h
  have hs : bAnd(canonK 1782 11 (mask 11) (1782 * 11) (SuzTP i),
      Nat.beq (pcomp 1782 11 (mask 11) (SuzTP i) (SuzTP i)) (pidn 1782 11)) = true := h.2.2.1
  rw [bAnd_iff] at hs
  have h2 := prep_c (prep_tP hi) (prep_tP hi)
  rw [SuzH.c, Nat.eq_of_beq_eq_true hs.2] at h2
  exact prep_unique h2 prep_one

open scoped Classical in
@[expose] noncomputable def permS (P : ℕ) : Sym :=
  if h : ∃ g : Sym, PRep 1782 11 P g then h.choose else 1

theorem prep_permS {P Q : ℕ} (h : SuzH.perm P Q = true) : PRep 1782 11 P (permS P) := by
  obtain ⟨g, hg, -⟩ := CFSG.KC.EnumSound.permOK_perm h
  have hex : ∃ g : Sym, PRep 1782 11 P g := ⟨g, hg⟩
  rw [permS, dif_pos hex]
  exact hex.choose_spec

theorem mem_M {a : ℕ} {g : Sym}
    (hg : PRep 1782 11 a g) (hc : SuzH.cn a = true) (hs : OddCore.msift a = true) : g ∈ suzM := by
  refine (inM_iff (rep_unpack hg)).1 ?_
  rw [OddCore.inM_eq rfl hc]
  exact hs

theorem not_mem_M {a : ℕ} {g : Sym}
    (hg : PRep 1782 11 a g) (hc : SuzH.cn a = true) (hs : OddCore.msift a = false) :
    g ∉ suzM := by
  intro hm
  have h := (inM_iff (rep_unpack hg)).2 hm
  rw [OddCore.inM_eq rfl hc, hs] at h
  exact Bool.false_ne_true h

theorem not_mem_T {a : ℕ} {g : Sym}
    (hg : PRep 1782 11 a g) (hc : SuzH.cn a = true) (hs : OddCore.msift a = false)
    (hsv : OddCore.msift (SuzH.c Suz2306.V a) = false) : g ∉ suzT := by
  rw [mem_suzT_iff]
  rintro (h | h)
  · exact not_mem_M hg hc hs h
  · exact not_mem_M (prep_c prep_V hg) (CFSG.KC.BfsPin.canonK_pcomp OddCore.canonV hc) hsv h

theorem comm_of_beq {P X : ℕ} {g x : Sym} (hg : PRep 1782 11 P g) (hx : PRep 1782 11 X x)
    (h : Nat.beq (SuzH.c P X) (SuzH.c X P) = true) : Commute g x := by
  have h1 := prep_c hg hx
  have h2 := prep_c hx hg
  rw [Nat.eq_of_beq_eq_true h] at h1
  exact prep_unique h1 h2

theorem pow5_eq_one {P : ℕ} {g : Sym} (hP : PRep 1782 11 P g)
    (h : SuzH.pow5 P = pidn 1782 11) : g ^ 5 = 1 := by
  have h5 : PRep 1782 11 (SuzH.pow5 P) (g * (g * (g * (g * g)))) :=
    prep_c hP (prep_c hP (prep_c hP (prep_c hP hP)))
  rw [h] at h5
  have e := prep_unique h5 prep_one
  rw [← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem letOK_facts {L : ℕ → ℕ} {R m : ℕ} (h : SuzH.letOK L R m = true) {z : ℕ} (hz : z < m) :
    SuzH.cn (L z) = true ∧ SuzH.perm (L z) (L (m + 1 + z)) = true ∧
      OddCore.msift (L z) = true ∧ Nat.beq (SuzH.c (L z) R) (SuzH.c R (L z)) = true ∧
      SuzH.pow5 (L z) = pidn 1782 11 := by
  have h1 := allN_spec h z hz
  simp only [band, Bool.and_eq_true] at h1
  obtain ⟨a, b, c, d, e⟩ := h1
  exact ⟨a, b, c, d, Nat.eq_of_beq_eq_true e⟩

@[expose] noncomputable def ell (L : ℕ → ℕ) (t : Sym) (m z : ℕ) : Sym :=
  if z < m then permS (L z) else if z = m then t else (permS (L (z - (m + 1))))⁻¹

theorem hL_of_letters {L : ℕ → ℕ} {R m : ℕ} {t : Sym} (hR : PRep 1782 11 R t) (hm : L m = R)
    (hl : SuzH.letOK L R m = true) : ∀ z < 2 * m + 1, PRep 1782 11 (L z) (ell L t m z) := by
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
    {H : Subgroup Sym} (hH : suzM ≤ H) {L : ℕ → ℕ} {R m : ℕ} {t : Sym}
    (hR : PRep 1782 11 R t) (hl : SuzH.letOK L R m = true) :
    ∀ z < 2 * m + 1, (ell L t m z ∈ centralizerIn H t ∧ ell L t m z ^ 5 = 1) ∨
      ∀ k ∈ centralizerIn H t, Commute k (ell L t m z) := by
  have hmem : ∀ z < m, permS (L z) ∈ centralizerIn H t ∧ permS (L z) ^ 5 = 1 := by
    intro z hz
    obtain ⟨hc, hp, hs, hct, h5⟩ := letOK_facts hl hz
    have hP := prep_permS hp
    exact ⟨mem_centralizerIn.2 ⟨hH (mem_M hP hc hs), comm_of_beq hP hR hct⟩, pow5_eq_one hP h5⟩
  intro z hz
  unfold ell
  split_ifs with h1 h2
  · exact Or.inl (hmem z h1)
  · exact Or.inr fun k hk => (mem_centralizerIn.1 hk).2
  · have hi : z - (m + 1) < m := by omega
    obtain ⟨h5, h6⟩ := hmem _ hi
    exact Or.inl ⟨(centralizerIn H t).inv_mem h5, by rw [inv_pow, h6, inv_one]⟩

theorem fourClassesLarge_base
    {H : Subgroup Sym} (hH : suzM ≤ H) {L : ℕ → ℕ} {R m : ℕ} {t : Sym}
    (hR : PRep 1782 11 R t) (hm : L m = R) (hl : SuzH.letOK L R m = true) {B : List BaseRec}
    {PF ZF DF : ℕ} (hb : commBaseOK 1782 11 (mask 11) L (2 * m + 1) B PF ZF DF = true) :
    FourClassesLarge ↥(centralizerIn H t) :=
  fourClassesLarge_of_commBase _ (hL_of_letters hR hm hl) (hK_of_letters hH hR hl) hb

theorem fourClassesLarge_enum
    {H : Subgroup Sym} (hH : suzM ≤ H) (hHT : H ≤ suzT) {L : ℕ → ℕ} {R m : ℕ} {t : Sym}
    (hR : PRep 1782 11 R t) (hm : L m = R) (hl : SuzH.letOK L R m = true) {Y YI : ℕ → ℕ}
    {nY : ℕ} (hy : SuzH.yOK Y YI L m nY = true) {RR : List RepRec} {O PF ZF DF : ℕ}
    (he : enumOK 1782 11 (mask 11) L (2 * m + 1) RR O PF ZF DF Y nY = true) :
    FourClassesLarge ↥(centralizerIn H t) := by
  have hL := hL_of_letters hR hm hl
  have hyk : ∀ k < nY, SuzH.cn (Y k) = true ∧ SuzH.perm (Y k) (YI k) = true ∧
      OddCore.msift (Y k) = false ∧ OddCore.msift (SuzH.c Suz2306.V (Y k)) = false ∧
      ∀ z < m + 1, Nat.beq (SuzH.c (Y k) (L z)) (SuzH.c (L z) (Y k)) = true := by
    intro k hk
    have h1 := allN_spec hy k hk
    simp only [band, Bool.and_eq_true] at h1
    obtain ⟨a, b, c, d, e⟩ := h1
    exact ⟨a, b, notB_true c, notB_true d, fun z hz => allN_spec e z hz⟩
  have hY : ∀ k < nY, PRep 1782 11 (Y k) (permS (Y k)) := fun k hk =>
    prep_permS (hyk k hk).2.1
  have hYc : ∀ k < nY, ∀ z < 2 * m + 1, Commute (permS (Y k)) (ell L t m z) := by
    intro k hk z hz
    by_cases hzm : z < m + 1
    · exact comm_of_beq (hY k hk) (hL z hz) ((hyk k hk).2.2.2.2 z hzm)
    · have hi : z - (m + 1) < m + 1 := by omega
      have hc := comm_of_beq (hY k hk) (hL _ (by omega)) ((hyk k hk).2.2.2.2 _ hi)
      have e : ell L t m z = (ell L t m (z - (m + 1)))⁻¹ := by
        unfold ell
        have h1 : ¬ z < m := by omega
        have h2 : ¬ z = m := by omega
        have h3 : z - (m + 1) < m := by omega
        rw [if_neg h1, if_neg h2, if_pos h3]
      rw [e]
      exact hc.inv_right
  refine fourClassesLarge_of_commEnum _ hL (hK_of_letters hH hR hl) hY hYc (fun k hk hm' => ?_) he
  obtain ⟨hc, -, hs, hsv, -⟩ := hyk k hk
  exact not_mem_T (hY k hk) hc hs hsv (hHT (mem_centralizerIn.1 hm').1)

theorem fourClassesLarge_M0 :
    FourClassesLarge ↥(centralizerIn suzM (suzInv 0)) :=
  fourClassesLarge_enum le_rfl suzM_le_suzT (L := SuzH0.L) (prep_tP (by norm_num)) rfl
    SuzH0.lettersAll SuzH0.yAll SuzH0.enumAll

theorem fourClassesLarge_T0 :
    FourClassesLarge ↥(centralizerIn suzT (suzInv 0)) :=
  fourClassesLarge_enum suzM_le_suzT le_rfl (L := SuzH0.L) (prep_tP (by norm_num)) rfl
    SuzH0.lettersAll SuzH0.yAll SuzH0.enumAll

theorem fourClassesLarge_M1 :
    FourClassesLarge ↥(centralizerIn suzM (suzInv 1)) :=
  fourClassesLarge_base le_rfl (L := SuzH1.L) (prep_tP (by norm_num)) rfl SuzH1.lettersAll
    SuzH1.baseAll

theorem fourClassesLarge_T1 :
    FourClassesLarge ↥(centralizerIn suzT (suzInv 1)) :=
  fourClassesLarge_base suzM_le_suzT (L := SuzH1.L) (prep_tP (by norm_num)) rfl
    SuzH1.lettersAll SuzH1.baseAll

theorem fourClassesLarge_T2 :
    FourClassesLarge ↥(centralizerIn suzT (suzInv 2)) :=
  fourClassesLarge_base suzM_le_suzT (L := SuzH2.L) (prep_tP (by norm_num)) rfl
    SuzH2.lettersAll SuzH2.baseAll

theorem fourClassesLarge_T3 :
    FourClassesLarge ↥(centralizerIn suzT (suzInv 3)) :=
  fourClassesLarge_base suzM_le_suzT (L := SuzH3.L) (prep_tP (by norm_num)) rfl
    SuzH3.lettersAll SuzH3.baseAll

theorem fourClassesLarge_T :
    ∀ i < 4, FourClassesLarge ↥(centralizerIn suzT (suzInv i)) := by
  intro i hi
  interval_cases i
  · exact fourClassesLarge_T0
  · exact fourClassesLarge_T1
  · exact fourClassesLarge_T2
  · exact fourClassesLarge_T3

theorem ne_of_neqP {P Q : ℕ} {g h : Sym} (hg : PRep 1782 11 P g) (hh : PRep 1782 11 Q h)
    (hn : SuzH.neqP P Q = true) : g ≠ h := by
  rintro rfl
  have hall : allN 1782 (fun i => Nat.beq (pg 11 (mask 11) P i) (pg 11 (mask 11) Q i)) = true :=
    allN_of_forall fun i hi => by
      have e1 : pg 11 (mask 11) P i = (g ⟨i, hi⟩ : ℕ) := hg ⟨i, hi⟩
      have e2 : pg 11 (mask 11) Q i = (g ⟨i, hi⟩ : ℕ) := hh ⟨i, hi⟩
      rw [e1, e2]
      exact Nat.beq_refl _
  have h2 := notB_true hn
  rw [hall] at h2
  exact Bool.noConfusion h2

theorem sq_of_perm {P : ℕ} (h : SuzH.perm P P = true) : permS P * permS P = 1 := by
  have h1 := prep_permS h
  have hi := prep_inv_of_permOK h1 h
  exact mul_eq_one_iff_eq_inv.2 (prep_unique h1 hi)

theorem orderOf_two {g : Sym} (h : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem hasElemAbelianEight_suzM :
    HasElemAbelianEight ↥suzM := by
  have h := SuzHE.e8All
  simp only [SuzH.e8OK, band, Bool.and_eq_true] at h
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
  have ma := mem_M ra ca sa
  have mb := mem_M rb cb sb
  have md := mem_M rd cd sd
  set a := permS (SuzHE.E.getD 0 0)
  set b := permS (SuzHE.E.getD 1 0)
  set d := permS (SuzHE.E.getD 2 0)
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

theorem fours_of_ok {l li : ℕ}
    {i : ℕ} (hi : i < 4) (h : SuzH.foursOK l li (SuzTP i) = true) :
    ∃ g ∈ suzM, orderOf (g * suzInv i * g⁻¹ * (suzInv i)⁻¹) = 2 := by
  unfold SuzH.foursOK at h
  rw [OddCore.strictB_app] at h
  simp only [band, Bool.and_eq_true] at h
  obtain ⟨hc, hp, hs, h2, hn⟩ := h
  have rl := prep_permS hp
  have rli := prep_inv_of_permOK rl hp
  have ht := prep_tP hi
  have hti : (suzInv i)⁻¹ = suzInv i := (eq_inv_of_mul_eq_one_left (suzInv_sq hi)).symm
  have rC : PRep 1782 11 (SuzH.c (SuzH.c (SuzH.c l (SuzTP i)) li) (SuzTP i))
      (permS l * suzInv i * (permS l)⁻¹ * (suzInv i)⁻¹) := by
    rw [hti]
    exact prep_c (prep_c (prep_c rl ht) rli) ht
  refine ⟨permS l, mem_M rl hc hs, orderOf_two ?_ (ne_of_neqP rC prep_one hn)⟩
  have h3 := prep_c rC rC
  rw [Nat.eq_of_beq_eq_true h2] at h3
  exact prep_unique h3 prep_one

theorem fours_wit :
    ∀ i ∈ [2, 3], ∃ l ∈ suzM, orderOf (l * suzInv i * l⁻¹ * (suzInv i)⁻¹) = 2 := by
  have h := SuzHE.foursAll
  rw [band, Bool.and_eq_true] at h
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact fours_of_ok (by norm_num) h.1
  · exact fours_of_ok (by norm_num) h.2

end CertificateChecks.KernelSpor.SuzHG

end
