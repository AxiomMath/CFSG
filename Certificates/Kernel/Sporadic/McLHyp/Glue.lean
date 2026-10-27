module

public import Certificates.Kernel.Sporadic.McLHyp.T0
public import Certificates.Kernel.Sporadic.McLHyp.T1
public import Certificates.Kernel.Sporadic.McLHyp.E8
public import Certificates.Kernel.Census.McLN
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Spor.CommBaseSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.RankThree.PartTwo.KFacts.K426McL
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.McLInputs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.McLHG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.CommBase
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.EvenSporadicStandard.HypOne

abbrev Sym : Type := Equiv.Perm (Fin 275)

theorem band (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem prep_c {P Q : ℕ} {g h : Sym} (hP : PRep 275 9 P g) (hQ : PRep 275 9 Q h) :
    PRep 275 9 (McLH.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_one : PRep 275 9 (pidn 275 9) 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_root {k RI : ℕ} (hk : k < 22)
    (h : McLH.rootOK (CertificateChecks.KernelLC.McLC.MC.F k) RI = true) :
    PRep 275 9 (CertificateChecks.KernelLC.McLC.MC.F k) (tp 275 (mclCentTbl k)) := by
  unfold McLH.rootOK at h
  simp only [band, Bool.and_eq_true] at h
  obtain ⟨hc, -, hie⟩ := h
  have heq : mclCentTbl k =
      CFSG.KS.MulH.tabT (unpack 275 9 (CertificateChecks.KernelLC.McLC.MC.F k)) := by
    rw [← CertificateChecks.KernelLC.McLC.natArr_cent k hk, CFSG.KS.MulH.tabT_natArr]
  have hp : permOK 275 (mclCentTbl k) = true := by
    rw [heq]
    exact CFSG.KS.MulH.permOK_unpack hc hie
  have hr := co2Rep_natArr_iff.2 (rep_tp hp)
  rw [CertificateChecks.KernelLC.McLC.natArr_cent k hk] at hr
  exact prep_of_rep hr

theorem roots : McLH.rootOK (CertificateChecks.KernelLC.McLC.MC.F 4) McLHE.RI0 = true ∧
    McLH.rootOK (CertificateChecks.KernelLC.McLC.MC.F 17) McLHE.RI1 = true := by
  have h := McLHE.rootsAll
  rw [band, Bool.and_eq_true] at h
  exact h

theorem prep_t0 : PRep 275 9 (CertificateChecks.KernelLC.McLC.MC.F 4) (tp 275 McL.t0) :=
  prep_root (by norm_num) roots.1

theorem prep_t1 : PRep 275 9 (CertificateChecks.KernelLC.McLC.MC.F 17) (tp 275 McL.t1) :=
  prep_root (by norm_num) roots.2

open scoped Classical in
@[expose] noncomputable def permS (P : ℕ) : Sym :=
  if h : ∃ g : Sym, PRep 275 9 P g then h.choose else 1

theorem prep_permS {P Q : ℕ} (h : McLH.perm P Q = true) : PRep 275 9 P (permS P) := by
  obtain ⟨g, hg, -⟩ := CFSG.KC.EnumSound.permOK_perm h
  have hex : ∃ g : Sym, PRep 275 9 P g := ⟨g, hg⟩
  rw [permS, dif_pos hex]
  exact hex.choose_spec

theorem mem_P {a : ℕ} {g : Sym}
    (hg : PRep 275 9 a g) (hc : McLH.cn a = true) (hs : McLH.msift a = true) : g ∈ mclP := by
  obtain ⟨-, -, h3, -⟩ := CFSG.KS.PF.canon_facts hc
  exact CFSG.RankThree.PartTwo.KFacts.K426.mem_mclP_of_sift (rep_unpack hg)
    (siftK_soundR CertificateChecks.KernelCensus.McLK.binds
      CertificateChecks.KernelCensus.McLK.hperm CertificateChecks.KernelCensus.McLC.hl rfl h3
      (range_of_canonK hc) hs)

theorem comm_of_beq {P X : ℕ} {g x : Sym} (hg : PRep 275 9 P g) (hx : PRep 275 9 X x)
    (h : Nat.beq (McLH.c P X) (McLH.c X P) = true) : Commute g x := by
  have h1 := prep_c hg hx
  have h2 := prep_c hx hg
  rw [Nat.eq_of_beq_eq_true h] at h1
  exact prep_unique h1 h2

theorem pow5_eq_one {P : ℕ} {g : Sym} (hP : PRep 275 9 P g)
    (h : McLH.pow5 P = pidn 275 9) : g ^ 5 = 1 := by
  have h5 : PRep 275 9 (McLH.pow5 P) (g * (g * (g * (g * g)))) :=
    prep_c hP (prep_c hP (prep_c hP (prep_c hP hP)))
  rw [h] at h5
  have e := prep_unique h5 prep_one
  rw [← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem letOK_facts {L : ℕ → ℕ} {R m : ℕ} (h : McLH.letOK L R m = true) {z : ℕ} (hz : z < m) :
    McLH.cn (L z) = true ∧ McLH.perm (L z) (L (m + 1 + z)) = true ∧
      McLH.msift (L z) = true ∧ Nat.beq (McLH.c (L z) R) (McLH.c R (L z)) = true ∧
      McLH.pow5 (L z) = pidn 275 9 := by
  have h1 := allN_spec h z hz
  simp only [band, Bool.and_eq_true] at h1
  obtain ⟨a, b, c, d, e⟩ := h1
  exact ⟨a, b, c, d, Nat.eq_of_beq_eq_true e⟩

@[expose] noncomputable def ell (L : ℕ → ℕ) (t : Sym) (m z : ℕ) : Sym :=
  if z < m then permS (L z) else if z = m then t else (permS (L (z - (m + 1))))⁻¹

theorem hL_of_letters {L : ℕ → ℕ} {R m : ℕ} {t : Sym} (hR : PRep 275 9 R t) (hm : L m = R)
    (hl : McLH.letOK L R m = true) : ∀ z < 2 * m + 1, PRep 275 9 (L z) (ell L t m z) := by
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
    {H : Subgroup Sym} (hH : mclP ≤ H) {L : ℕ → ℕ} {R m : ℕ} {t : Sym}
    (hR : PRep 275 9 R t) (hl : McLH.letOK L R m = true) :
    ∀ z < 2 * m + 1, (ell L t m z ∈ centralizerIn H t ∧ ell L t m z ^ 5 = 1) ∨
      ∀ k ∈ centralizerIn H t, Commute k (ell L t m z) := by
  have hmem : ∀ z < m, permS (L z) ∈ centralizerIn H t ∧ permS (L z) ^ 5 = 1 := by
    intro z hz
    obtain ⟨hc, hp, hs, hct, h5⟩ := letOK_facts hl hz
    have hP := prep_permS hp
    exact ⟨mem_centralizerIn.2 ⟨hH (mem_P hP hc hs), comm_of_beq hP hR hct⟩, pow5_eq_one hP h5⟩
  intro z hz
  unfold ell
  split_ifs with h1 h2
  · exact Or.inl (hmem z h1)
  · exact Or.inr fun k hk => (mem_centralizerIn.1 hk).2
  · have hi : z - (m + 1) < m := by omega
    obtain ⟨h5, h6⟩ := hmem _ hi
    exact Or.inl ⟨(centralizerIn H t).inv_mem h5, by rw [inv_pow, h6, inv_one]⟩

theorem fourClassesLarge_base
    {H : Subgroup Sym} (hH : mclP ≤ H) {L : ℕ → ℕ} {R m : ℕ} {t : Sym}
    (hR : PRep 275 9 R t) (hm : L m = R) (hl : McLH.letOK L R m = true) {B : List BaseRec}
    {PF ZF DF : ℕ} (hb : commBaseOK 275 9 (mask 9) L (2 * m + 1) B PF ZF DF = true) :
    FourClassesLarge ↥(centralizerIn H t) :=
  fourClassesLarge_of_commBase _ (hL_of_letters hR hm hl) (hK_of_letters hH hR hl) hb

theorem fourClassesLarge_P0 :
    FourClassesLarge ↥(centralizerIn mclP (tp 275 McL.t0)) :=
  fourClassesLarge_base le_rfl (L := McLH0.L) prep_t0 rfl McLH0.lettersAll McLH0.baseAll

theorem fourClassesLarge_R0 :
    FourClassesLarge ↥(centralizerIn mclR (tp 275 McL.t0)) :=
  fourClassesLarge_base le_sup_left (L := McLH0.L) prep_t0 rfl McLH0.lettersAll McLH0.baseAll

theorem fourClassesLarge_R1 :
    FourClassesLarge ↥(centralizerIn mclR (tp 275 McL.t1)) :=
  fourClassesLarge_base le_sup_left (L := McLH1.L) prep_t1 rfl McLH1.lettersAll McLH1.baseAll

theorem ne_of_neqP {P Q : ℕ} {g h : Sym} (hg : PRep 275 9 P g) (hh : PRep 275 9 Q h)
    (hn : McLH.neqP P Q = true) : g ≠ h := by
  rintro rfl
  have hall : allN 275 (fun i => Nat.beq (pg 9 (mask 9) P i) (pg 9 (mask 9) Q i)) = true :=
    allN_of_forall fun i hi => by
      have e1 : pg 9 (mask 9) P i = (g ⟨i, hi⟩ : ℕ) := hg ⟨i, hi⟩
      have e2 : pg 9 (mask 9) Q i = (g ⟨i, hi⟩ : ℕ) := hh ⟨i, hi⟩
      rw [e1, e2]
      exact Nat.beq_refl _
  have h2 := notB_true hn
  rw [hall] at h2
  exact Bool.noConfusion h2

theorem sq_of_perm {P : ℕ} (h : McLH.perm P P = true) : permS P * permS P = 1 := by
  have h1 := prep_permS h
  have hi := prep_inv_of_permOK h1 h
  exact mul_eq_one_iff_eq_inv.2 (prep_unique h1 hi)

theorem orderOf_two {g : Sym} (h : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem hasElemAbelianEight_mclP :
    HasElemAbelianEight ↥mclP := by
  have h := McLHE.e8All
  simp only [McLH.e8OK, band, Bool.and_eq_true] at h
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
  set a := permS (McLHE.E.getD 0 0)
  set b := permS (McLHE.E.getD 1 0)
  set d := permS (McLHE.E.getD 2 0)
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

theorem fours_wit :
    ∃ l ∈ mclP, orderOf (l * tp 275 McL.t1 * l⁻¹ * (tp 275 McL.t1)⁻¹) = 2 := by
  have h := McLHE.foursAll
  unfold McLH.foursOK at h
  rw [strictB_app] at h
  simp only [band, Bool.and_eq_true] at h
  obtain ⟨ht2, hc, hp, hs, h2, hn⟩ := h
  have rl := prep_permS hp
  have rli := prep_inv_of_permOK rl hp
  have ht := prep_t1
  have htt : tp 275 McL.t1 * tp 275 McL.t1 = 1 := by
    have e := prep_c ht ht
    rw [Nat.eq_of_beq_eq_true ht2] at e
    exact prep_unique e prep_one
  have hti : (tp 275 McL.t1)⁻¹ = tp 275 McL.t1 := (eq_inv_of_mul_eq_one_left htt).symm
  have rC : PRep 275 9 (McLH.c (McLH.c (McLH.c McLHE.W (CertificateChecks.KernelLC.McLC.MC.F 17))
      McLHE.WI) (CertificateChecks.KernelLC.McLC.MC.F 17))
      (permS McLHE.W * tp 275 McL.t1 * (permS McLHE.W)⁻¹ * (tp 275 McL.t1)⁻¹) := by
    rw [hti]
    exact prep_c (prep_c (prep_c rl ht) rli) ht
  refine ⟨permS McLHE.W, mem_P rl hc hs, orderOf_two ?_ (ne_of_neqP rC prep_one hn)⟩
  have h3 := prep_c rC rC
  rw [Nat.eq_of_beq_eq_true h2] at h3
  exact prep_unique h3 prep_one

end CertificateChecks.KernelSpor.McLHG

end
