module

public import Certificates.Kernel.Sp6Insp443.Orb
public import Certificates.Kernel.Sp6Insp443.CentGlue
public import CFSG.Certificates.Kernel.Sp6Insp443.OrbSound
public import CFSG.Certificates.Kernel.KGC31PPow
public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6Model
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.PcompFacts
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermSix
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KS.Raw.Orb hiding tabP strictB_eq
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I CFSG.KC.KGC31P
  CFSG.KC.BfsPin CFSG.KC.Child3 CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.EvenSmallLie.Sp6
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.Quasithin.KGC31.Native CertificateChecks.KernelLC.Sp6J
  CFSG.KS.SporSch.MOC

theorem exists_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr hs, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hab⟩ := exists_of_forall₂ hs a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

#kc_forall_chunks orbAll (fun k => ch725105o k = true) 21 CertificateChecks.KernelS6I.ch725105o 1

theorem hsz36 : szOK 36 6 = true := by decide +kernel

theorem hN : RX.N = 5103 := by decide +kernel

theorem orbT_all : ∀ j < RX.N, ch725105t j = true := by
  intro j hj
  rw [hN] at hj
  have hk : j / 243 < 21 := by omega
  have h := CFSG.KS.allBlk_spec (orbAll (j / 243) hk) (j % 243)
    (Nat.mod_lt _ (by norm_num))
  have e : (Nat.mul 243 (j / 243)).add (j % 243) = j := Nat.div_add_mod j 243
  rwa [e] at h

theorem inv_facts {j : Nat} (hj : j < RX.N) :
    PP 36 6 (RX.E j) ∧ porbOne 36 6 5 O.X5 O.C5 (RX.E j) = true ∧
      porbOne 36 6 7 O.X7 O.C7 (RX.E j) = true := by
  have h := orbT_all j hj
  unfold ch725105t at h
  rw [CFSG.KS.Raw.strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨CFSG.KC.HeGlueK.PP_of_permOK2 hsz36 h.1, h.2.1, h.2.2⟩

theorem rec_facts {j : Nat} (hj : j < RX.N) :
    RepFacts 36 6 XQ.S XQ.SI 2 RX.CS RX.OFF RX.CI RX.E RX.P RX.L RX.K RX.S RX.SI RX.N 4000 j :=
  repK_facts (allN_iff.1 kRX j hj)

theorem hpos : ∀ c ∈ RX.CS, 0 < c := by
  rw [kCSX]
  decide

theorem hlen : RX.CS.length = 4 := by rw [kCSX]; rfl

theorem rec_conj {i : Nat} (hi : i < 4) : ∀ k < lget RX.CS i,
    ∃ c ∈ sp6Q.originalSubgroup,
      PRep 36 6 (RX.E (lget RX.OFF i + k)) (c * sp6InvReps.getD i 1 * c⁻¹) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨1, one_mem _, ?_⟩
      rw [one_mul, inv_one, mul_one, Nat.add_zero]
      exact prep_of_imageList (rep_img i hi)
    · obtain ⟨hjN, hci⟩ := ci_eq kOffX (fun j hj => allN_iff.1 kRX j hj) (hlen ▸ hi) hk
      have hkj : lget RX.OFF i + k - lget RX.OFF (RX.CI (lget RX.OFF i + k)) = k := by
        rw [hci]
        omega
      obtain ⟨hP, hL, hcj⟩ := (rec_facts hjN).tree (by rw [hkj]; omega)
      rw [hkj] at hP
      rw [hci] at hcj
      obtain ⟨c, hc, hr⟩ := ih _ hP (by omega)
      have hl : RX.L (lget RX.OFF i + k) < 2 := hL
      refine ⟨sp6Gens.getD (RX.L (lget RX.OFF i + k)) 1 * c,
        mul_mem (genMem _ hl) hc, ?_⟩
      rw [← hcj]
      have e : sp6Gens.getD (RX.L (lget RX.OFF i + k)) 1 * c * sp6InvReps.getD i 1 *
          (sp6Gens.getD (RX.L (lget RX.OFF i + k)) 1 * c)⁻¹ =
          sp6Gens.getD (RX.L (lget RX.OFF i + k)) 1 * (c * sp6InvReps.getD i 1 * c⁻¹) *
            (sp6Gens.getD (RX.L (lget RX.OFF i + k)) 1)⁻¹ := by group
      rw [e]
      exact prep_pcomp (by norm_num) (prep_pcomp (by norm_num) (prepGen _ hl) hr) (prepGenInv _ hl)

theorem rec_inv {j : Nat} (hj : j < RX.N) :
    ∃ g ∈ sp6Q.originalSubgroup, orderOf g = 2 ∧ PRep 36 6 (RX.E j) g := by
  have F := rec_facts hj
  have hi : RX.CI j < 4 := hlen ▸ F.ci_lt
  obtain ⟨c, hc, hr⟩ := rec_conj hi _ F.loc_lt
  have e : lget RX.OFF (RX.CI j) + (j - lget RX.OFF (RX.CI j)) = j := by
    have := F.off_le
    omega
  rw [e] at hr
  have hmem : sp6InvReps.getD (RX.CI j) 1 ∈ sp6InvReps := by
    rw [List.getD_eq_getElem _ _ (by rw [sp6InvReps_eq]; exact hi)]
    exact List.getElem_mem _
  obtain ⟨h1, h2⟩ := sp6InvReps_mem _ hmem
  refine ⟨_, mul_mem (mul_mem hc h1) (inv_mem hc), ?_, hr⟩
  rw [← h2]
  exact MulEquiv.orderOf_eq (MulAut.conj c) _

theorem rec_eq {a b : Nat} (ha : a < RX.N) (hb : b < RX.N) {g : Equiv.Perm (Fin 36)}
    (hga : PRep 36 6 (RX.E a) g) (hgb : PRep 36 6 (RX.E b) g) : a = b := by
  apply E_inj (fun j hj => allN_iff.1 kRX j hj) ha hb
  obtain ⟨-, hw, hA0, -⟩ := PF.canon_facts (rec_facts ha).canon
  obtain ⟨-, -, hB0, -⟩ := PF.canon_facts (rec_facts hb).canon
  exact PF.eq_of_fields (PF.w_pos hw) hA0 hB0 fun i hi => by
    rw [hga ⟨i, hi⟩, hgb ⟨i, hi⟩]

theorem exists_rec
    {u : Equiv.Perm (Fin 36)} (hu : u ∈ co3X36)
    (ho : orderOf u = 2) : ∃ j < RX.N, PRep 36 6 (RX.E j) u := by
  classical
  rw [← sp6Q_originalSubgroup] at hu
  have hX := forall₂_cosetOrderTables (by norm_num : (36 : ℕ) < 2 ^ 32) sp6Q 1
    (by norm_num : 0 < 2)
  set xs := (((enumeration sp6Q).map (1 * ·)).filter fun h => decide (orderOf h = 2)).reverse
  have hxs : ∀ x, x ∈ xs ↔ x ∈ sp6Q.originalSubgroup ∧ orderOf x = 2 := by
    intro x
    simp only [xs, List.mem_reverse, List.mem_filter, List.mem_map, one_mul, exists_eq_right,
      mem_enumeration_iff sp6Q sp6Q_valid, decide_eq_true_eq]
  have hxl : xs.length = RX.N := by rw [← hX.length_eq, cntX]
  choose! ε hε using fun j (hj : j < RX.N) => rec_inv hj
  set εs := (List.range RX.N).map ε
  have hnd : εs.Nodup := List.Nodup.map_on (fun a ha b hb e => by
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    exact rec_eq ha' hb' (hε a ha').2.2 (e ▸ (hε b hb').2.2)) List.nodup_range
  have hperm : εs.Perm xs := by
    refine (hnd.subperm fun y hy => ?_).perm_of_length_le (by rw [hxl]; simp [εs])
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hj' := List.mem_range.1 hj
    exact (hxs _).2 ⟨(hε j hj').1, (hε j hj').2.1⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (hperm.symm.subset ((hxs u).2 ⟨hu, ho⟩))
  exact ⟨j, List.mem_range.1 hj, (hε j (List.mem_range.1 hj)).2.2⟩

theorem mem_invs :
    ∀ t ∈ orderTables co3Sp36Chain 2, ∃ j < RX.N, t = tabP 36 6 (RX.E j) := by
  intro T hT
  obtain ⟨g, hg, hTg⟩ := exists_of_forall₂
    (forall₂_orderTables (by norm_num : (36 : ℕ) < 2 ^ 32) co3Sp36Chain (m := 2) (by norm_num))
    T hT
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ valid] at hg
  obtain ⟨j, hj, hp⟩ := exists_rec hg.1 hg.2
  have hs : T.size = 36 := filterProducts_size _ (idT 36) [] (by simp [idT])
    (fun _ h => absurd h List.not_mem_nil) T hT
  exact ⟨j, hj, eq_tabP_of_rep (by norm_num) hs hTg (CFSG.KC.KGC31P.imageList_of_prep hp)⟩

theorem hI :
    ∀ t ∈ orderTables co3Sp36Chain 2, ∃ u, PP 36 6 u ∧ t = tabP 36 6 u := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  exact ⟨_, (inv_facts hj).1, rfl⟩

theorem xfacts : ((∀ c ∈ O.C5, ∀ b ∈ c, PP 36 6 b) ∧ cands5 = O.C5.map (List.map (tabP 36 6))) ∧
    ((∀ c ∈ O.C7, ∀ b ∈ c, PP 36 6 b) ∧ cands7 = O.C7.map (List.map (tabP 36 6))) ∧
    (PP 36 6 O.X5 ∧ x5T = tabP 36 6 O.X5) ∧ (PP 36 6 O.X7 ∧ x7T = tabP 36 6 O.X7) ∧
    pord 36 6 5 O.X5 = true ∧ pord 36 6 7 O.X7 = true := by
  have h := ch725105x
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨gridOK_spec hsz36 h.1, gridOK_spec hsz36 h.2.1, cellOK_spec hsz36 h.2.2.1,
    cellOK_spec hsz36 h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem orb5 :
    orbCheck 36 5 (orderTables co3Sp36Chain 2) (powTabs 36 x5T 5) cands5 = true := by
  obtain ⟨⟨hc, hce⟩, -, ⟨hx, hxe⟩, -, ho, -⟩ := xfacts
  rw [hxe, hce, orbCheck_powTabs hsz36 hx (by norm_num) ho hc hI, orbCheck, List.all_cons,
    List.all_nil, Bool.and_true, invOK_tabP hx, Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz36 hx (inv_facts hj).1 hc]
  exact (inv_facts hj).2.1

theorem orb7 :
    orbCheck 36 7 (orderTables co3Sp36Chain 2) (powTabs 36 x7T 7) cands7 = true := by
  obtain ⟨-, ⟨hc, hce⟩, -, ⟨hx, hxe⟩, -, ho⟩ := xfacts
  rw [hxe, hce, orbCheck_powTabs hsz36 hx (by norm_num) ho hc hI, orbCheck, List.all_cons,
    List.all_nil, Bool.and_true, invOK_tabP hx, Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz36 hx (inv_facts hj).1 hc]
  exact (inv_facts hj).2.2

end CertificateChecks.KernelS6I

end
