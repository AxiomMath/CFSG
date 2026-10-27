
module

public import Certificates.Kernel.KGC31M22.Checks
public import Certificates.Kernel.KGC31M22.Cos
public import Certificates.Kernel.KGC31M22.InvG
public import Certificates.Kernel.SporSch.Mathieu.M22Facts
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.Certificates.Kernel.KGC31PPow
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.SporSch.ChainKZTot
public import CFSG.Certificates.Kernel.SporSch.ChainKCount
public import CFSG.Certificates.Kernel.SporSch.ClsMem
public import CFSG.Quasithin.Vol2.KGFactC31M22RefBase
public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.Quasithin.Vol2.KGFactC31FixEq
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import CFSG.Monster.B.Mathieu.M22CheckInputs
public import CFSG.Quasithin.Vol2.KGFactC31M22Data
public import CFSG.Sporadic.Schreier.ImagePairs
import Mathlib.Tactic.Group
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
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
public import CFSG.Quasithin.Background.C2Basic
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
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M22
open CertificateChecks.KernelSporSch CFSG.KS.SporSch.MOC CFSG.KS.SporSch.ClsSpec
open CFSG.Monster.B.Mathieu CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem hsz : szOK 22 5 = true := M22OC.szOK'

theorem ppG (l : Int) : PP 22 5 (G l) := by
  unfold G
  split
  · exact CFSG.KC.HeGlueK.PP_of_permOK2 hsz M22OC.pA
  · exact CFSG.KC.HeGlueK.PP_of_permOK2 hsz M22OC.pB

theorem gensT_eq (l : Int) : gensT l = tabP 22 5 (G l) := by
  unfold gensT G
  split
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img M22OC.imgA
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img M22OC.imgB

theorem wordT_eq (wd : List Int) : wordT 22 gensT wd = tabP 22 5 (pw wd) :=
  wordT_tabP hsz gensT_eq ppG wd

theorem ppw' (wd : List Int) : PP 22 5 (pw wd) := PP_pword hsz ppG wd

theorem ppL (ws : List (List Int)) : ∀ b ∈ ws.map pw, PP 22 5 b := by
  intro b hb
  obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hb
  exact ppw' wd

theorem mapW (ws : List (List Int)) : ws.map (wordT 22 gensT) = (ws.map pw).map (tabP 22 5) := by
  rw [List.map_map]
  exact List.map_congr_left fun wd _ => wordT_eq wd

theorem beq_nat (x y : Nat) : (x == y) = Nat.beq x y := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨fun h => h ▸ Nat.beq_refl x, Nat.eq_of_beq_eq_true⟩

#kc_forall_chunks invAll (fun k => invBlkG k = true) 2 CertificateChecks.KernelKGC31M22.invBlkG 1

theorem invOne_all : ∀ j < D.c, invOneG j = true := by
  intro j hj
  have hN := Nat.eq_of_beq_eq_true kN
  have hk : j / 600 < 2 := by omega
  apply List.all_eq_true.1 (invAll (j / 600) hk) j
  rw [List.mem_range'_1]
  omega

theorem inv_facts {j : Nat} (hj : j < D.c) :
    PP 22 5 (D.ST j) ∧ porbOne 22 5 5 X5 C5 (D.ST j) = true ∧
      porbOne 22 5 7 X7 C7 (D.ST j) = true ∧ pactOne 22 5 11 X11 (D.ST j) = true := by
  have h := invOne_all j hj
  simp only [invOneG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨PP_of_permOK hsz h1, h2, h3, h4⟩

theorem ppR0 : PP 22 5 M22OC.R0 := by
  obtain ⟨hd, -, -⟩ := M22OC.clsOK2 0 (by decide)
  obtain ⟨-, -, hr, hST, -⟩ := clsHdK_facts hd
  rw [← Nat.eq_of_beq_eq_true M22OC.repCK, ← hST]
  exact (inv_facts hr).1

theorem prepD : CFSG.KS.Raw.Orb.PRep 22 5 D.R m22Rep1 := by
  have e : D.R = M22OC.R0 := Nat.eq_of_beq_eq_true M22OC.repCK
  rw [e]
  exact prep_of_imageList M22OC.imgRep0

theorem mem_invs : ∀ t ∈ orderTables m22Certificate 2, ∃ k < D.c, t = tabP 22 5 (D.ST k) := by
  intro T hT
  obtain ⟨g, hg, hTg⟩ := exists_of_forall₂
    (forall₂_orderTables hn22 m22Certificate (m := 2) (by norm_num)) T hT
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ validM22] at hg
  obtain ⟨d, hd, c, hc, hgc⟩ :=
    CFSG.ClassicalInvolution.m22_cover_and_centralizers.1 g (by simpa using hg.1) hg.2
  rw [List.mem_singleton] at hd
  subst hd
  have hcls := datum_class M22OC.chainQ M22OC.tA_eq M22OC.tB_eq M22OC.clsOK2 (j := 0)
    (by decide) prepD
  have hK : c ∈ Subgroup.closure ({m22gA, m22gB} : Set (Equiv.Perm (Fin 22))) :=
    (orig_pair (words := m22Words) (bv := (#v[0, 1, 2, 3, 4] : Vector (Fin 22) 5))
      (gA := m22gA) (gB := m22gB) (by decide) (by decide)).le hc
  obtain ⟨k, hk, pk⟩ := (hcls.1 g).1 ⟨c, hK, hgc⟩
  refine ⟨k, hk, ?_⟩
  have hs : T.size = 22 := filterProducts_size _ (idT 22) [] (by simp [idT])
    (fun _ h => absurd h List.not_mem_nil) T hT
  rw [CFSG.KS.Tbl.toTable_ext hn22 hs hTg]
  exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (CFSG.KC.KGC31P.imageList_of_prep pk)

theorem hI : ∀ t ∈ orderTables m22Certificate 2, ∃ u, PP 22 5 u ∧ t = tabP 22 5 u := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  exact ⟨_, (inv_facts hj).1, rfl⟩

theorem conj_map (c : List ℤ) (ws : List (List ℤ)) :
    (ws.map (wordT 22 gensT)).map (conjTab 22 (wordT 22 gensT c) (invT 22 (wordT 22 gensT c))) =
      ((ws.map pw).map (pcj 22 5 (pw c) (pinv 22 5 (pw c)))).map (tabP 22 5) := by
  rw [mapW, wordT_eq, invT_tabP (ppw' c)]
  simp only [List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply]
  exact conjTab_tabP (ppw' c) (ppw' c).pinv (ppw' b)

theorem hex2_eq : hex2T = hex2P.map (tabP 22 5) := by
  unfold hex2T hex2P hexT hexConjT hexP hcP
  exact conj_map hexConjW hexW

theorem cands5_eq : cands5 = C5.map (List.map (tabP 22 5)) := by
  rw [cands5, C5, hex2_eq, duadT, hexT, mapW, mapW, duadP, hexP]
  rfl

theorem cands7_eq : cands7 = C7.map (List.map (tabP 22 5)) := by
  rw [cands7, C7, e8T, mapW, e8P]
  rfl

theorem ppC5 : ∀ c ∈ C5, ∀ b ∈ c, PP 22 5 b := by
  simp only [C5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  refine ⟨ppL _, ppL _, ?_⟩
  intro b hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  exact PP_pcj (ppw' _) (ppw' _).pinv (ppL hexW b' hb')

theorem ppC7 : ∀ c ∈ C7, ∀ b ∈ c, PP 22 5 b := by
  simp only [C7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  exact ppL _

theorem ord5 : ordTest 22 5 x5T = true := by rw [x5T, wordT_eq, ordTest_tabP (ppw' w5)]; exact kOrd5
theorem ord7 : ordTest 22 7 x7T = true := by rw [x7T, wordT_eq, ordTest_tabP (ppw' w7)]; exact kOrd7
theorem ord11 : ordTest 22 11 x11T = true := by
  rw [x11T, wordT_eq, ordTest_tabP (ppw' w11)]; exact kOrd11

theorem orb5 : orbCheck 22 5 (orderTables m22Certificate 2) (powTabs 22 x5T 5) cands5 = true := by
  rw [x5T, wordT_eq, cands5_eq, orbCheck_powTabs hsz (ppw' w5) (by norm_num) kOrd5 ppC5 hI,
    orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w5), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz (ppw' w5) (inv_facts hj).1 ppC5]
  exact (inv_facts hj).2.1

theorem orb7 : orbCheck 22 7 (orderTables m22Certificate 2) (powTabs 22 x7T 7) cands7 = true := by
  rw [x7T, wordT_eq, cands7_eq, orbCheck_powTabs hsz (ppw' w7) (by norm_num) kOrd7 ppC7 hI,
    orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w7), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz (ppw' w7) (inv_facts hj).1 ppC7]
  exact (inv_facts hj).2.2.1

theorem act11 : actCheck 22 11 (orderTables m22Certificate 2) (powTabs 22 x11T 11) = true := by
  rw [x11T, wordT_eq, actCheck_powTabs (ppw' w11) (by norm_num) kOrd11 hI, actCheck,
    List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w11), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP (ppw' w11) (inv_facts hj).1]
  exact (inv_facts hj).2.2.2

theorem hcInv : invOK 22 hexConjT (invT 22 hexConjT) = true := by
  rw [hexConjT, wordT_eq]
  exact invOK_tabP (ppw' _)

theorem kEbP : pebasis 22 5 hexP = true ∧ pebasis 22 5 duadP = true ∧ pebasis 22 5 e8P = true := by
  have h := kEb
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ebW (ws : List (List ℤ)) :
    ebasisOK 22 (ws.map (wordT 22 gensT)) = pebasis 22 5 (ws.map pw) := by
  rw [mapW]
  exact ebasisOK_tabP hsz (ppL ws)

theorem eb : ebasisOK 22 hexT = true ∧ ebasisOK 22 duadT = true ∧ ebasisOK 22 e8T = true :=
  ⟨(ebW hexW).trans kEbP.1, (ebW duadW).trans kEbP.2.1, (ebW e8W).trans kEbP.2.2⟩

@[expose] noncomputable def ev (w : List ℤ) : Equiv.Perm (Fin 22) := (elt w : G₀)

@[expose] noncomputable def evN (w : List ℕ) : Equiv.Perm (Fin 22) := ev (w.map Int.ofNat)

theorem ev_mem (w : List ℤ) : ev w ∈ NativeSporadic.M22 := (elt w).2

theorem rep_pw (w : List ℤ) : Rep 22 (tabP 22 5 (pw w)) (ev w) := by
  rw [← wordT_eq]
  exact rep_elt w

theorem rep_pinv (w : List ℤ) : Rep 22 (tabP 22 5 (pinv 22 5 (pw w))) (ev w)⁻¹ := by
  rw [← invT_tabP (ppw' w)]
  exact CFSG.KS.Tbl.invT_rep hn22 (rep_pw w)

theorem ppN (r : List ℕ) : PP 22 5 (pwN r) := ppw' _

theorem rep_pwN (r : List ℕ) : Rep 22 (tabP 22 5 (pwN r)) (evN r) := rep_pw _

theorem rep_pinvN (r : List ℕ) : Rep 22 (tabP 22 5 (pinv 22 5 (pwN r))) (evN r)⁻¹ := rep_pinv _

theorem rep_eq {T : Table} {g h : Equiv.Perm (Fin 22)} (hg : Rep 22 T g) (hh : Rep 22 T h) :
    g = h :=
  Equiv.ext fun i => Fin.ext ((rep_apply hg i).symm.trans (rep_apply hh i))

@[expose] noncomputable def bv (ws : List (List ℤ)) : Fin ws.length → Equiv.Perm (Fin 22) :=
  fun i => ev (ws.get i)

theorem forall₂_bv (ws : List (List ℤ)) :
    List.Forall₂ (Rep 22) (ws.map (wordT 22 gensT)) (List.ofFn (bv ws)) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, bv]
  exact rep_elt _

theorem eb_of {ws : List (List ℤ)} (h : pebasis 22 5 (ws.map pw) = true) : EBasis (bv ws) :=
  ebasis_of_ebasisOK hn22 (forall₂_bv ws) (by rw [ebW]; exact h)

theorem normAll_eq (ws : List (List ℤ)) (hE : EBasis (bv ws)) {T : Table}
    {g : Equiv.Perm (Fin 22)} (hT : Rep 22 T g) :
    normAll 22 (ws.map (wordT 22 gensT)) T = true ↔ g ∈ eNorm hE :=
  normAll_iff hn22 hE (forall₂_bv ws) hT

theorem bv_zero {ws : List (List ℤ)} (hw : 0 < ws.length) : bv ws ⟨0, hw⟩ = ev (ws.headD []) := by
  cases ws with
  | nil => exact absurd hw (by simp)
  | cons w ws => rfl

theorem headD_pw {ws : List (List ℤ)} (hw : 0 < ws.length) :
    (ws.map pw).headD 0 = pw (ws.headD []) := by
  cases ws with
  | nil => exact absurd hw (by simp)
  | cons w ws => rfl

theorem hcent : centralizerIn m22Certificate.originalSubgroup m22Rep1 =
    m22CentQ1.originalSubgroup :=
  CFSG.ClassicalInvolution.m22_cover_and_centralizers.2 (m22Rep1, m22CentQ1.originalSubgroup)
    (List.mem_singleton_self _)

theorem validQ1 : ValidSchreier m22CentQ1 := chainK_valid M22OC.chainC1 (by decide) (by decide)

theorem mem_E1 (g : Equiv.Perm (Fin 22)) : g ∈ (enumeration m22CentQ1).reverse ↔
    g ∈ NativeSporadic.M22 ∧ g * m22Rep1 = m22Rep1 * g := by
  rw [List.mem_reverse, mem_enumeration_iff _ validQ1, ← hcent, mem_centralizerIn,
    m22Certificate_original]

@[expose] noncomputable def Lz (ζ : Equiv.Perm (Fin 22)) : List (Equiv.Perm (Fin 22)) :=
  (enumeration m22CentQ1).reverse.map (MulAut.conj ζ)

theorem mem_Lz {ζ u : Equiv.Perm (Fin 22)} (hζ : ζ ∈ NativeSporadic.M22)
    (hz : ζ * m22Rep1 * ζ⁻¹ = u) (x : Equiv.Perm (Fin 22)) :
    x ∈ Lz ζ ↔ x ∈ centralizerIn NativeSporadic.M22 u := by
  rw [Lz, List.mem_map, mem_centralizerIn]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgK, hga⟩ := (mem_E1 g).1 hg
    rw [MulAut.conj_apply, ← hz]
    refine ⟨NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem hζ hgK)
      (NativeSporadic.M22.inv_mem hζ), ?_⟩
    calc ζ * g * ζ⁻¹ * (ζ * m22Rep1 * ζ⁻¹) = ζ * (g * m22Rep1) * ζ⁻¹ := by group
      _ = ζ * (m22Rep1 * g) * ζ⁻¹ := by rw [hga]
      _ = ζ * m22Rep1 * ζ⁻¹ * (ζ * g * ζ⁻¹) := by group
  · rintro ⟨hxK, hxb⟩
    rw [← hz] at hxb
    refine ⟨ζ⁻¹ * x * ζ, (mem_E1 _).2 ⟨NativeSporadic.M22.mul_mem
      (NativeSporadic.M22.mul_mem (NativeSporadic.M22.inv_mem hζ) hxK) hζ, ?_⟩, ?_⟩
    · calc ζ⁻¹ * x * ζ * m22Rep1 = ζ⁻¹ * (x * (ζ * m22Rep1 * ζ⁻¹)) * ζ := by group
        _ = ζ⁻¹ * ((ζ * m22Rep1 * ζ⁻¹) * x) * ζ := by rw [hxb]
        _ = m22Rep1 * (ζ⁻¹ * x * ζ) := by group
    · rw [MulAut.conj_apply]
      group

theorem nodup_Lz (ζ : Equiv.Perm (Fin 22)) : (Lz ζ).Nodup :=
  List.Nodup.map (MulAut.conj ζ).injective (List.nodup_reverse.2 (enumeration_nodup _ validQ1))

theorem ppTR : ∀ L ∈ trPL 22 5 M22C1.LR M22C1.TR 3, ∀ t ∈ L, PP 22 5 t := fun L hL t ht => by
  have h := kTR
  rw [Bool.and_eq_true] at h
  exact PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 h.1 L hL) t ht)

theorem ppTRDU : ∀ L ∈ trPL 22 5 CDU.LR CDU.TR 3, ∀ t ∈ L, PP 22 5 t := fun L hL t ht => by
  have h := kTR
  rw [Bool.and_eq_true] at h
  exact PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 h.2 L hL) t ht)

theorem ppCB : ∀ c ∈ CB, PP 22 5 c :=
  PP_pfilterProducts hsz _ ppTR _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem ppCent (r : List ℕ) : ∀ c ∈ cent (pwN r), PP 22 5 c := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact PP_pcj (ppw' _) (ppw' _).pinv (ppCB d hd)

theorem allQ1 : allTables m22CentQ1 = CB.map (tabP 22 5) := by
  have hL : levelTables m22CentQ1 =
      (trPL 22 5 M22C1.LR M22C1.TR 3).map (List.map (tabP 22 5)) :=
    levelTables_eq M22OC.chainC1 (by decide) (by decide)
  rw [allTables, hL, idT_tabP hsz]
  have := filterProducts_tabP (f := allTrue) (fk := fun _ => true) (fun _ _ => rfl) _ ppTR
    (pidn 22 5) [] (PP.id hsz)
  rwa [List.map_nil] at this

theorem forall₂_cent (r : List ℕ) :
    List.Forall₂ (Rep 22) ((cent (pwN r)).map (tabP 22 5)) (Lz (evN r)) := by
  have e : (cent (pwN r)).map (tabP 22 5) = (CB.map (tabP 22 5)).map
      (conjTab 22 (tabP 22 5 (pwN r)) (tabP 22 5 (pinv 22 5 (pwN r)))) := by
    rw [cent, List.map_map, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    simp only [Function.comp_apply]
    exact (conjTab_tabP (ppw' _) (ppw' _).pinv (ppCB c hc)).symm
  have h1 : List.Forall₂ (Rep 22) (CB.map (tabP 22 5)) (enumeration m22CentQ1).reverse := by
    rw [← allQ1]
    exact forall₂_allTables hn22 m22CentQ1
  rw [e, Lz, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h1.imp fun T g h => by
    rw [MulAut.conj_apply]
    exact rep_conjTab (rep_pw _) (rep_pinv _) h

theorem conj_a {r0 : List ℕ} {u : List ℤ}
    (h : Nat.beq (pcj 22 5 (pwN r0) (pinv 22 5 (pwN r0)) M22OC.R0) (pw u) = true) :
    evN r0 * m22Rep1 * (evN r0)⁻¹ = ev u := by
  have hrep : Rep 22 (tabP 22 5 M22OC.R0) m22Rep1 := by
    have e : toTable m22Rep1 = tabP 22 5 M22OC.R0 :=
      CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img M22OC.imgRep0
    rw [← e]
    exact rep_toTable hn22 _
  have e1 : Rep 22 (tabP 22 5 (pcj 22 5 (pwN r0) (pinv 22 5 (pwN r0)) M22OC.R0))
      (evN r0 * m22Rep1 * (evN r0)⁻¹) := by
    rw [← conjTab_tabP (ppN r0) (ppN r0).pinv ppR0]
    exact rep_conjTab (rep_pwN _) (rep_pinvN _) hrep
  rw [Nat.eq_of_beq_eq_true h] at e1
  exact rep_eq e1 (rep_pw u)

theorem card_cent_eq {r0 : List ℕ} {u : Equiv.Perm (Fin 22)}
    (hz : evN r0 * m22Rep1 * (evN r0)⁻¹ = u) {P : Equiv.Perm (Fin 22) → Prop} [DecidablePred P]
    {fk : Nat → Bool} (hP : ∀ c g, PP 22 5 c → Rep 22 (tabP 22 5 c) g → (fk c = true ↔ P g)) :
    Nat.card {c : NativeSporadic.M22 // (c : Equiv.Perm (Fin 22)) * u = u * c ∧ P c} =
      (cent (pwN r0)).countP fk := by
  have e1 : Nat.card {c : NativeSporadic.M22 // (c : Equiv.Perm (Fin 22)) * u = u * c ∧ P c} =
      Nat.card {c : centralizerIn NativeSporadic.M22 u // P c} :=
    Nat.card_congr
      { toFun := fun c => ⟨⟨c.1.1, mem_centralizerIn.2 ⟨c.1.2, c.2.1⟩⟩, c.2.2⟩
        invFun := fun c => ⟨⟨c.1.1, (mem_centralizerIn.1 c.1.2).1⟩,
          (mem_centralizerIn.1 c.1.2).2, c.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, card_subtype_eq_countP _ (Lz (evN r0)) (nodup_Lz _) (mem_Lz (ev_mem _) hz) P]
  have h2 : List.Forall₂ (fun c g => PP 22 5 c ∧ Rep 22 (tabP 22 5 c) g) (cent (pwN r0))
      (Lz (evN r0)) :=
    (List.forall₂_and_left _ _).2 ⟨ppCent r0, List.forall₂_map_left_iff.1 (forall₂_cent r0)⟩
  refine (countP_eq_of_forall₂ h2 fun c g h _ => ?_).symm
  rw [hP c g h.1 h.2, decide_eq_true_iff]

theorem comm_count (ws : List (List ℤ)) (hw : 0 < ws.length) (r0 : List ℕ)
    (hz : evN r0 * m22Rep1 * (evN r0)⁻¹ = ev (ws.headD [])) :
    countProducts 22 (commAll 22 (ws.map (wordT 22 gensT))) (levelTables m22Certificate)
        (idT 22) = (cent (pwN r0)).countP (pcommAll 22 5 (ws.map pw)) := by
  classical
  have hfP : ∀ T g, Rep 22 T g → (commAll 22 (ws.map (wordT 22 gensT)) T = true ↔
      ∀ i, g * bv ws i = bv ws i * g) := fun T g hT => by
    unfold commAll
    exact CFSG.Quasithin.KGC31.all_iff_of_forall₂ (forall₂_bv ws) fun b x hb =>
      tblEq_iff_eq (Rep.compT hT hb) (Rep.compT hb hT)
  rw [← card_m22_eq (P := fun g => ∀ i, g * bv ws i = bv ws i * g) hfP]
  have e : Nat.card {x : G₀ // ∀ i, (x : Equiv.Perm (Fin 22)) * bv ws i = bv ws i * x} =
      Nat.card {c : NativeSporadic.M22 // (c : Equiv.Perm (Fin 22)) * ev (ws.headD []) =
        ev (ws.headD []) * c ∧ ∀ i, (c : Equiv.Perm (Fin 22)) * bv ws i = bv ws i * c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun h => ⟨by rw [← bv_zero hw]; exact h _, h⟩, fun h => h.2⟩)
  rw [e]
  refine card_cent_eq (P := fun g => ∀ i, g * bv ws i = bv ws i * g) hz fun c g hc hg => ?_
  rw [← commAll_tabP (ppL ws) hc, ← mapW]
  exact hfP _ g hg

theorem maskVec_inj {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : maskVec k a = maskVec k b) : a = b := by
  have hs : Function.Surjective (fun m : Fin (2 ^ k) => maskVec k m) := fun c => by
    obtain ⟨m, hm, rfl⟩ := exists_maskVec c
    exact ⟨⟨m, hm⟩, rfl⟩
  have hc : Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → ZMod 2) := by simp
  have hi := ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hs, hc⟩).1
  exact congrArg Fin.val (hi (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)

theorem norm_count (ws : List (List ℤ)) (hw : 0 < ws.length) (hE : EBasis (bv ws))
    (r0 : List ℕ) (rsN : List (List ℕ)) (hz : evN r0 * m22Rep1 * (evN r0)⁻¹ = ev (ws.headD []))
    (hok : pcosetOK 22 5 (pw (ws.headD [])) (ws.map pw) (rsN.map pwN) = true) :
    countProducts 22 (normAll 22 (ws.map (wordT 22 gensT))) (levelTables m22Certificate)
        (idT 22) =
      pcosetCount 22 5 (cent (pwN r0)) (rsN.map pwN)
        (fun g => pnormAll 22 5 (ws.map pw) g (pinv 22 5 g)) := by
  classical
  set u := ev (ws.headD []) with hu
  set rsW := rsN.map (List.map Int.ofNat)
  have hfP : ∀ T g, Rep 22 T g → (normAll 22 (ws.map (wordT 22 gensT)) T = true ↔
      g ∈ eNorm hE) := fun T g hT => normAll_eq ws hE hT
  have hrs : List.Forall₂ (Rep 22) (rsW.map (wordT 22 gensT)) (rsN.map evN) := by
    rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun r _ => rep_elt _
  have hok' : cosetOK 22 (wordT 22 gensT (ws.headD [])) (ws.map (wordT 22 gensT))
      (rsW.map (wordT 22 gensT)) = true := by
    rw [wordT_eq, mapW, mapW, cosetOK_tabP hsz (ppw' _) (ppL ws) (ppL rsW), List.map_map]
    exact hok
  have hb : Rep 22 (wordT 22 gensT (ws.headD [])) u := rep_elt _
  have hu0 : u = bv ws ⟨0, hw⟩ := (bv_zero hw).symm
  have hconj : ∀ m (hm : m < (rsN.map evN).length), (rsN.map evN)[m] * u * (rsN.map evN)[m]⁻¹ =
      eElt (bv ws) (maskVec ws.length (m + 1)) := by
    intro m hm
    have hlen' : (rsW.map (wordT 22 gensT)).length = (rsN.map evN).length := hrs.length_eq
    have hok2 := hok'
    unfold cosetOK at hok2
    rw [Bool.and_eq_true, List.all_eq_true] at hok2
    have hm' : m < (rsW.map (wordT 22 gensT)).length := by omega
    have h1 := hok2.2 m (List.mem_range.mpr hm')
    rw [Bool.and_eq_true] at h1
    have hr : Rep 22 ((rsW.map (wordT 22 gensT)).getD m (idT 22)) (rsN.map evN)[m] := by
      rw [List.getD_eq_getElem _ _ hm']
      have := (List.forall₂_iff_get.mp hrs).2 m hm' hm
      simpa using this
    have hri := Rep.inv_of_invOK hr h1.1
    have hlen : (ws.map (wordT 22 gensT)).length = ws.length := List.length_map _
    exact (tblEq_iff_eq (rep_conjTab hr hri hb)
      (rep_maskProd hn22 (bv ws) _ (forall₂_bv ws) (m + 1))).mp h1.2
  have hlen2 : (rsN.map evN).length + 1 = 2 ^ ws.length := by
    have hok2 := hok'
    unfold cosetOK at hok2
    rw [Bool.and_eq_true, beq_iff_eq] at hok2
    simp only [List.length_map] at hok2
    simpa [rsW] using hok2.1
  have hd : (rsN.map evN).Pairwise fun r r' => r * u * r⁻¹ ≠ r' * u * r'⁻¹ := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij e
    rw [hconj i hi, hconj j hj] at e
    have := maskVec_inj (by omega) (by omega) (eElt_injective hE e)
    omega
  have hP : ∀ g ∈ NativeSporadic.M22, g ∈ eNorm hE →
      ∃ r ∈ rsN.map evN, g * u * g⁻¹ = r * u * r⁻¹ := by
    intro g _ hgN
    have hb0 : u ∈ eSub hE := hu0 ▸ mem_eSub hE ⟨0, hw⟩
    have hx : g * u * g⁻¹ ∈ eSub hE := (Subgroup.mem_normalizer_iff.mp hgN u).mp hb0
    have hb1 : u ≠ 1 := by
      intro h
      have h1 := hE.ne_one (Pi.single ⟨0, hw⟩ 1) (by rw [eElt_single, ← hu0, h])
      have := congrFun h1 ⟨0, hw⟩
      simp at this
    have hx1 : g * u * g⁻¹ ≠ 1 := by
      intro h
      apply hb1
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact exists_conj_of_cosetOK hn22 hE (forall₂_bv ws) hb hrs hok' hx hx1
  rw [← card_m22_eq (P := (· ∈ eNorm hE)) hfP, card_eq_sum_coset (K := NativeSporadic.M22) u (rsN.map evN)
    (· ∈ eNorm hE) hP (fun r hr => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
      exact ev_mem _) hd, pcosetCount, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply]
  refine card_cent_eq (P := fun c => evN r * c ∈ eNorm hE) hz fun c g hc hg => ?_
  have hpc := (ppN r).pc hc
  rw [← normAll_tabP hsz (ppL ws) hpc, ← mapW, ← compT_tabP' (ppN r) hc]
  exact normAll_eq ws hE (Rep.compT (rep_pwN r) hg)

theorem cosP (i : Nat) (U : List Nat) (r0 : List ℕ) (rs : List (List ℕ)) (cC cN : Nat)
    (h : cosAll U (pwN r0) (rs.map pwN) cC cN = true) :
    Nat.beq (pcj 22 5 (pwN r0) (pinv 22 5 (pwN r0)) M22OC.R0) (U.headD 0) = true ∧
      pcosetOK 22 5 (U.headD 0) U (rs.map pwN) = true ∧
      (cent (pwN r0)).countP (pcommAll 22 5 U) = cC ∧
      pcosetCount 22 5 (cent (pwN r0)) (rs.map pwN)
        (fun g => pnormAll 22 5 U g (pinv 22 5 g)) = cN := by
  unfold cosAll at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem counts_of (ws : List (List ℤ)) (hw : 0 < ws.length) (r0 : List ℕ) (rs : List (List ℕ))
    (cC cN : Nat) (heb : pebasis 22 5 (ws.map pw) = true)
    (h : cosAll (ws.map pw) (pwN r0) (rs.map pwN) cC cN = true) :
    countProducts 22 (commAll 22 (ws.map (wordT 22 gensT))) (levelTables m22Certificate)
        (idT 22) = cC ∧
      countProducts 22 (normAll 22 (ws.map (wordT 22 gensT))) (levelTables m22Certificate)
        (idT 22) = cN := by
  obtain ⟨h1, h2, h3, h4⟩ := cosP 0 _ r0 rs cC cN h
  rw [headD_pw hw] at h1 h2
  have hz := conj_a h1
  exact ⟨(comm_count ws hw r0 hz).trans h3,
    (norm_count ws hw (eb_of heb) r0 rs hz h2).trans h4⟩

theorem cntHex : countProducts 22 (commAll 22 hexT) (levelTables m22Certificate) (idT 22) = 16 ∧
    countProducts 22 (normAll 22 hexT) (levelTables m22Certificate) (idT 22) = 5760 := by
  have h := cosBlk0
  unfold cosBlk at h
  rw [if_pos rfl] at h
  unfold hexP at h
  have hb := kEbP.1
  unfold hexP at hb
  rw [hexT]
  exact counts_of hexW (by decide) W.hexR0 W.hexRs 16 5760 hb h

theorem cntDuad : countProducts 22 (commAll 22 duadT) (levelTables m22Certificate) (idT 22) = 16 ∧
    countProducts 22 (normAll 22 duadT) (levelTables m22Certificate) (idT 22) = 1920 := by
  have h := cosBlk1
  unfold cosBlk at h
  rw [if_neg (by decide), if_pos rfl] at h
  unfold duadP at h
  have hb := kEbP.2.1
  unfold duadP at hb
  rw [duadT]
  exact counts_of duadW (by decide) W.duadR0 W.duadRs 16 1920 hb h

theorem cntE8 : countProducts 22 (commAll 22 e8T) (levelTables m22Certificate) (idT 22) = 8 ∧
    countProducts 22 (normAll 22 e8T) (levelTables m22Certificate) (idT 22) = 1344 := by
  have h := cosBlk2
  unfold cosBlk at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  unfold e8P at h
  have hb := kEbP.2.2
  unfold e8P at hb
  rw [e8T]
  exact counts_of e8W (by decide) W.e8R0 W.e8Rs 8 1344 hb h

theorem tab_img (w : List Int) : imageList (tab (wordG gensG w)) = (unpack 22 5 (pw w)).toList := by
  rw [tab_eq]
  refine imageList_of_rep (ppw' w).1 ?_
  rw [← wordT_eq]
  exact Rep.wordT hn22 w fun l _ => hrep l

theorem toTable_tab (w : List Int) : toTable (tab (wordG gensG w)) = tabP 22 5 (pw w) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (tab_img w)

theorem gens_img {ws : List (List Int)} {S : Nat → Nat} {m : Nat} (hl : ws.length = m)
    (h : (List.range m).all (fun j => Nat.beq (S j) (pw (ws.getD j []))) = true) :
    ∀ j < (ws.map fun w => tab (wordG gensG w)).length,
      imageList ((ws.map fun w => tab (wordG gensG w)).getD j 1) = (unpack 22 5 (S j)).toList := by
  intro j hj
  have hj' : j < ws.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map, tab_img, ← List.getD_eq_getElem _ [] hj',
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h j (List.mem_range.2 (hl ▸ hj')))]

theorem kGensP : (List.range 2).all (fun j => Nat.beq (CHX.S j) (pw (hexGenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CDU.S j) (pw (duadGenW.getD j []))) = true := by
  have h := kGens
  rw [Bool.and_eq_true] at h
  exact h

theorem chainHX : ChainK 22 5 hexGen hexChainW (#v[0, 1, 2, 3] : Vector (Fin 22) 4)
    CHX.S CHX.SI CHX.LR CHX.TR CHX.TRI 8 CHX.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.1, by decide, CHX.head, CHX.hl,
    by norm_num, CHX.hs⟩

theorem chainDU : ChainK 22 5 duadGen duadChainW (#v[2, 3, 4] : Vector (Fin 22) 3)
    CDU.S CDU.SI CDU.LR CDU.TR CDU.TRI 6 CDU.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2, by decide, CDU.head, CDU.hl,
    by norm_num, CDU.hs⟩

theorem kOrdCP : ordK CHX.LR 4 = 5760 ∧ ordK CDU.LR 3 = 960 := by
  have h := kOrd
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem chHX : hexChain.check = true ∧ hexChain.orderCertificate = 5760 := by
  obtain ⟨a, b⟩ := chainK_check (by decide) (by decide) chainHX
  exact ⟨a, b.trans kOrdCP.1⟩

theorem chDU : duadChain.check = true ∧ duadChain.orderCertificate = 960 := by
  obtain ⟨a, b⟩ := chainK_check (by decide) (by decide) chainDU
  exact ⟨a, b.trans kOrdCP.2⟩

theorem duadL : levelTables duadChain = (trPL 22 5 CDU.LR CDU.TR 3).map (List.map (tabP 22 5)) :=
  levelTables_eq chainDU (by decide) (by decide)

theorem duadIn : (duadT.all fun b =>
    countProducts 22 (tblEq 22 b) (levelTables duadChain) (idT 22) == 1) = true := by
  rw [duadT, mapW, List.all_map, duadL, idT_tabP hsz, ← kDuad]
  refine all_congr' fun b hb => ?_
  simp only [Function.comp_apply]
  rw [countProducts_tabP (f := tblEq 22 (tabP 22 5 b)) (fk := Nat.beq b)
    (fun X hX => tblEq_tabP (ppL duadW b hb) hX) _ ppTRDU _ (PP.id hsz), beq_nat]

theorem mzW (ws : List (List Int)) (gs : List (List Int)) (ms : List (List Nat)) :
    ((gs.map fun w => tab (wordG gensG w)).zip ms).all
        (fun p => masksOK 22 (ws.map (wordT 22 gensT)) (toTable p.1) p.2) =
      ((gs.map pw).zip ms).all (fun p => pmasksOK 22 5 (ws.map pw) p.1 p.2) := by
  rw [mapW, List.zip_map_left, List.zip_map_left, List.all_map, List.all_map]
  refine all_congr' fun p _ => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [toTable_tab, masksOK_tabP hsz (ppL ws) (ppw' _)]

theorem kMasksP : ((hexGenW.map pw).zip hexMasks).all (fun p => pmasksOK 22 5 hexP p.1 p.2) =
      true ∧
    ((duadGenW.map pw).zip duadMasks).all (fun p => pmasksOK 22 5 duadP p.1 p.2) = true := by
  have h := kMasks
  rw [Bool.and_eq_true] at h
  exact h

theorem mHex : (hexGen.zip hexMasks).all (fun p => masksOK 22 hexT (toTable p.1) p.2) = true :=
  (mzW hexW hexGenW hexMasks).trans kMasksP.1

theorem mDuad : (duadGen.zip duadMasks).all (fun p => masksOK 22 duadT (toTable p.1) p.2) =
    true :=
  (mzW duadW duadGenW duadMasks).trans kMasksP.2

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M22 in
open Certificates in
theorem cert7203 : ordTest 22 5 x5T = true ∧ ordTest 22 7 x7T = true ∧ ordTest 22 11 x11T = true ∧
    orbCheck 22 5 (orderTables m22Certificate 2) (powTabs 22 x5T 5) cands5 = true ∧
    orbCheck 22 7 (orderTables m22Certificate 2) (powTabs 22 x7T 7) cands7 = true ∧
    actCheck 22 11 (orderTables m22Certificate 2) (powTabs 22 x11T 11) = true ∧
    invOK 22 hexConjT (invT 22 hexConjT) = true ∧
    ebasisOK 22 hexT = true ∧ ebasisOK 22 duadT = true ∧ ebasisOK 22 e8T = true ∧
    countProducts 22 (commAll 22 hexT) (levelTables m22Certificate) (idT 22) = 16 ∧
    countProducts 22 (normAll 22 hexT) (levelTables m22Certificate) (idT 22) = 5760 ∧
    countProducts 22 (commAll 22 duadT) (levelTables m22Certificate) (idT 22) = 16 ∧
    countProducts 22 (normAll 22 duadT) (levelTables m22Certificate) (idT 22) = 1920 ∧
    countProducts 22 (commAll 22 e8T) (levelTables m22Certificate) (idT 22) = 8 ∧
    countProducts 22 (normAll 22 e8T) (levelTables m22Certificate) (idT 22) = 1344 ∧
    hexChain.check = true ∧ hexChain.orderCertificate = 5760 ∧
    duadChain.check = true ∧ duadChain.orderCertificate = 960 ∧
    (duadT.all fun b => countProducts 22 (tblEq 22 b) (levelTables duadChain) (idT 22) == 1) =
      true ∧
    (hexGen.zip hexMasks).all (fun p => masksOK 22 hexT (toTable p.1) p.2) = true ∧
    (duadGen.zip duadMasks).all (fun p => masksOK 22 duadT (toTable p.1) p.2) = true :=
  ⟨ord5, ord7, ord11, orb5, orb7, act11, hcInv, eb.1, eb.2.1, eb.2.2, cntHex.1, cntHex.2,
    cntDuad.1, cntDuad.2, cntE8.1, cntE8.2, chHX.1, chHX.2, chDU.1, chDU.2, duadIn, mHex,
    mDuad⟩

end CertificateChecks.KernelKGC31M22

end
