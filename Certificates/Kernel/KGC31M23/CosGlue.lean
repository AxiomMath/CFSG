
module

public import Certificates.Kernel.KGC31M23.Cnt
public import CFSG.Certificates.Kernel.CosetConj
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Quasithin.Vol2.KGFactC31M23Base
public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.Sporadic.Schreier.M23Data
public import CFSG.Sporadic.Schreier.M23PinnedInputs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
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
public import CFSG.Quasithin.Vol2.KGFactC31M23RefBase
public import CFSG.Sporadic.Schreier.M23
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M23
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M23OC
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.KC.CosetConj CFSG.Blueprint CFSG.Certificates

theorem hsz : szOK 23 5 = true := szOK'

theorem ppA : PP 23 5 (M23Q.S 0) := CFSG.KC.HeGlueK.PP_of_permOK2 hsz pA

theorem ppB : PP 23 5 (M23Q.S 1) := CFSG.KC.HeGlueK.PP_of_permOK2 hsz pB

theorem ppG (l : Int) : PP 23 5 (G l) := by
  unfold G
  split
  · exact ppA
  · exact ppB

theorem gensT_eq (l : Int) : gensT l = tabP 23 5 (G l) := by
  unfold gensT G
  split
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgA
  · exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgB

theorem wordT_eq (wd : List Int) : wordT 23 gensT wd = tabP 23 5 (pw wd) :=
  wordT_tabP hsz gensT_eq ppG wd

theorem ppw' (wd : List Int) : PP 23 5 (pw wd) := PP_pword hsz ppG wd

theorem ppL (ws : List (List Int)) : ∀ b ∈ ws.map pw, PP 23 5 b := by
  intro b hb
  obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hb
  exact ppw' wd

theorem mapW (ws : List (List Int)) : ws.map (wordT 23 gensT) = (ws.map pw).map (tabP 23 5) := by
  rw [List.map_map]
  exact List.map_congr_left fun wd _ => wordT_eq wd

@[expose] noncomputable def ev (w : List ℤ) : Equiv.Perm (Fin 23) := (elt w : G₀)

theorem ev_mem (w : List ℤ) : ev w ∈ NativeSporadic.M23 := (elt w).2

theorem rep_pw (w : List ℤ) : Rep 23 (tabP 23 5 (pw w)) (ev w) := by
  rw [← wordT_eq]
  exact rep_elt w

theorem rep_pinv (w : List ℤ) : Rep 23 (tabP 23 5 (pinv 23 5 (pw w))) (ev w)⁻¹ := by
  rw [← invT_tabP (ppw' w)]
  exact CFSG.KS.Tbl.invT_rep hn23 (rep_pw w)

theorem rep_pcj (w v : List ℤ) :
    Rep 23 (tabP 23 5 (pcj 23 5 (pw w) (pinv 23 5 (pw w)) (pw v))) (ev w * ev v * (ev w)⁻¹) := by
  rw [← conjTab_tabP (ppw' w) (ppw' w).pinv (ppw' v)]
  exact rep_conjTab (rep_pw w) (rep_pinv w) (rep_pw v)

theorem rep_eq {T : Table} {g h : Equiv.Perm (Fin 23)} (hg : Rep 23 T g) (hh : Rep 23 T h) :
    g = h :=
  Equiv.ext fun i => Fin.ext ((rep_apply hg i).symm.trans (rep_apply hh i))

@[expose] noncomputable def bv (ws : List (List ℤ)) : Fin ws.length → Equiv.Perm (Fin 23) :=
  fun i => ev (ws.get i)

theorem forall₂_bv (ws : List (List ℤ)) :
    List.Forall₂ (Rep 23) (ws.map (wordT 23 gensT)) (List.ofFn (bv ws)) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, bv]
  exact rep_elt _

theorem eb_of {ws : List (List ℤ)} (h : pebasis 23 5 (ws.map pw) = true) : EBasis (bv ws) :=
  ebasis_of_ebasisOK hn23 (forall₂_bv ws) (by rw [mapW, ebasisOK_tabP hsz (ppL ws)]; exact h)

theorem normAll_eq (ws : List (List ℤ)) (hE : EBasis (bv ws)) {T : Table}
    {g : Equiv.Perm (Fin 23)} (hT : Rep 23 T g) :
    normAll 23 (ws.map (wordT 23 gensT)) T = true ↔ g ∈ eNorm hE :=
  normAll_iff hn23 hE (forall₂_bv ws) hT

theorem mem_eNorm_of {ws : List (List ℤ)} (hE : EBasis (bv ws)) {v : List ℤ}
    (h : pnormAll 23 5 (ws.map pw) (pw v) (pinv 23 5 (pw v)) = true) : ev v ∈ eNorm hE := by
  rw [← normAll_eq ws hE (rep_pw v), mapW, normAll_tabP hsz (ppL ws) (ppw' v)]
  exact h

@[expose] noncomputable def C : Subgroup (Equiv.Perm (Fin 23)) :=
  centralizerIn NativeSporadic.M23 b0

theorem b0_eq : b0 = ev (wW.headD []) := rfl

theorem mem_cbG (g : Equiv.Perm (Fin 23)) : g ∈ cbG ↔ g ∈ C := by
  rw [cbG, List.mem_reverse, List.mem_filter, decide_eq_true_iff, mem_enumeration_iff _ validM23,
    m23Certificate_originalSubgroup, C, mem_centralizerIn]

theorem nodup_cbG : cbG.Nodup := List.nodup_reverse.2 ((enumeration_nodup _ validM23).filter _)

theorem eq_map_toTable : ∀ {Ts : List Table} {gs : List (Equiv.Perm (Fin 23))},
    List.Forall₂ (Rep 23) Ts gs → (∀ T ∈ Ts, T.size = 23) → Ts = gs.map toTable
  | [], [], .nil, _ => rfl
  | T :: Ts, g :: gs, .cons h hs, hsz => by
    rw [List.map_cons, CFSG.KS.Tbl.toTable_ext hn23 (hsz T List.mem_cons_self) h,
      eq_map_toTable hs fun T' h' => hsz T' (List.mem_cons_of_mem _ h')]

theorem cbT_eq : cbT = cbG.map toTable :=
  eq_map_toTable forall₂_cbT
    (filterProducts_size _ (idT 23) [] (by simp [idT]) (fun _ h => absurd h List.not_mem_nil))

@[expose] noncomputable def P1 : List Nat :=
  pfilterProducts 23 5 (fun _ => true) (trPL 23 5 M23C1.LR M23C1.TR 4) (pidn 23 5) []

theorem ppTR : ∀ L ∈ trPL 23 5 M23C1.LR M23C1.TR 4, ∀ t ∈ L, PP 23 5 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 kTR L hL) t ht)

theorem ppP1 : ∀ c ∈ P1, PP 23 5 c :=
  PP_pfilterProducts hsz _ ppTR _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem ppCB : ∀ c ∈ CB, PP 23 5 c := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact PP_pcj (ppw' _) (ppw' _).pinv (ppP1 d hd)

theorem allQ1 : allTables m23CentQ1 = P1.map (tabP 23 5) := by
  have hL : levelTables m23CentQ1 =
      (trPL 23 5 M23C1.LR M23C1.TR 4).map (List.map (tabP 23 5)) :=
    levelTables_eq chainC1 (by decide) (by decide)
  rw [allTables, hL, idT_tabP hsz]
  have := filterProducts_tabP (f := allTrue) (fk := fun _ => true) (fun _ _ => rfl) _ ppTR
    (pidn 23 5) [] (PP.id hsz)
  rwa [List.map_nil] at this

theorem validQ1 : ValidSchreier m23CentQ1 := chainK_valid chainC1 (by decide) (by decide)

theorem hcent : centralizerIn m23Certificate.originalSubgroup m23Rep1 =
    m23CentQ1.originalSubgroup :=
  CFSG.ClassicalInvolution.m23_cover_and_centralizers.2 (m23Rep1, m23CentQ1.originalSubgroup)
    (List.mem_singleton_self _)

theorem mem_E1 (g : Equiv.Perm (Fin 23)) : g ∈ (enumeration m23CentQ1).reverse ↔
    g ∈ NativeSporadic.M23 ∧ g * m23Rep1 = m23Rep1 * g := by
  rw [List.mem_reverse, mem_enumeration_iff _ validQ1, ← hcent, mem_centralizerIn,
    m23Certificate_originalSubgroup]

@[expose] noncomputable def ζ : Equiv.Perm (Fin 23) := ev (wI CFSG.KD.M23Conj.z)

theorem rep1_eq : m23Rep1 = ev [1] := by
  simp [m23Rep1, m23InvReps, m23InvRepWords, evalCodes, ev, elt, wordG, gensG]

theorem hzA : ζ * m23Rep1 * ζ⁻¹ = b0 := by
  rw [rep1_eq, b0_eq]
  refine rep_eq (rep_pcj _ [1]) ?_
  have e : pcj 23 5 (pw (wI CFSG.KD.M23Conj.z)) (pinv 23 5 (pw (wI CFSG.KD.M23Conj.z))) (pw [1]) =
      pw (wW.headD []) := Nat.eq_of_beq_eq_true kZ
  rw [e]
  exact rep_pw _

@[expose] noncomputable def Lz : List (Equiv.Perm (Fin 23)) :=
  (enumeration m23CentQ1).reverse.map (MulAut.conj ζ)

theorem mem_Lz (x : Equiv.Perm (Fin 23)) : x ∈ Lz ↔ x ∈ C := by
  have hζ : ζ ∈ NativeSporadic.M23 := ev_mem _
  rw [Lz, List.mem_map, C, mem_centralizerIn]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgK, hga⟩ := (mem_E1 g).1 hg
    rw [MulAut.conj_apply, ← hzA]
    refine ⟨NativeSporadic.M23.mul_mem (NativeSporadic.M23.mul_mem hζ hgK)
      (NativeSporadic.M23.inv_mem hζ), ?_⟩
    calc ζ * g * ζ⁻¹ * (ζ * m23Rep1 * ζ⁻¹) = ζ * (g * m23Rep1) * ζ⁻¹ := by group
      _ = ζ * (m23Rep1 * g) * ζ⁻¹ := by rw [hga]
      _ = ζ * m23Rep1 * ζ⁻¹ * (ζ * g * ζ⁻¹) := by group
  · rintro ⟨hxK, hxb⟩
    rw [← hzA] at hxb
    refine ⟨ζ⁻¹ * x * ζ, (mem_E1 _).2 ⟨NativeSporadic.M23.mul_mem
      (NativeSporadic.M23.mul_mem (NativeSporadic.M23.inv_mem hζ) hxK) hζ, ?_⟩, ?_⟩
    · calc ζ⁻¹ * x * ζ * m23Rep1 = ζ⁻¹ * (x * (ζ * m23Rep1 * ζ⁻¹)) * ζ := by group
        _ = ζ⁻¹ * ((ζ * m23Rep1 * ζ⁻¹) * x) * ζ := by rw [hxb]
        _ = m23Rep1 * (ζ⁻¹ * x * ζ) := by group
    · rw [MulAut.conj_apply]
      group

theorem nodup_Lz : Lz.Nodup :=
  List.Nodup.map (MulAut.conj ζ).injective (List.nodup_reverse.2 (enumeration_nodup _ validQ1))

theorem forall₂_CB : List.Forall₂ (Rep 23) (CB.map (tabP 23 5)) Lz := by
  have e : CB.map (tabP 23 5) = (P1.map (tabP 23 5)).map
      (conjTab 23 (tabP 23 5 Z) (tabP 23 5 (pinv 23 5 Z))) := by
    rw [CB, List.map_map, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    simp only [Function.comp_apply]
    exact (conjTab_tabP (ppw' _) (ppw' _).pinv (ppP1 c hc)).symm
  have h1 : List.Forall₂ (Rep 23) (P1.map (tabP 23 5)) (enumeration m23CentQ1).reverse := by
    rw [← allQ1]
    exact forall₂_allTables hn23 m23CentQ1
  rw [e, Lz, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h1.imp fun T g h => by
    rw [MulAut.conj_apply]
    exact rep_conjTab (rep_pw _) (rep_pinv _) h

theorem CB_eq : CB.map (tabP 23 5) = Lz.map toTable := by
  refine eq_map_toTable forall₂_CB fun T hT => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hT
  rw [tabP_eq (ppCB c hc)]
  exact CFSG.KS.Tbl.size_toTable _

theorem cbT_perm : cbT.Perm (CB.map (tabP 23 5)) := by
  rw [cbT_eq, CB_eq]
  exact ((List.perm_ext_iff_of_nodup nodup_cbG nodup_Lz).2 fun x =>
    (mem_cbG x).trans (mem_Lz x).symm).map _

theorem countP_cbT (f : Table → Bool) : cbT.countP f = CB.countP fun c => f (tabP 23 5 c) := by
  rw [cbT_perm.countP_eq, List.countP_map]
  rfl

theorem kappa_mem {w v : List ℤ} (h : ev v * b0 * (ev v)⁻¹ = ev w * b0 * (ev w)⁻¹) :
    (ev v)⁻¹ * ev w ∈ C := by
  rw [C, mem_centralizerIn]
  refine ⟨NativeSporadic.M23.mul_mem (NativeSporadic.M23.inv_mem (ev_mem v)) (ev_mem w), ?_⟩
  calc (ev v)⁻¹ * ev w * b0 = (ev v)⁻¹ * (ev w * b0 * (ev w)⁻¹) * ev w := by group
    _ = (ev v)⁻¹ * (ev v * b0 * (ev v)⁻¹) * ev w := by rw [h]
    _ = b0 * ((ev v)⁻¹ * ev w) := by group

theorem conj_eq_of {w v : List ℤ}
    (h : Nat.beq (pcj 23 5 (pw v) (pinv 23 5 (pw v)) B0) (pcj 23 5 (pw w) (pinv 23 5 (pw w)) B0) =
      true) : ev v * b0 * (ev v)⁻¹ = ev w * b0 * (ev w)⁻¹ := by
  refine rep_eq (rep_pcj v (wW.headD [])) ?_
  have e := Nat.eq_of_beq_eq_true h
  rw [B0] at e
  rw [e]
  exact rep_pcj w _

theorem countP_coset {f : Table → Bool} {w v : List ℤ} (hκ : (ev v)⁻¹ * ev w ∈ C)
    (hF : ∀ g ∈ C, f (toTable (ev v * g)) = f (toTable g)) :
    cbT.countP (fun c => f (compT 23 (wordT 23 gensT w) c)) = cbT.countP f := by
  have key := countP_mul_eq nodup_cbG mem_cbG (fun g => f (toTable g)) hκ hF
  rw [cbT_eq, List.countP_map, List.countP_map]
  refine Eq.trans (List.countP_congr fun g _ => ?_) (key.trans ?_)
  · rw [Function.comp_apply,
      CFSG.KS.Tbl.toTable_ext hn23 (by simp [compT]) (Rep.compT (rep_elt w) (rep_toTable hn23 g))]
    rfl
  · rfl

theorem sum_map_const {α : Type*} {l : List α} {g : α → Nat} {N : Nat} (h : ∀ x ∈ l, g x = N) :
    (l.map g).sum = l.length * N := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx), List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem cosetCount_eq {f : Table → Bool} {ws : List (List ℤ)}
    (h : ∀ m (hm : m < ws.length), cbT.countP (fun c => f (compT 23 (wordT 23 gensT ws[m]) c)) =
      cbT.countP f) :
    cosetCount 23 cbT (ws.map (wordT 23 gensT)) f = ws.length * cbT.countP f := by
  rw [cosetCount, List.map_map]
  refine sum_map_const fun w hw => ?_
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hw
  exact h m hm

theorem beq_nat (x y : Nat) : (x == y) = Nat.beq x y := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨fun h => h ▸ Nat.beq_refl x, Nat.eq_of_beq_eq_true⟩

theorem htri : ∀ i ∈ triT, i < 23 := by decide

theorem fix_tabP {X : Nat} (hX : PP 23 5 X) : fixesAll (tabP 23 5 X) triT = pfix triT X := by
  rw [fixesAll, pfix]
  exact all_congr' fun i hi => by rw [ap_tabP' hX (htri i hi), beq_nat]

theorem fix_mul {v : List ℤ} (hv : ∀ i : Fin 23, i.val ∈ triT → ev v i = i)
    (g : Equiv.Perm (Fin 23)) : fixesAll (toTable (ev v * g)) triT = fixesAll (toTable g) triT := by
  rw [Bool.eq_iff_iff, fixesAll_iff htri (rep_toTable hn23 _), fixesAll_iff htri (rep_toTable hn23 _)]
  constructor
  · intro h i hi
    apply (ev v).injective
    rw [← Equiv.Perm.mul_apply, h i hi, hv i hi]
  · intro h i hi
    rw [Equiv.Perm.mul_apply, h i hi, hv i hi]

end CertificateChecks.KernelKGC31M23

end
