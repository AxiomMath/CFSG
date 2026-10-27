
module

public import Certificates.Kernel.SchreierFam.He725K
public import Certificates.Kernel.SchreierFam.He725C
public import Certificates.Kernel.SchreierFam.He725W
public import Certificates.Kernel.SchreierFam.C23330G
public import Certificates.Kernel.SporSch.Th.GenStr
public import CFSG.Certificates.Kernel.Misc.BaseWordsSound
public import CFSG.Certificates.Kernel.RouteP.TextSplit
public import CFSG.Certificates.Kernel.Spor.BaseExt
public import CFSG.Certificates.Kernel.Spor.StrongOfFold
public import CFSG.Quasithin.Vol2.KGFactC31HeBase
public import CFSG.Sporadic.HeldB.CertPChain
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import CFSG.Certificates.Kernel.LocalCompTits.Span
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
public import CFSG.Quasithin.Vol2.KGFactC31HeRefBase
public import CFSG.Sporadic.HeldB.InnerClass
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelSchreierFam.He725.DS CFSG.SectionRank.QTK.Insp443.He.l7Der
#kss_strof CertificateChecks.KernelSchreierFam.He725.QS CFSG.Quasithin.KGC31.He.qW

namespace CertificateChecks.KernelSchreierFam.He725

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.BaseWords
  CFSG.SectionRank.QTK.Insp443.He CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Quasithin.KGC31.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CertificateChecks.KernelLC.HeFix

noncomputable abbrev U (p : Nat) : Array Nat := unpack 8330 14 p

theorem decodeWs_ofList {cs : List Char} (hne : cs ≠ []) (hc : ∀ c ∈ cs, c.toNat < 128) :
    decodeWs (String.ofList cs) =
      (CFSG.KC.RouteP.splitSepL cs [' ']).map fun p => (p.filter (· ≠ '0')).map decodeL := by
  unfold decodeWs
  have h1 : String.ofList cs ≠ "" := fun h => hne (by
    have := congrArg String.toList h
    simpa using this)
  have hs : ∀ c ∈ [' '], c.toNat < 128 := by
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    decide
  rw [if_neg h1, show (" " : String) = String.ofList [' '] from rfl,
    CFSG.KS.RouteP.splitOn_ofList_sep hc hs (by decide), List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [decodeW]

theorem ascii_of_all {cs : List Char} (h : cs.all (fun c => decide (c.toNat < 128)) = true) :
    ∀ c ∈ cs, c.toNat < 128 := fun c hc => by
  have := List.all_eq_true.1 h c hc
  simpa using this

theorem gen_eq : l7GenW = gL := by decide +kernel

theorem c_eq : c7W = cL.getD 0 [] := by
  have h : [c7W] = cL := by decide +kernel
  rw [← h]
  rfl

theorem der_eq : l7Der = dL := by
  rw [DS.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem q_eq : qW = qL := by
  rw [QS.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem gA_bind : gA.size = 3 ∧ ∀ j < 3, gA[j]! = unpack 8330 14 (LU j) :=
  He23330.letters_S

theorem wA_eqK {wd : List Int} {r : Nat}
    (h : wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 wd r = true) : wA wd = U r :=
  (wordEqK_sound gA_bind kPLU h).1

theorem word_val {j : Nat} (hj : j < 6) : wA (WJ j) = U (FJ j) := by
  have he := enAll j hj
  unfold enK at he
  simp only [Bool.and_eq_true] at he
  obtain ⟨⟨⟨hR, hN⟩, hs, hl⟩, h0⟩ := he
  have hck : ∀ i < NB j, ckW j i = true := by
    interval_cases j
    · exact ck0All
    · exact ck1All
    · exact ck2All
    · exact ck3All
    · exact ck4All
    · exact ck5All
  have hc := CFSG.KC.PermTool.wordK_chain (k := 32) (N := NB j) (S := LU) (SI := LUI)
    (R := RT j) (Nat.le_of_ble_eq_true hN) (Nat.eq_of_beq_eq_true hR)
    (fun i hi => Nat.eq_of_beq_eq_true (hck i hi))
  refine wA_eqK ?_
  unfold wordEqK
  rw [hs, hl, hc, Nat.eq_of_beq_eq_true h0, Nat.beq_refl]

theorem facts_cn : (∀ j < 4, cn (S j) = true ∧ cn (SI j) = true) ∧ cn (CC 0) = true ∧
    cn (CC 1) = true ∧ ∀ i < 4, cn (QQ i) = true := by
  have h := kCn
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun j hj => ?_, h2, h3, fun i hi => allN_spec h4 i hi⟩
  have := allN_spec h1 j hj
  simpa only [bAnd_iff] using this

theorem gL0 : gL.getD 0 [] = x7W := by
  rw [← gen_eq]
  rfl

theorem gL1 : gL.getD 1 [] = c7W ++ x7W ++ invW c7W := by
  rw [← gen_eq]
  rfl

theorem x7_eq : wA x7W = U (S 0) := by
  have h := word_val (j := 0) (by norm_num)
  rwa [show WJ 0 = x7W from gL0] at h

theorem x7i_eq : wAi x7W = U (SI 0) := by
  rw [wAi, x7_eq]
  exact (invEqK_sound (allN_spec kP 0 (by norm_num))).1

theorem c7_eq : wA c7W = U (CC 0) := by
  have h := word_val (j := 1) (by norm_num)
  rwa [show WJ 1 = c7W from c_eq.symm] at h

theorem c7i_eq : wAi c7W = U (CC 1) := by
  rw [wAi, c7_eq]
  exact (invEqK_sound kC).1

theorem qA_eq : qA = QL.map U := by
  have hl : qL.length = 4 := Nat.eq_of_beq_eq_true kQlen
  have hq : ∀ i < 4, wA (qL.getD i []) = U (QQ i) := fun i hi => by
    have h := word_val (j := 2 + i) (by omega)
    interval_cases i <;> exact h
  rw [qA, q_eq]
  apply List.ext_getElem (by simp [hl, QL])
  intro i h1 h2
  have hi : i < 4 := by simpa [hl] using h1
  rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ [] (by omega), hq i hi]
  interval_cases i <;> rfl

theorem foldPush_eq {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {T : Array (Array Nat)}
    {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP T base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hD : kO + D.length = kS) :
    D.foldl (fun S' wd => S'.push (wordA n S' (S'.map (invCand n)) wd)) (T.extract 0 kO) = T := by
  have hH := rawHeadK_sound hb hh
  have hsz : T.size = kS := hb.2.2.2.1
  have hun : ∀ j < kS, T[j]!.size = n := fun j hj => by
    rw [hb.2.2.2.2.1 j hj, unpack, Array.size_ofFn]
  unfold rawHeadOK at hH
  simp only [Bool.and_eq_true] at hH
  have hwd := hH.1.1.2
  have hext : (T.extract 0 kO).size = kO := by simp [hsz]; omega
  have hW : ∀ m < D.length,
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)[kO + m]! = D[m]! := by
    intro m hm
    rw [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, getElem!_pos _ _ (by simp; omega),
      Array.getElem_ofFn, if_neg (by simp), List.getD_eq_getElem _ _ (by simp; omega),
      getElem!_pos D m hm]
    simp
  have key : ∀ m ≤ D.length, (D.take m).foldl
      (fun S' wd => S'.push (wordA n S' (S'.map (invCand n)) wd)) (T.extract 0 kO) =
      T.extract 0 (kO + m) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        show kO + (m + 1) = kO + m + 1 by omega, ← extract_push (by omega)]
      congr 1
      have h1 := allLt_spec hwd (i := kO + m) (by omega)
      rw [hext] at h1
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1
      rcases h1 with h1 | ⟨hl, he⟩
      · omega
      · rw [hW m (by omega), getElem!_pos D m (by omega)] at hl he
        change wordA n _ (rawInvs n _) _ = _
        rw [wordA_prefix (n := n) (j := kO + m) (S := T.extract 0 (kO + m)) (T := T)
          (by rw [Array.size_extract]; omega) (by omega)
          (fun i hi => by
            rw [getElem!_pos _ i (by rw [Array.size_extract]; omega), getElem!_pos T i (by omega)]
            simp) _ hl]
        exact (eq_of_eqA_size (hun (kO + m) (by omega)) (wordA_size _) he).symm
  have e := key D.length le_rfl
  rw [List.take_length, hD, ← hsz, Array.extract_size] at e
  exact e

noncomputable abbrev SA : Array (Array Nat) := Array.ofFn (n := 4) fun j => U (S j.val)

theorem SA_size : SA.size = 4 := Array.size_ofFn

theorem SA_get : ∀ j < 4, SA[j]! = U (S j) := by
  intro j hj
  rw [getElem!_pos SA j (by rw [SA_size]; exact hj), Array.getElem_ofFn]

theorem SA_init : SA.extract 0 2 = #[U (S 0), U (S 1)] := by
  apply Array.ext (by simp [SA_size])
  intro i h1 h2
  have hi : i < 2 := by simpa using h2
  rw [Array.getElem_extract]
  simp only [Nat.zero_add, Array.getElem_ofFn]
  interval_cases i <;> simp

theorem bindsS : Binds 8330 14 He725S.S 4 2 He725S.BP SA #[0, 1] := by
  have h := kBase
  rw [bAnd_iff] at h
  exact ⟨by norm_num, by norm_num, by norm_num, SA_size, SA_get, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec h.1 t ht)⟩

theorem bindsX : Binds 8330 14 He725X.S 4 5 He725X.BP SA #[0, 1, 2, 3, 4] := by
  have h := kBase
  rw [bAnd_iff] at h
  exact ⟨by norm_num, by norm_num, by norm_num, SA_size, fun j hj => by
      rw [SA_get j hj, Nat.eq_of_beq_eq_true (allN_spec kSX j hj)], rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec h.2 t ht)⟩

theorem lx : lettersOK 3 x7W = true := by decide +kernel
theorem lc : lettersOK 3 c7W = true := by decide +kernel
theorem lci : lettersOK 3 (invW c7W) = true := by decide +kernel
theorem lcx : lettersOK 3 (c7W ++ x7W) = true := by decide +kernel
theorem lw : lettersOK 3 (c7W ++ x7W ++ invW c7W) = true := by decide +kernel

theorem w1_elt : elt (c7W ++ x7W ++ invW c7W) = elt c7W * elt x7W * (elt c7W)⁻¹ := by
  rw [elt_append lcx lci, elt_append lc lx, elt_invW lc]

theorem w1_rep :
    Rep 8330 (wA (gL.getD 1 [])) (elt c7W * elt x7W * (elt c7W)⁻¹) := by
  rw [gL1, ← w1_elt]
  exact rep_wA lw

theorem w1_eq :
    wA (gL.getD 1 []) = U (S 1) := by
  have hx := lx
  have hc := lc
  have r1 := w1_rep
  have rC : Rep 8330 (U (CC 0)) (elt c7W) := by
    rw [← c7_eq]
    exact rep_wA hc
  have rX : Rep 8330 (U (S 0)) (elt x7W) := by
    rw [← x7_eq]
    exact rep_wA hx
  have rCI : Rep 8330 (U (CC 1)) (elt c7W)⁻¹ := by
    rw [← c7i_eq]
    exact rep_wAi hc
  obtain ⟨hS0, -⟩ := facts_cn.1 0 (by norm_num)
  have hC0 := facts_cn.2.1
  have hC1 := facts_cn.2.2.1
  have e : U (S 1) = compA 8330 (compA 8330 (U (CC 0)) (U (S 0))) (U (CC 1)) := by
    rw [compA_unpack hC0 hS0, compA_unpack (canonK_pcomp hC0 hS0) hC1]
    exact congrArg U (Nat.eq_of_beq_eq_true kG1)
  have r2 : Rep 8330 (U (S 1)) (elt c7W * elt x7W * (elt c7W)⁻¹) := by
    rw [e]
    exact rep_compA (rep_compA rC rX) rCI
  exact eq_of_eqA_size (wordA_size _) (by simp [U, unpack]) ((eqA_iff r1 r2).2 rfl)

theorem l7S_eq : l7S = SA := by
  have hinit : (l7GenW.map wA).toArray = SA.extract 0 2 := by
    rw [gen_eq]
    have h0 : wA (gL.getD 0 []) = U (S 0) := by rw [gL0]; exact x7_eq
    change #[wA (gL.getD 0 []), wA (gL.getD 1 [])] = _
    rw [h0, w1_eq, SA_init]
  rw [l7S, hinit, der_eq]
  exact foldPush_eq bindsS He725S.head rfl

theorem SA_isInv {j : Nat} (hj : j < 4) : isInvA 8330 SA[j]! (invCand 8330 SA[j]!) = true := by
  have h := invEqK_sound (allN_spec kP j hj)
  rw [SA_get j hj, h.1]
  exact h.2

theorem perm_SA_mem :
    ∀ j < 4, permOfArr 8330 SA[j]! ∈ CFSG.Sporadic.HeldB.heP := by
  have hH := rawHeadK_sound bindsS He725S.head
  unfold rawHeadOK at hH
  simp only [Bool.and_eq_true] at hH
  have hwd := hH.1.1.2
  have hrep : ∀ j < 4, Rep 8330 SA[j]! (permOfArr 8330 SA[j]!) :=
    fun j hj => (rep_permOfArr (SA_isInv hj)).1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h2 : j < 2
    · have hw : lettersOK 2 (gL.getD j []) = true := by interval_cases j <;> decide +kernel
      have e : SA[j]! = wA (gL.getD j []) := by
        rw [SA_get j hj]
        interval_cases j
        · rw [gL0, x7_eq]
        · rw [w1_eq]
      have hr : Rep 8330 SA[j]! (elt (gL.getD j [])) := by
        rw [e]
        exact rep_wA (lettersOK_mono (by norm_num) hw)
      rw [Rep.unique (hrep j hj) hr]
      exact elt_mem_heP hw
    · have h1 := allLt_spec hwd (i := j) (by simpa using hj)
      have hext : (SA.extract 0 2).size = 2 := by simp [SA_size]
      rw [hext] at h1
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1
      rcases h1 with h1 | ⟨hl, he⟩
      · omega
      have hw := rep_wordA (S := SA) (Sinv := rawInvs 8330 SA)
        (gs := fun h => permOfArr 8330 SA[h]!) (j := j)
        (fun h hh => hrep h (by omega))
        (fun h hh => by
          rw [rawInvs_get (by simp; omega)]
          exact (rep_permOfArr (SA_isInv (by omega))).2) _ hl
      rw [eq_of_eqA (hrep j hj) hw he]
      have hle : Subgroup.closure (Set.range fun h : Fin j => permOfArr 8330 SA[(h : Nat)]!) ≤
          CFSG.Sporadic.HeldB.heP :=
        (Subgroup.closure_le _).2 (by
          rintro _ ⟨h, rfl⟩
          exact ih h.val h.2 (by omega))
      exact hle (Quiver.SchreierGraph.evalWord_mem_closure _ _)

theorem fix_arr5 : ∀ v < 5, (#[0, 1, 2, 3, 4] : Array Nat)[v]! = v := by
  intro v hv
  interval_cases v <;> rfl

theorem sepX :
    Sep 8330 SA #[0, 1, 2, 3, 4] := by
  intro G hG hfix
  have hle : Subgroup.closure {g : Equiv.Perm (Fin 8330) | ∃ j < SA.size, permOfArr 8330 SA[j]! = g}
      ≤ CFSG.Sporadic.HeldB.heP := (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact perm_SA_mem j hj)
  refine CFSG.Sporadic.HeldB.eq_one_of_fix_base (hle hG) fun x hx => ?_
  have hb := fix_arr5 x.val hx
  have hlt : (#[0, 1, 2, 3, 4] : Array Nat)[x.val]! < 8330 := by
    rw [hb]
    exact x.2
  have h := hfix x.val (by simpa using hx) hlt
  have e : (⟨(#[0, 1, 2, 3, 4] : Array Nat)[x.val]!, hlt⟩ : Fin 8330) = x := Fin.ext hb
  rw [e] at h
  exact h

theorem chainX :
    rawChainOK 8330 (SA.extract 0 2) SA #[0, 1, 2, 3, 4]
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 4 dL) 4 = true :=
  rawChainTK_sound bindsX He725X.head He725X.tl He725X.hst sepX He725X.hs (by norm_num)

@[expose] def finL (l : List Nat) : List (Fin 8330) :=
  l.map fun x => ⟨x % 8330, Nat.mod_lt _ (by decide)⟩

theorem sepS :
    Sep 8330 SA #[0, 1] := by
  refine sep_of_ext (by norm_num) (k := 2) (by norm_num) (by norm_num)
    (base := finL [0, 1]) (ext := finL [0, 1, 2, 3, 4]) (baseArr := #[0, 1])
    (extArr := #[0, 1, 2, 3, 4]) (by decide) rfl rfl (by decide) chainX
    (fun i hi1 hi2 => ?_) sepX
  have hi : i < 5 := by simpa [finL] using hi2
  have hi2' : 2 ≤ i := by simpa [finL] using hi1
  rw [rawLevels_get (by simpa using hi), (levelTK_sound bindsX He725X.head He725X.tl hi).2]
  have h := allN_spec kLast (i - 2) (by omega)
  have e2 : Nat.add 2 (i - 2) = i := by
    rw [Nat.add_eq]
    omega
  rw [e2] at h
  exact Nat.eq_of_beq_eq_true h

theorem part1 : ([x7W, c7W].all (lettersOK 2) && fixB bs [wA x7W] 7 && !(fixB bs [wA x7W] 1) &&
    normsW bs qA (wA x7W) (wAi x7W) && normsW bs qA (wA c7W) (wAi c7W)) = true := by
  have hl : [x7W, c7W].all (lettersOK 2) = true := by decide +kernel
  have hf := kFix
  have hn := kNorm
  simp only [bAnd_iff] at hf hn
  have e1 : [wA x7W] = [S 0].map U := by rw [x7_eq]; rfl
  rw [hl, e1, fixB_map, fixB_map, x7_eq, x7i_eq, c7_eq, c7i_eq, qA_eq, normsW_map, normsW_map]
  change (true && fixBK 8330 14 bsL [S 0] 7 && !(fixBK 8330 14 bsL [S 0] 1) &&
    normsWK 8330 14 bsL QL (S 0) (SI 0) && normsWK 8330 14 bsL QL (CC 0) (CC 1)) = true
  obtain ⟨hf1, hf2⟩ := hf
  have hf2' : fixBK 8330 14 bsL [S 0] 1 = false := by
    cases h : fixBK 8330 14 bsL [S 0] 1
    · rfl
    · rw [h] at hf2
      exact absurd hf2 Bool.false_ne_true
  rw [hf1, hf2', hn.1, hn.2]
  rfl

theorem part2 :
    (rawChainOK 8330 (arrO l7S l7GenW.length) l7S (arrBase l7B) l7Wd 4 &&
      ((rawOrbitSizes 8330 l7S (arrBase l7B)).prod == 21504)) = true := by
  have hb : arrBase l7B = #[0, 1] := by decide +kernel
  have hlen : l7GenW.length = 2 := by rw [gen_eq]; rfl
  have hW : l7Wd = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 4 dL := by
    rw [l7Wd, hlen, der_eq]
    decide +kernel
  rw [hb, hlen, hW, l7S_eq, arrO,
    rawChainTK_sound bindsS He725S.head He725S.tl He725S.hst sepS He725S.hs (by norm_num),
    rawOrbitSizesTK_sound bindsS He725S.head He725S.tl, kProd]
  rfl

end CertificateChecks.KernelSchreierFam.He725

end
