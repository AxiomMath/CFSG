module

public import Certificates.Kernel.KDenseP.Tp3L
public import Certificates.Kernel.KDenseP.AgreeOf
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoAll
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R13699
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136100
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136101
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136102
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136103
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136104
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136105
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136106
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136107
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136108
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136109
public import Certificates.Kernel.KDenseP.MonFiveCw
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136112
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136113
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136114
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136115
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136116
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136117
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136118
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136119
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136120
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136121
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136122
public import CFSG.Certificates.Kernel.KDenseP.MonFive.R136123
public import CFSG.Certificates.Kernel.KDenseP.MonFive.LookChk
public import CFSG.Certificates.Kernel.KDenseP.LookSound
public import CFSG.Certificates.Kernel.KDenseP.ReplaySound
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoEChk1
public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoEChk2
public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoEChk3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.MonFive

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster.AxisCount CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive
  CFSG.KC.KDenseP.TwoPoint

set_option maxRecDepth 100000

theorem tp3_exact
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs nes : List (List Native.Gen × List Native.Gen)) (hL : pairsLetterOK (tp3 eqs nes) = true)
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x) {CH : ℕ → ℕ} {nch : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT (Y443.words (tp3 eqs nes)) S (CH k) = true)
    (hplan : planOKP (Y443.words (tp3 eqs nes)) CH nch IT = true)
    (hwk : wkOK IT (tpWK eqs.length nes.length) = true) :
    agreeAll eqs = true ∧ ∀ e ∈ nes, e.2 = [] → EdgeNoncomm.moveCheck e.1 (aV ()) = true := by
  obtain ⟨hl, hk⟩ := wkOK_spec hwk
  rw [tpWK_length] at hl
  have it := itemL hd hL hS hc hplan
  have heq := (tp3L_sound hd eqs nes hL hS hc hplan hwk).1
  constructor
  · refine agreeAll_of_wordLin (fun e he => ?_) heq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 0 + j < IT.length := by rw [hl]; omega
    obtain ⟨v1, v2, -, -⟩ := it _ ht
    rw [tp3_getD_eq eqs nes (by norm_num) hj] at v1 v2
    exact ⟨v1, v2⟩
  · intro e he h2
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have ht : eqs.length * 3 + j < IT.length := by rw [hl]; omega
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWK_getD_ne hj] at k1 k2
    obtain ⟨v1, -, -, n⟩ := it _ ht
    rw [tp3_getD_ne eqs nes hj] at v1 n
    obtain ⟨k, hk', hne⟩ := n k2
    rw [k1, h2] at hne
    have hw : CertificateChecks.KernelKDense.wit 0 = aV () := ite_eq_left rfl
    have hn : Native.evalWord [] (aV ()) = aV () := rfl
    rw [hw, hn] at hne
    unfold EdgeNoncomm.moveCheck
    rw [Bool.and_eq_true, List.all_eq_true]
    exact ⟨v1, moveCheckAux_of_res5 hk' hne⟩

@[expose] def ixOK (IXf : ℕ → ℕ) (nu nr : ℕ) : Bool := (List.range nr).all fun k => Nat.blt (IXf k) nu

theorem ix_lt {IXf : ℕ → ℕ} {nu nr : ℕ} (h : ixOK IXf nu nr = true) : ∀ k < nr, IXf k < nu :=
  fun k hk => by
    have e := List.all_eq_true.1 h k (List.mem_range.2 hk)
    rwa [Nat.blt_eq] at e

theorem chunks_of_ix {P : ℕ → Prop} {CH IXf : ℕ → ℕ} {nu nr : ℕ} (hu : ∀ k < nu, P (CH k))
    (hix : ∀ k < nr, IXf k < nu) : ∀ k < nr, P (CH (IXf k)) := fun k hk => hu _ (hix k hk)

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.M5RM.MT = true := by
  kd_monoTabL CFSG.KD.M5RME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.M5RM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem look_eq : CFSG.KD.M5RL.look = fun k => findIdx k CFSG.KD.M5RM.MT.keys :=
  funext fun l => lookT_eq CFSG.KD.M5RL.tab_ok CFSG.KD.M5RL.len_ok l

theorem m5_loc (p : List (List Native.Gen × List Native.Gen)) :
    ∀ (S S' : ℕ → St) (c : ℕ), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) →
      CFSG.KD.M5RL.chkRL p S c = CFSG.KD.M5RL.chkRL p S' c := by
  intro S S' c h3 h4
  unfold CFSG.KD.M5RL.chkRL chunkOKNL
  rw [h3, h4]

theorem m5_prod (p : List (List Native.Gen × List Native.Gen)) :
    ∀ (S : ℕ → St) (c : ℕ), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      CFSG.KD.M5RL.chkRL p S c =
        stEqN 4 (CFSG.KD.M5RL.runCL p c (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold CFSG.KD.M5RL.chkRL chunkOKNL
  rw [h]
  rfl

theorem snd_of_mem_nesOf {lo n : ℕ} {e : List Native.Gen × List Native.Gen}
    (h : e ∈ nesOf lo n) : e.2 = [] := by
  unfold nesOf at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, -, hi⟩ := h
  split at hi
  · exact absurd hi (by simp)
  · rw [← Option.some_inj.1 hi]

theorem repMovesOf_of {lo n : ℕ}
    (h : ∀ e ∈ nesOf lo n, EdgeNoncomm.moveCheck e.1 (aV ()) = true) : repMovesOf lo n = true := by
  unfold repMovesOf
  rw [List.all_eq_true]
  intro i hi
  unfold repMove
  rw [Bool.or_eq_true]
  by_cases hk : (fiveReps[lo + i]!).kind = true
  · exact Or.inl hk
  · have hk' : (fiveReps[lo + i]!).kind = false := Bool.eq_false_iff.2 hk
    have hm : ((fiveReps[lo + i]!).wa ++ (fiveReps[lo + i]!).wb, ([] : List Native.Gen)) ∈
        nesOf lo n := by
      unfold nesOf
      rw [List.mem_filterMap]
      exact ⟨i, hi, by rw [ite_eq_right (by rw [hk']; exact Bool.false_ne_true)]⟩
    exact Or.inr (h ((fiveReps[lo + i]!).wa ++ (fiveReps[lo + i]!).wb, []) hm)

open Lean in
macro "kd_m5p% " pre:ident w?:(num)? eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  let (s0, w, lt) ← match w? with
    | some w => pure ((n "S0" : Term), w, ← `(fun x hx =>
        (CFSG.KC.KDenseP.rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans
          (by interval_cases x <;> rfl)))
    | none => pure (← `(CFSG.KD.KDF.I), Syntax.mkNumLit "3",
        ← `(fun x hx => CFSG.KC.KDenseP.rlS_lt hx))
  `(tp3_exact CertificateChecks.KernelKDenseP.MonFive.data_ok $eqs $nes (by quickRfl)
      (S := CFSG.KC.KDenseP.rlS (CFSG.KD.M5RL.runCL $(n "P")) $(n "CH") $(n "PRf") $s0 $w)
      $lt (CH := $(n "CHI"))
      (nch := kd_count% $pre $(mkIdent `IX)) (IT := $(n "IT"))
      (fun k hk => CFSG.KC.KDenseP.chunkOKN_of_look CertificateChecks.KernelKDenseP.MonFive.look_eq
        (chunks_of_ix (CH := $(n "CH")) (IXf := $(n "IXf")) (P := fun c => CFSG.KC.KDenseP.chunkOKNL 4 2 5
            CFSG.KD.KDF.F CFSG.KD.M5RM.MT CFSG.KD.M5RL.look (Y443.words (tp3 $eqs $nes))
            (CFSG.KC.KDenseP.rlS (CFSG.KD.M5RL.runCL $(n "P")) $(n "CH") $(n "PRf") $s0 $w) c = true)
          (nu := kd_count% $pre $(mkIdent `CH))
          (CFSG.KC.KDenseP.replay_sound (m5_loc $(n "P")) (m5_prod $(n "P")) (CH := $(n "CH"))
            (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf")) (S0 := $s0) (w := $w)
            (ng := kd_count% $pre $(mkIdent `u)) (by kd_allE $pre $(mkIdent `u)) (by quickRfl))
          (ix_lt (IXf := $(n "IXf")) (by quickRfl)) k hk))
      (by quickRfl) (by quickRfl))

theorem c13699 : agreeAll (relSeg 0 13) = true := (kd_m5p% CFSG.KD.M5R.c13699 (relSeg 0 13) []).1
theorem c136100 : agreeAll (relSeg 13 12) = true :=
  (kd_m5p% CFSG.KD.M5R.c136100 165 (relSeg 13 12) []).1
theorem c136101 : agreeAll (relSeg 25 10) = true :=
  (kd_m5p% CFSG.KD.M5R.c136101 186 (relSeg 25 10) []).1
theorem g136102 : agreeAll (relSeg 35 2 ++ relSeg 39 2) = true :=
  (kd_m5p% CFSG.KD.M5R.c136102 117 (relSeg 35 2 ++ relSeg 39 2) []).1
theorem g136103 : agreeAll (relSeg 41 1 ++ relSeg 44 3) = true :=
  (kd_m5p% CFSG.KD.M5R.c136103 135 (relSeg 41 1 ++ relSeg 44 3) []).1
theorem c136104 : agreeAll (relSeg 47 10) = true :=
  (kd_m5p% CFSG.KD.M5R.c136104 180 (relSeg 47 10) []).1
theorem c136105 : agreeAll (relSeg 57 11) = true :=
  (kd_m5p% CFSG.KD.M5R.c136105 (relSeg 57 11) []).1
theorem c136106 : agreeAll (relTail 68) = true := (kd_m5p% CFSG.KD.M5R.c136106 (relTail 68) []).1
theorem c136102 : agreeAll (relSeg 35 6) = true :=
  (relSeg35_ok c13699 c136100 c136101 g136102 g136103 c136104 c136105 c136106).1
theorem c136103 : agreeAll (relSeg 41 6) = true :=
  (relSeg35_ok c13699 c136100 c136101 g136102 g136103 c136104 c136105 c136106).2

theorem rel_ok : agreeAll relEqs = true :=
  relDrop_ok (a := 0) (b := 13) c13699 (relDrop_ok (a := 13) (b := 12) c136100
    (relDrop_ok (a := 25) (b := 10) c136101 (relDrop_ok (a := 35) (b := 6) c136102
      (relDrop_ok (a := 41) (b := 6) c136103 (relDrop_ok (a := 47) (b := 10) c136104
        (relDrop_ok (a := 57) (b := 11) c136105 c136106))))))

theorem g136107 : agreeAll (normPick 0 [0, 1, 4, 6]) = true :=
  (kd_m5p% CFSG.KD.M5R.c136107 129 (normPick 0 [0, 1, 4, 6]) []).1
theorem g136108 : agreeAll (normPick 1 [0, 1, 4, 6]) = true :=
  (kd_m5p% CFSG.KD.M5R.c136108 126 (normPick 1 [0, 1, 4, 6]) []).1
theorem g136109 : agreeAll (normPick 2 [0, 1, 4, 6]) = true :=
  (kd_m5p% CFSG.KD.M5R.c136109 135 (normPick 2 [0, 1, 4, 6]) []).1

theorem normSeg_ok (lo n : ℕ) : agreeAll (normSeg lo n) = true :=
  normSub_ok rel_ok g136107 g136108 g136109 fun _ hp =>
    List.mem_of_mem_drop (List.mem_of_mem_take hp)

theorem c136107 : agreeAll (normSeg 0 5) = true := normSeg_ok 0 5
theorem c136108 : agreeAll (normSeg 5 6) = true := normSeg_ok 5 6
theorem c136109 : agreeAll (normSeg 11 6) = true := normSeg_ok 11 6
theorem c136110 : agreeAll (normSeg 17 6) = true := normSeg_ok 17 6
theorem c136111 : agreeAll (normTail 23) = true :=
  normSub_ok rel_ok g136107 g136108 g136109 fun _ hp => List.mem_of_mem_drop hp
theorem c136112 : EdgeNoncomm.moveCheck fiveGens[8]! (aV ()) = true :=
  (kd_m5p% CFSG.KD.M5R.c136112 [] [(fiveGens[8]!, [])]).2 (fiveGens[8]!, [])
    (List.mem_singleton.2 rfl) rfl

theorem c136113 : agreeAll (repEqsOf 0 3) = true ∧ repMovesOf 0 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136113 270 (repEqsOf 0 3) (nesOf 0 3))
theorem c136114 : agreeAll (repEqsOf 3 3) = true ∧ repMovesOf 3 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136114 282 (repEqsOf 3 3) (nesOf 3 3))
theorem c136115 : agreeAll (repEqsOf 6 3) = true ∧ repMovesOf 6 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136115 272 (repEqsOf 6 3) (nesOf 6 3))
theorem c136116 : agreeAll (repEqsOf 9 3) = true ∧ repMovesOf 9 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136116 291 (repEqsOf 9 3) (nesOf 9 3))
theorem c136117 : agreeAll (repEqsOf 12 3) = true ∧ repMovesOf 12 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136117 268 (repEqsOf 12 3) (nesOf 12 3))
theorem c136118 : agreeAll (repEqsOf 15 3) = true ∧ repMovesOf 15 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136118 282 (repEqsOf 15 3) (nesOf 15 3))
theorem c136119 : agreeAll (repEqsOf 18 2) = true ∧ repMovesOf 18 2 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136119 200 (repEqsOf 18 2) (nesOf 18 2))
theorem c136120 : agreeAll (repEqsOf 20 2) = true ∧ repMovesOf 20 2 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136120 203 (repEqsOf 20 2) (nesOf 20 2))
theorem c136121 : agreeAll (repEqsOf 22 3) = true ∧ repMovesOf 22 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136121 305 (repEqsOf 22 3) (nesOf 22 3))
theorem c136122 : agreeAll (repEqsOf 25 3) = true ∧ repMovesOf 25 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136122 284 (repEqsOf 25 3) (nesOf 25 3))
theorem c136123 : agreeAll (repEqsOf 28 3) = true ∧ repMovesOf 28 3 = true :=
  (fun h => ⟨h.1, repMovesOf_of fun e he => h.2 e he (snd_of_mem_nesOf he)⟩)
    (kd_m5p% CFSG.KD.M5R.c136123 306 (repEqsOf 28 3) (nesOf 28 3))

end CertificateChecks.KernelKDenseP.MonFive

end
