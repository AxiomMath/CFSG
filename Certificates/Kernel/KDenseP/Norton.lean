module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.SepAt
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.ReplaySound
public import CFSG.Certificates.Kernel.KDenseP.Norton.MonoAll
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125200
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125201
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125202
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125203
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125204
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125205
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125206
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125210
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125211
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125212
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125220
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125221
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125222
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125223
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125360
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125361
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125362
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125363
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125364
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125365
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125366
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125367
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125368
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125369
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125370
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125371
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125372
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125373
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125374
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125500
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125501
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125502
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125552
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125553
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125554
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125555
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125556
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125557
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125558
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125559
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125560
public import CFSG.Certificates.Kernel.KDenseP.Norton.C125561
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.Norton.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.Norton.MonoEChk1

public section

namespace CertificateChecks.KernelKDenseP.Norton

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Norton CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.Gen11
  CFSG.AGLEmbedding.Norton.Gen13

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.NRTM.MT = true := by
  kd_monoTabL CFSG.KD.NRTME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.NRTM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

open Lean in
macro "kd_nrt% " pre:ident eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3B_sound CertificateChecks.KernelKDenseP.Norton.data_ok $eqs $nes (by quickRfl)
      (S := $(n "S")) (fun x hx => by interval_cases x <;> rfl) (CH := $(n "CH"))
      (nch := kd_count% $pre $(mkIdent `t)) (IT := $(n "IT")) (by kd_allE $pre $(mkIdent `t))
      (by quickRfl) (by quickRfl))

theorem nrt_loc (P : Prs) : ∀ (S S' : ℕ → St) (c : ℕ), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
    S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) → CFSG.KD.NRT.chkP P S c = CFSG.KD.NRT.chkP P S' c := by
  intro S S' c h3 h4
  unfold CFSG.KD.NRT.chkP chunkOKN
  rw [h3, h4]

theorem nrt_prod (P : Prs) : ∀ (S : ℕ → St) (c : ℕ), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
    CFSG.KD.NRT.chkP P S c = stEqN 4 (CFSG.KD.NRT.runP P (f20 c (nat_lit 0)) c (S (f20 c (nat_lit 3))))
      (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold CFSG.KD.NRT.chkP chunkOKN CFSG.KD.NRT.runP
  rw [h]

open Lean in
macro "kd_nrtKC% " pre:ident w?:(num)? : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  let (s0, w) ← match w? with
    | some w => pure ((n "S0" : Term), w)
    | none => pure (← `(CFSG.KD.KDF.I), Syntax.mkNumLit "3")
  `(replay_sound (run := $(n "rn")) (chk := CFSG.KD.NRT.chkP $(n "P"))
      (fun S S' c h3 h4 => nrt_loc _ S S' c h3 h4) (fun S c h => nrt_prod _ S c h)
      (CH := $(n "CH")) (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf"))
      (S0 := $s0) (w := $w) (ng := kd_count% $pre $(mkIdent `u))
      (nch := kd_count% $pre $(mkIdent `CH)) (by kd_allE $pre $(mkIdent `u)) (by quickRfl))

open Lean in
macro "kd_nrtK% " pre:ident w?:(num)? eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  match w? with
  | some w =>
    `(tp3B_sound CertificateChecks.KernelKDenseP.Norton.data_ok $eqs $nes (by quickRfl)
      (S := rlS $(n "rn") $(n "CH") $(n "PRf") $(n "S0") $w)
      (fun x hx => (rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans (by interval_cases x <;> rfl))
      (CH := $(n "CH")) (nch := kd_count% $pre $(mkIdent `CH)) (IT := $(n "IT"))
      (kd_nrtKC% $pre $w) (by quickRfl) (by quickRfl))
  | none =>
    `(tp3B_sound CertificateChecks.KernelKDenseP.Norton.data_ok $eqs $nes (by quickRfl)
      (S := rlS $(n "rn") $(n "CH") $(n "PRf") CFSG.KD.KDF.I 3) (fun x hx => rlS_lt hx)
      (CH := $(n "CH")) (nch := kd_count% $pre $(mkIdent `CH)) (IT := $(n "IT"))
      (kd_nrtKC% $pre) (by quickRfl) (by quickRfl))

theorem agreeAll_append (a b : List (List Native.Gen × List Native.Gen)) :
    agreeAll (a ++ b) = (agreeAll a && agreeAll b) := List.all_append

theorem c125200 : agreeAll qOrderPairs = true := (kd_nrtK% CFSG.KD.NRT.c125200 qOrderPairs []).1

theorem c125201 : agreeAll qCommPairs = true ∧ agreeAll wInvPairs = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c125201 e125201 []).1
  rwa [e125201, agreeAll_append, Bool.and_eq_true] at h

theorem c125202 : agreeAll wQSelfPairs = true ∧ agreeAll wQOtherPairs = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c125202 e125202 []).1
  rwa [e125202, agreeAll_append, Bool.and_eq_true] at h

theorem c125203 : agreeAll (nodeQPairs 0) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125203 (nodeQPairs 0) []).1
theorem c125204 : agreeAll (nodeQPairs 1) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125204 (nodeQPairs 1) []).1
theorem c125205 : agreeAll (nodeQPairs 2) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125205 (nodeQPairs 2) []).1

theorem c125206 : EdgeNoncomm.moveCheck (qW 0) (aV ()) = true ∧
    EdgeNoncomm.moveCheck (qW 1) (aV ()) = true ∧ EdgeNoncomm.moveCheck (qW 2) (aV ()) = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125206 [] n125206).2
  exact ⟨moveCheck_of_sepL (h (qW 0, []) (by simp [n125206])),
    moveCheck_of_sepL (h (qW 1, []) (by simp [n125206])),
    moveCheck_of_sepL (h (qW 2, []) (by simp [n125206]))⟩

theorem c125210 : agreeAll sevenOrderPairs = true :=
  (kd_nrtK% CFSG.KD.NRT.c125210 sevenOrderPairs []).1

theorem c125211 : agreeAll sevenCommPairs = true ∧ agreeAll sevenActPairs = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c125211 e125211 []).1
  rwa [e125211, agreeAll_append, Bool.and_eq_true] at h

theorem c125212 : EdgeNoncomm.moveCheck dW (aV ()) = true ∧ EdgeNoncomm.moveCheck zW (aV ()) = true ∧
    (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeWord k) (aV ())) = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c125212 [] n125212).2
  have hd := h (tauS dW) (by simp [n125212])
  refine ⟨moveCheck_of_suffix (w := dW) (s := [.xi, .tau]) hd.1 hd.2.1 hd.2.2, moveCheck_of_sepL (h (zW, []) (by simp [n125212])),
    List.all_eq_true.2 fun k hk => moveCheck_of_sepL (h (sevenNeWord k, []) ?_)⟩
  exact List.mem_append_right _ (List.mem_map.2 ⟨k, hk, rfl⟩)

theorem c125220 : agreeAll sevenXPairs = true := (kd_nrtK% CFSG.KD.NRT.c125220 sevenXPairs []).1

theorem c125221 : agreeAll sevenYPairs = true ∧ agreeAll sevenIPairs = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125221 e125221 []).1
  rwa [e125221, agreeAll_append, Bool.and_eq_true] at h

theorem c125222 : agreeAll sevenGPairs = true := (kd_nrtK% CFSG.KD.NRT.c125222 sevenGPairs []).1

theorem c125223 :
    (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeXWord k) (aV ())) = true ∧
      (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeYWord k) (aV ())) = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c125223 [] n125223).2
  refine ⟨List.all_eq_true.2 fun k hk => ?_,
    List.all_eq_true.2 fun k hk => moveCheck_of_sepL (h (sevenNeYWord k, []) ?_)⟩
  · have hx := h (tauS (sevenNeXWord k)) (List.mem_append_left _ (List.mem_map.2 ⟨k, hk, rfl⟩))
    exact moveCheck_of_suffix (w := sevenNeXWord k) (s := [.xi, .tau]) hx.1 hx.2.1 hx.2.2
  · exact List.mem_append_right _ (List.mem_map.2 ⟨k, hk, rfl⟩)

theorem c125360 : agreeAll tbOrderPairs = true ∧ agreeAll tbWOrderPairs = true ∧
    (EdgeNoncomm.moveCheck tbW (aV ()) || EdgeNoncomm.moveCheck tbW (bV ()) ||
      EdgeNoncomm.moveCheck tbW (wV ())) = true := by
  obtain ⟨he, hn⟩ := kd_nrtK% CFSG.KD.NRT.c125360 e125360 n125360
  rw [e125360, agreeAll_append, Bool.and_eq_true] at he
  refine ⟨he.1, he.2, ?_⟩
  have ht := hn (tauS tbW) (List.mem_singleton.2 rfl)
  rw [moveCheck_of_suffix (w := tbW) (s := [.xi, .tau]) ht.1 ht.2.1 ht.2.2]
  rfl

theorem c125361 : agreeAll tbCentralPairs = true :=
  (kd_nrtK% CFSG.KD.NRT.c125361 tbCentralPairs []).1
theorem c125362 : agreeAll (tbChainPairs [0]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125362 (tbChainPairs [0]) []).1
theorem c125363 : agreeAll (tbChainPairs [1, 10]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125363 (tbChainPairs [1, 10]) []).1
theorem c125364 : agreeAll (tbChainPairs [2, 9]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125364 (tbChainPairs [2, 9]) []).1
theorem c125365 : agreeAll (tbChainPairs [3, 8]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125365 (tbChainPairs [3, 8]) []).1
theorem c125366 : agreeAll (tbChainPairs [4, 7]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125366 (tbChainPairs [4, 7]) []).1
theorem c125367 : agreeAll (tbChainPairs [5, 6]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125367 (tbChainPairs [5, 6]) []).1
theorem c125368 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [0, 1, 2]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125368 33 (tbActPairs tbB1 tbXRows tbC1 [0, 1, 2]) []).1
theorem c125369 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [3, 4, 5]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125369 24 (tbActPairs tbB1 tbXRows tbC1 [3, 4, 5]) []).1
theorem c125370 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [6, 7, 8]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125370 27 (tbActPairs tbB1 tbXRows tbC1 [6, 7, 8]) []).1
theorem c125371 : agreeAll (tbActPairs tbB1 tbXRows tbC1 [9, 10, 11]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125371 33 (tbActPairs tbB1 tbXRows tbC1 [9, 10, 11]) []).1
theorem c125372 : agreeAll (tbActPairs tbB2 tbYRows tbC2 [0, 1, 2, 3]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125372 15 (tbActPairs tbB2 tbYRows tbC2 [0, 1, 2, 3]) []).1
theorem c125373 : agreeAll (tbActPairs tbB2 tbYRows tbC2 [4, 5, 6, 7]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125373 18 (tbActPairs tbB2 tbYRows tbC2 [4, 5, 6, 7]) []).1
theorem c125374 : agreeAll (tbActPairs tbB2 tbYRows tbC2 [8, 9, 10, 11]) = true :=
  (kd_nrtK% CFSG.KD.NRT.c125374 36 (tbActPairs tbB2 tbYRows tbC2 [8, 9, 10, 11]) []).1

theorem c125500 : thirteenOrderCheck () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125500 e125500 []).1
  simp only [e125500, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  simp only [thirteenOrderCheck, eqWords3C_eq_agree]
  exact h

theorem c125501 : thirteenRelCheck () = true := by
  have hc := kd_nrtKC% CFSG.KD.NRT.c125501
  have h := tp3B_eqs data_ok e125501 n125501 (by quickRfl)
    (S := rlS CFSG.KD.NRT.c125501.rn CFSG.KD.NRT.c125501.CH CFSG.KD.NRT.c125501.PRf CFSG.KD.KDF.I 3)
    (fun x hx => rlS_lt hx) (CH := CFSG.KD.NRT.c125501.CH)
    (nch := kd_count% CFSG.KD.NRT.c125501 CH) (IT := CFSG.KD.NRT.c125501.IT) hc (by quickRfl)
    (by quickRfl)
  simp only [e125501, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have hit := itemL data_ok (p := tri e125501 n125501) (by quickRfl)
    (S := rlS CFSG.KD.NRT.c125501.rn CFSG.KD.NRT.c125501.CH CFSG.KD.NRT.c125501.PRf CFSG.KD.KDF.I 3)
    (fun x hx => rlS_lt hx) (CH := CFSG.KD.NRT.c125501.CH)
    (nch := kd_count% CFSG.KD.NRT.c125501 CH) (IT := CFSG.KD.NRT.c125501.IT) hc (by quickRfl) 24
    (by decide +kernel)
  have hs := itemL_sepAt data_ok (p := tri e125501 n125501) (by quickRfl)
    (S := rlS CFSG.KD.NRT.c125501.rn CFSG.KD.NRT.c125501.CH CFSG.KD.NRT.c125501.PRf CFSG.KD.KDF.I 3)
    (fun x hx => rlS_lt hx) (CH := CFSG.KD.NRT.c125501.CH)
    (nch := kd_count% CFSG.KD.NRT.c125501 CH) (IT := CFSG.KD.NRT.c125501.IT) hc (by quickRfl) 24
    (by decide +kernel) (by decide +kernel)
    (r := 576) (by norm_num) (by decide +kernel)
  have e1 : (tri e125501 n125501).getD 24 ([], []) = (thirteenZ, []) := rfl
  have e2 : CFSG.KD.NRT.c125501.IT[24]! % 4 = 1 := by decide +kernel
  rw [e1] at hit hs
  rw [e2] at hs
  obtain ⟨v1, -, -⟩ := hit
  simp only [thirteenRelCheck, eqWords3C_eq_agree, Bool.and_eq_true]
  refine ⟨by simp only [and_assoc] at h ⊢; exact h, ?_⟩
  unfold neXC thirteenP
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨v1, fun g hg => absurd hg List.not_mem_nil⟩, diffX_of_res5 hs⟩

theorem c125502 : elevenEligibleCheck () = true := by
  obtain ⟨h, hn⟩ := kd_nrtK% CFSG.KD.NRT.c125502 e125502 n125502
  simp only [e125502, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have ht := hn (tauS gen11W0) (List.mem_singleton.2 rfl)
  have hm := moveCheck_of_suffix (w := gen11W0) (s := [.xi, .tau]) ht.1 ht.2.1 ht.2.2
  simp only [elevenEligibleCheck, agreeC_eq, hm, Bool.true_or, Bool.and_true, Bool.and_eq_true,
    and_assoc] at h ⊢
  exact h

theorem c125552 : d13OrderCheck () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125552 e125552 []).1
  simp only [e125552, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [d13OrderCheck, agreeC_eq, Bool.and_eq_true, and_assoc] at h ⊢
  exact h

theorem c125553 : d13CommCheck () = true := by
  obtain ⟨h, hn⟩ := kd_nrtK% CFSG.KD.NRT.c125553 e125553 n125553
  simp only [e125553, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have ht := hn (tauS genD13W1) (List.mem_singleton.2 rfl)
  have hm := moveCheck_of_suffix (w := genD13W1) (s := [.xi, .tau]) ht.1 ht.2.1 ht.2.2
  simp only [d13CommCheck, agreeC_eq, hm, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    and_assoc] at h ⊢
  exact h

theorem c125554 : d13X1xCheck () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125554 e125554 []).1
  simp only [e125554, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

theorem c125555 : d13X1yCheck () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125555 e125555 []).1
  simp only [e125555, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

theorem c125556 : d13X2xCheck () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125556 e125556 []).1
  simp only [e125556, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

theorem c125557 : d13X2yCheck () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125557 e125557 []).1
  simp only [e125557, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

theorem c125558 : d13ANorm1Check () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125558 e125558 []).1
  simp only [e125558, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [d13ANorm1Check, agreeC_eq, Bool.and_eq_true, and_assoc] at h ⊢
  exact h

theorem c125559 : d13ANorm2Check () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125559 e125559 []).1
  simp only [e125559, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [d13ANorm2Check, agreeC_eq, Bool.and_eq_true, and_assoc] at h ⊢
  exact h

theorem c125560 : thirteenEligibleCheck () = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c125560 e125560 []).1
  simp only [e125560, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [thirteenEligibleCheck, agreeC_eq, Bool.and_eq_true, and_assoc] at h ⊢
  exact h

theorem c125561 : d13ANorm4Check () = true := by
  have h := (kd_nrt% CFSG.KD.NRT.c125561 e125561 []).1
  simp only [e125561, agreeAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [d13ANorm4Check, agreeC_eq, Bool.and_eq_true, and_assoc] at h ⊢
  exact h

end CertificateChecks.KernelKDenseP.Norton

end
