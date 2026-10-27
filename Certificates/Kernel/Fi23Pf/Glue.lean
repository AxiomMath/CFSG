module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi23PerfInputs
import Certificates.Kernel.Fi23Pf.Checks
import Certificates.Kernel.Fi23M.Facts
import Certificates.Kernel.Fi23M.WGlue
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Spor.Mat3Sound
import CFSG.Certificates.Kernel.DecTextSound
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.Common.StrChars
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic
public import CFSG.Sporadic.Fi23.Setup
public import CFSG.F3.SepSpec

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Pf

open CFSG.F3.Native CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CertificateChecks.KernelWP CFSG.KS.Mat3 CFSG.KD.Fi23Pf

#ks_chars_of CertificateChecks.KernelFi23Pf.Txt CFSG.EvenSporadicStandard.Solomon78.fi23PerfTxt

noncomputable def LS : List (List Char) := Txt.chars.splitOn '\n'

noncomputable def GS : List (List Nat) := ((LS.drop 1).take 12).map CFSG.KC.DecText.natsK

noncomputable def XS : List Nat := CFSG.KC.DecText.natsK (LS.getD 13 [])

noncomputable def YS : List Nat := CFSG.KC.DecText.natsK (LS.getD 14 [])

theorem lines_eq : CFSG.EvenSporadicStandard.Solomon78.fi23PerfLines = LS.map String.ofList := by
  have e : ("\n" : String) = String.singleton '\n' := rfl
  rw [CFSG.EvenSporadicStandard.Solomon78.fi23PerfLines, Txt.eq, e, LS]
  exact CFSG.KC.Str.splitOn_ofList Txt.chars '\n'

theorem parseWord_ofList {cs : List Char} (h : CFSG.KC.DecText.digitsOK cs = true) :
    CFSG.EvenSporadicStandard.Solomon78.parseWord (String.ofList cs) = CFSG.KC.DecText.natsK cs := by
  have e := CFSG.KC.DecText.natsOf_ofList h
  unfold natsOf at e
  have e2 := congrArg Array.toList e
  rw [Array.toList_map, List.toList_toArray, List.toList_toArray] at e2
  rw [← e2]
  unfold CFSG.EvenSporadicStandard.Solomon78.parseWord
  congr 2

theorem getElem!_LS (i : Nat) (hi : i < LS.length) :
    (LS.map String.ofList)[i]! = String.ofList (LS.getD i []) := by
  rw [getElem!_pos _ i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem len_LS : 16 ≤ LS.length := by decide +kernel

theorem M_eq : CFSG.EvenSporadicStandard.Solomon78.fi23PerfM = 12 := by
  rw [CFSG.EvenSporadicStandard.Solomon78.fi23PerfM, lines_eq, getElem!_LS 0 (by have := len_LS; omega),
    CFSG.KC.Str.toNat!_ofList (by decide +kernel)
      (List.all_eq_true.1 (by quickRfl : (LS.getD 0 []).all Char.isDigit = true))]
  decide +kernel

theorem gens_eq : CFSG.EvenSporadicStandard.Solomon78.fi23PerfGens = GS := by
  rw [CFSG.EvenSporadicStandard.Solomon78.fi23PerfGens, lines_eq, M_eq, ← List.map_drop,
    ← List.map_take, List.map_map]
  have hd : ((LS.drop 1).take 12).all CFSG.KC.DecText.digitsOK = true := by quickRfl
  rw [GS]
  exact List.map_congr_left fun l hl => parseWord_ofList (List.all_eq_true.1 hd l hl)

theorem x_eq : CFSG.EvenSporadicStandard.Solomon78.fi23PerfX = XS := by
  rw [CFSG.EvenSporadicStandard.Solomon78.fi23PerfX, M_eq, lines_eq,
    getElem!_LS 13 (by have := len_LS; omega), XS]
  exact parseWord_ofList (by quickRfl)

theorem y_eq : CFSG.EvenSporadicStandard.Solomon78.fi23PerfY = YS := by
  rw [CFSG.EvenSporadicStandard.Solomon78.fi23PerfY, M_eq, lines_eq,
    getElem!_LS 14 (by have := len_LS; omega), YS]
  exact parseWord_ofList (by quickRfl)

noncomputable abbrev gm (w : List Nat) : Matrix (Fin 253) (Fin 253) (ZMod 3) := (w.map genMat).prod

theorem gm_append (u v : List Nat) : gm (u ++ v) = gm u * gm v := by
  unfold gm
  rw [List.map_append, List.prod_append]

theorem gm_flatten : ∀ L : List (List Nat), gm L.flatten = (L.map gm).prod
  | [] => rfl
  | u :: L => by rw [List.flatten_cons, gm_append, gm_flatten L, List.map_cons, List.prod_cons]

def dW7 : List Nat := (List.replicate 7 dWord).flatten

def cw (g : List Nat) : List Nat :=
  g ++ dW7 ++ CFSG.EvenSporadicStandard.Solomon78.invLetters g

structure Facts (X : Array W) (u : List Nat) : Prop where
  size : X.size = 253
  wf : RowsWF (toVM X)
  canon : canonM 253 (toVM X) = true
  mat : toMatW 253 X = gm u

theorem Facts.mul {X Y : Array W} {u v : List Nat} (hX : Facts X u) (hY : Facts Y v) :
    Facts (mulW 253 X Y) (u ++ v) :=
  ⟨by rw [mulW_size, hX.size], RowsWF.mulW hX.wf hY.wf, canonM_mulW hX.size hX.wf hY.canon,
    by rw [toMatW_mulW hX.size hX.wf hY.wf, hX.mat, hY.mat, gm_append]⟩

theorem facts_wm (w : List Nat) (hw : ∀ x ∈ w, x < 2) :
    Facts (CFSG.EvenSporadicStandard.Solomon78.wm w) w := by
  obtain ⟨h1, h2, h3⟩ := prodW_facts w hw
  exact ⟨h1, h2, canonM_prodW w hw, h3⟩

theorem gm_rep (u : List Nat) : ∀ n, gm (List.replicate n u).flatten = gm u ^ n
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, gm_append, gm_rep u n, pow_succ']

theorem facts_D : Facts matD dW7 := by
  obtain ⟨h1, h2, h3⟩ := matD_facts
  have hc : canonM 253 (toVM matD) = true := by
    unfold matD
    exact canonM_powW (prodW_facts dWord dWord_lt).2.1 (canonM_prodW dWord dWord_lt) 7
  refine ⟨h1, h2, hc, ?_⟩
  rw [h3, dW7, gm_rep]

theorem invLetters_lt : ∀ g : List Nat, ∀ x ∈ CFSG.EvenSporadicStandard.Solomon78.invLetters g, x < 2
  | [] => fun _ h => absurd h List.not_mem_nil
  | y :: g => by
    intro x hx
    rw [CFSG.EvenSporadicStandard.Solomon78.invLetters, List.mem_append] at hx
    rcases hx with hx | hx
    · exact invLetters_lt g x hx
    · split at hx <;> simp at hx <;> omega

theorem facts_conj (g : List Nat) (hg : ∀ x ∈ g, x < 2) :
    Facts (CFSG.EvenSporadicStandard.Solomon78.conjW g) (cw g) := by
  have h := ((facts_wm g hg).mul facts_D).mul (facts_wm _ (invLetters_lt g))
  unfold CFSG.EvenSporadicStandard.Solomon78.conjW
  rw [cw]
  exact h

theorem facts_prod_aux (T : Array (Array W)) (f : Nat → List Nat)
    (hT : ∀ x < T.size, Facts T[x]! (f x)) :
    ∀ (w : List Nat), (∀ x ∈ w, x < T.size) → ∀ (M : Array W) (u : List Nat), Facts M u →
      Facts (w.foldl (fun M x => mulW 253 M T[x]!) M) (u ++ (w.map f).flatten)
  | [], _, M, u, hM => by simpa using hM
  | x :: w, hw, M, u, hM => by
    have h := facts_prod_aux T f hT w (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ _
      (hM.mul (hT x (hw x List.mem_cons_self)))
    rw [List.foldl_cons, List.map_cons, List.flatten_cons, ← List.append_assoc]
    exact h

theorem facts_id : Facts (idW 253) [] :=
  ⟨idW_size, rowsWF_idW, by rw [toVM_idW (by norm_num)]; exact canonM_idM 253, toMatW_idW⟩

theorem facts_prod (T : Array (Array W)) (f : Nat → List Nat)
    (hT : ∀ x < T.size, Facts T[x]! (f x)) (w : List Nat) (hw : ∀ x ∈ w, x < T.size) :
    Facts (prodW 253 T w) (w.map f).flatten := by
  have h := facts_prod_aux T f hT w hw _ _ facts_id
  rw [List.nil_append] at h
  exact h

theorem eqW_of {X Y : Array W} {u v : List Nat} (hX : Facts X u) (hY : Facts Y v) (h : gm u = gm v) :
    eqW 253 X Y = true :=
  eqW_of_toMatW hX.size (canonW_of_canonM hX.canon) (canonW_of_canonM hY.canon)
    (by rw [hX.mat, hY.mat, h])

theorem neW_of {X Y : Array W} {u v : List Nat} (hX : Facts X u) (hY : Facts Y v) (h : gm u ≠ gm v) :
    eqW 253 X Y = false :=
  eqW_false_of_toMatW (by rw [hX.mat, hY.mat]; exact h)

theorem commW_of {X Y : Array W} {u v : List Nat} (hX : Facts X u) (hY : Facts Y v)
    (h : gm (u ++ v) = gm (v ++ u)) : CFSG.EvenSporadicStandard.Solomon78.commW X Y = true :=
  eqW_of (hX.mul hY) (hY.mul hX) h

theorem pairOK_of {R X Y : Array W} {r x y : List Nat} (hR : Facts R r) (hX : Facts X x)
    (hY : Facts Y y) (h1 : gm (x ++ r) = gm (r ++ x)) (h2 : gm (y ++ r) = gm (r ++ y))
    (h3 : gm (x ++ y) = gm (r ++ (y ++ x))) :
    CFSG.EvenSporadicStandard.Solomon78.pairOK R X Y = true := by
  unfold CFSG.EvenSporadicStandard.Solomon78.pairOK
  rw [commW_of hX hR h1, commW_of hY hR h2, eqW_of (hX.mul hY) (hR.mul (hY.mul hX)) h3]
  rfl

theorem lists' : CFSG.KC.WP.statesOK 2 WC PS 18 = true ∧ CFSG.KC.WP.relProgsOK 2 18 PE 21 = true ∧
    CFSG.KC.WP.relProgsOK 2 18 PF 21 = true := by
  have h := lists
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem good : ∀ k < 18, Good (CFSG.KS.Mat3.Canon3 64009) (mat3 253 64009) CFSG.KD.Fi23M.RB 2 (RS k) (WC k) :=
  states_good hs hroot hinv lists'.1 fun k hk => S.all k hk

theorem top_good {P : List Nat} (hl : CFSG.KC.WP.letsOK 2 P = true)
    (hr : CFSG.KC.WP.refsOK 18 P = true) :
    Good (CFSG.KS.Mat3.Canon3 64009) (mat3 253 64009) CFSG.KD.Fi23M.RB 2
      (CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE P)
      (CFSG.KC.WP.progWord WC P) :=
  top_sound hs hroot hinv hl fun ins hi h1 => good _ (refs_of 18 P hr ins hi h1)

theorem eq_words (j : Nat) (hj : j < 21) :
    wordMat (mat3 253 64009) CFSG.KD.Fi23M.RB 2 (CFSG.KC.WP.progWord WC (PE j)) =
      wordMat (mat3 253 64009) CFSG.KD.Fi23M.RB 2 (CFSG.KC.WP.progWord WC (PF j)) := by
  obtain ⟨hlE, hrE⟩ := relProgsOK_spec 21 lists'.2.1 j hj
  obtain ⟨hlF, hrF⟩ := relProgsOK_spec 21 lists'.2.2 j hj
  have e : CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PE j) =
      CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PF j) :=
    Nat.eq_of_beq_eq_true (E.all j hj)
  rw [← (top_good hlE hrE).2, ← (top_good hlF hrF).2, e]

noncomputable def eqOK (j : Nat) (U V : List Nat) : Bool :=
  (CFSG.KC.WP.progWord WC (PE j) == U.map cd) && (CFSG.KC.WP.progWord WC (PF j) == V.map cd) &&
    U.all (fun x => decide (x < 2)) && V.all (fun x => decide (x < 2))

theorem gm_eq_of {j : Nat} (hj : j < 21) {U V : List Nat} (h : eqOK j U V = true) : gm U = gm V := by
  unfold eqOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hU, hV⟩, hu⟩, hv⟩ := h
  have e := eq_words j hj
  rw [hU, hV, wordMat_cd U hu, wordMat_cd V hv] at e
  exact e

noncomputable def stOK (k : Nat) (U : List Nat) : Bool :=
  (WC k == U.map cd) && U.all (fun x => decide (x < 2))

theorem gm_ne_of {k l : Nat} (hk : k < 18) (hl : l < 18) {U V : List Nat} (hU : stOK k U = true)
    (hV : stOK l V = true)
    (hn : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS k) (RS l)) = true) :
    gm U ≠ gm V := by
  unfold stOK at hU hV
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hU hV
  intro e
  have gk := good k hk
  have gl := good l hl
  have ek : mat3 253 64009 (RS k) = gm U := by rw [gk.2, hU.1, wordMat_cd U hU.2]
  have el : mat3 253 64009 (RS l) = gm V := by rw [gl.2, hV.1, wordMat_cd V hV.2]
  have hkl := mat3_inj (d := 253) (by norm_num) gk.1 gl.1 (by rw [ek, el]; exact e)
  rw [hkl, Nat.beq_refl] at hn
  exact absurd hn (by decide)

def uRB : List Nat := dW7 ++ cw CFSG.EvenSporadicStandard.Solomon78.fi23G1

def uRC : List Nat := uRB ++ cw CFSG.EvenSporadicStandard.Solomon78.fi23G2

noncomputable def uT (i : Nat) : List Nat := cw (GS.getD i [])

noncomputable def tOK (i : Nat) : Bool := eqOK (6 + i) (uT i ++ uRC) (uRC ++ uT i)

theorem gs_lt : GS.all (fun w => w.all fun x => decide (x < 2)) = true := by quickRfl

theorem gs_len : GS.length = 12 := by decide +kernel

theorem gs_word {g : List Nat} (hg : g ∈ GS) : ∀ x ∈ g, x < 2 := by
  have h := List.all_eq_true.1 gs_lt g hg
  simpa using h

theorem facts_T : ∀ x < (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray.size,
    Facts (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray[x]! (uT x) := by
  intro x hx
  simp only [List.size_toArray, List.length_map] at hx
  rw [List.getElem!_toArray, getElem!_pos _ x (by simpa using hx), List.getElem_map, uT,
    List.getD_eq_getElem _ _ hx]
  exact facts_conj _ (gs_word (List.getElem_mem hx))

theorem g1_lt : ∀ x ∈ CFSG.EvenSporadicStandard.Solomon78.fi23G1, x < 2 := by decide

theorem g2_lt : ∀ x ∈ CFSG.EvenSporadicStandard.Solomon78.fi23G2, x < 2 := by decide

theorem perfCheckOf_true : CFSG.EvenSporadicStandard.Solomon78.perfCheckOf
    CFSG.EvenSporadicStandard.Solomon78.fi23G1 CFSG.EvenSporadicStandard.Solomon78.fi23G2 GS XS YS =
      true := by
  have fD := facts_D
  have fD1 := facts_conj _ g1_lt
  have fC := facts_conj _ g2_lt
  have fA := facts_wm [0] (by decide)
  have fRB := fD.mul fD1
  have fRC := fRB.mul fC
  have hxl : ∀ x ∈ XS, x < (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray.size := by
    have h : XS.all (fun x => decide (x < 12)) = true := by quickRfl
    simpa [gs_len] using h
  have hyl : ∀ x ∈ YS, x < (GS.map CFSG.EvenSporadicStandard.Solomon78.conjW).toArray.size := by
    have h : YS.all (fun x => decide (x < 12)) = true := by quickRfl
    simpa [gs_len] using h
  have fX := facts_prod _ uT facts_T XS hxl
  have fY := facts_prod _ uT facts_T YS hyl
  have hT : ∀ t ∈ GS.map CFSG.EvenSporadicStandard.Solomon78.conjW,
      CFSG.EvenSporadicStandard.Solomon78.commW t
        (mulW 253 (mulW 253 matD (CFSG.EvenSporadicStandard.Solomon78.conjW
          CFSG.EvenSporadicStandard.Solomon78.fi23G1))
          (CFSG.EvenSporadicStandard.Solomon78.conjW CFSG.EvenSporadicStandard.Solomon78.fi23G2)) =
        true := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    have hi' : i < 12 := by simpa [gs_len] using hi
    have hall : (List.range 12).all tOK = true := by quickRfl
    have ht := List.all_eq_true.1 hall i (List.mem_range.2 hi')
    have fT := facts_T i (by simpa using hi)
    rw [List.getElem!_toArray, getElem!_pos _ i hi] at fT
    exact commW_of fT fRC (gm_eq_of (by omega) ht)
  unfold CFSG.EvenSporadicStandard.Solomon78.perfCheckOf
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · quickRfl
  · quickRfl
  · exact commW_of fD fD1 (gm_eq_of (j := 0) (by norm_num) (by quickRfl))
  · exact commW_of fD fC (gm_eq_of (j := 1) (by norm_num) (by quickRfl))
  · exact commW_of fD1 fC (gm_eq_of (j := 2) (by norm_num) (by quickRfl))
  · exact canonW_matD
  · exact canonW_of_canonM fD1.canon
  · exact canonW_of_canonM fC.canon
  · exact neW_of fD fD1 (gm_ne_of (k := 0) (l := 1) (by norm_num) (by norm_num) (by quickRfl)
      (by quickRfl) n01)
  · exact neW_of fD fC (gm_ne_of (k := 0) (l := 2) (by norm_num) (by norm_num) (by quickRfl)
      (by quickRfl) n02)
  · exact neW_of fD1 fC (gm_ne_of (k := 1) (l := 2) (by norm_num) (by norm_num) (by quickRfl)
      (by quickRfl) n12)
  · exact pairOK_of fRB fA fD1 (gm_eq_of (j := 3) (by norm_num) (by quickRfl))
      (gm_eq_of (j := 4) (by norm_num) (by quickRfl)) (gm_eq_of (j := 5) (by norm_num) (by quickRfl))
  · rw [List.all_toArray, List.all_eq_true]
    exact hT
  · exact pairOK_of fRC fX fY (gm_eq_of (j := 18) (by norm_num) (by quickRfl))
      (gm_eq_of (j := 19) (by norm_num) (by quickRfl)) (gm_eq_of (j := 20) (by norm_num) (by quickRfl))

public theorem fi23PerfCheck_true : CFSG.EvenSporadicStandard.Solomon78.fi23PerfCheck = true := by
  rw [CFSG.EvenSporadicStandard.Solomon78.fi23PerfCheck, gens_eq, x_eq, y_eq]
  exact perfCheckOf_true

end CertificateChecks.KernelFi23Pf
