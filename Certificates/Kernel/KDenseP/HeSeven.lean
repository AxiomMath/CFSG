module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.SepAt
public import Certificates.Kernel.KDenseP.FixOf
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.HeSeven.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.HeSeven.CFix
public import CFSG.Certificates.Kernel.KDenseP.HeSeven.CMove
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace CertificateChecks.KernelKDenseP.HeSeven

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.HeSeven CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven
  CFSG.HardMathSupport.Dickson.I271.TabMThreeA

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.HE7M.MT = true := by
  kd_monoTabL CFSG.KD.HE7ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.HE7M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem evalWordC_append (c : Native.Ctx) (w₁ w₂ : List Native.Gen) (v : Native.DVec) :
    Native.evalWordC c (w₁ ++ w₂) v = Native.evalWordC c w₂ (Native.evalWordC c w₁ v) := by
  unfold Native.evalWordC
  exact List.foldl_append

theorem evalWord_nil (v : Native.DVec) : Native.evalWord [] v = v := rfl

theorem fixAll_of_eqv {ws : List (List Native.Gen)} {v : Native.DVec}
    (h : ∀ w ∈ ws, (w.all fun g => g.validB) = true ∧ (Native.evalWord w v).eqv v = true) :
    fixAll ws v = true := by
  unfold fixAll Native.checkWords Native.checkWordsC
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  unfold Native.checkWordC
  rw [Bool.and_eq_true]
  exact h w hw

theorem fixAll_of_agree {ws : List (List Native.Gen)} (h : ∀ w ∈ ws, agree w [] = true) :
    fixAll ws (aV ()) = true ∧ fixAll ws (bV ()) = true ∧ fixAll ws (wV ()) = true := by
  have key : ∀ w ∈ ws, (w.all fun g => g.validB) = true ∧
      (Native.evalWord w (aV ())).eqv (aV ()) = true ∧ (Native.evalWord w (bV ())).eqv (bV ()) = true ∧
      (Native.evalWord w (wV ())).eqv (wV ()) = true := by
    intro w hw
    have h1 := h w hw
    unfold agree at h1
    simp only [Bool.and_eq_true, evalWord_nil] at h1
    obtain ⟨⟨⟨⟨hv, -⟩, ha⟩, hb⟩, hw'⟩ := h1
    exact ⟨hv, ha, hb, hw'⟩
  exact ⟨fixAll_of_eqv fun w hw => ⟨(key w hw).1, (key w hw).2.1⟩,
    fixAll_of_eqv fun w hw => ⟨(key w hw).1, (key w hw).2.2.1⟩,
    fixAll_of_eqv fun w hw => ⟨(key w hw).1, (key w hw).2.2.2⟩⟩

theorem agreeAll_eHe : agreeAll eHe = true :=
  (tp3B_sound data_ok eHe [] (by quickRfl) (S := CFSG.KD.HE7.cfix.S)
    (fun x hx => by interval_cases x <;> rfl) (CH := CFSG.KD.HE7.cfix.CH)
    (nch := kd_count% CFSG.KD.HE7.cfix t) (IT := CFSG.KD.HE7.cfix.IT)
    (by kd_allE CFSG.KD.HE7.cfix t) (by quickRfl) (by quickRfl)).1

theorem agree_he (k : ℕ) (hk : k < 15) : agree ((heWordList ()).getD k []) [] = true := by
  have hl : (heWordList ()).length = 15 := by decide +kernel
  refine List.all_eq_true.1 agreeAll_eHe ((heWordList ()).getD k [], []) (List.mem_map.2 ⟨_, ?_, rfl⟩)
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem fixAll_heChunk {ks : List ℕ} (hks : ∀ k ∈ ks, k < 15) :
    fixAll (heChunk ks) (aV ()) = true ∧ fixAll (heChunk ks) (bV ()) = true ∧
      fixAll (heChunk ks) (wV ()) = true := by
  refine fixAll_of_agree fun w hw => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  exact agree_he k (hks k hk)

theorem item_move (t : ℕ) (ht : t < 2) :
    (∀ g ∈ ((tri [] nHe).getD t ([], [])).1, g.validB = true) ∧
      (∀ g ∈ ((tri [] nHe).getD t ([], [])).2, g.validB = true) ∧
      (CFSG.KD.HE7.cmove.IT[t]! / 4 % 2 = 0 → Cong5D
        (Native.evalWord ((tri [] nHe).getD t ([], [])).1
          (KernelKDense.wit (CFSG.KD.HE7.cmove.IT[t]! % 4)))
        (Native.evalWord ((tri [] nHe).getD t ([], [])).2
          (KernelKDense.wit (CFSG.KD.HE7.cmove.IT[t]! % 4)))) ∧
      (CFSG.KD.HE7.cmove.IT[t]! / 4 % 2 = 1 → ∃ k < 196884,
        DVec.res5 (Native.evalWord ((tri [] nHe).getD t ([], [])).1
          (KernelKDense.wit (CFSG.KD.HE7.cmove.IT[t]! % 4))) k ≠
        DVec.res5 (Native.evalWord ((tri [] nHe).getD t ([], [])).2
          (KernelKDense.wit (CFSG.KD.HE7.cmove.IT[t]! % 4))) k) :=
  itemL data_ok (p := tri [] nHe) (by quickRfl)
  (S := CFSG.KD.HE7.cmove.S) (fun x hx => by interval_cases x <;> rfl) (CH := CFSG.KD.HE7.cmove.CH)
  (nch := kd_count% CFSG.KD.HE7.cmove t) (IT := CFSG.KD.HE7.cmove.IT)
  (by kd_allE CFSG.KD.HE7.cmove t) (by quickRfl) t (by
    have e : CFSG.KD.HE7.cmove.IT.length = 2 := by decide +kernel
    omega)

theorem moveCheck_heA_b : EdgeNoncomm.moveCheck heA (bV ()) = true := by
  obtain ⟨v1, -, -, hn⟩ := item_move 0 (by norm_num)
  have e1 : (tri [] nHe).getD 0 ([], []) = (heA, []) := rfl
  have e2 : CFSG.KD.HE7.cmove.IT[0]! / 4 % 2 = 1 := by decide +kernel
  have e3 : CFSG.KD.HE7.cmove.IT[0]! % 4 = 1 := by decide +kernel
  have e5 : KernelKDense.wit 1 = bV () := rfl
  simp only [e1] at v1 hn
  obtain ⟨k, hk, hne⟩ := hn e2
  rw [e3, e5, evalWord_nil] at hne
  unfold EdgeNoncomm.moveCheck
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.2 v1, KernelKDenseP.moveCheckAux_of_res5 hk hne⟩

theorem denseMoveCheck_wV : denseMoveCheck (wV ()) = true := by
  obtain ⟨v1, -, -, hn⟩ := item_move 1 (by norm_num)
  have e1 : (tri [] nHe).getD 1 ([], []) = (powL 17 denseZWord ++ tWord, powL 17 denseZWord) := rfl
  have e2 : CFSG.KD.HE7.cmove.IT[1]! / 4 % 2 = 1 := by decide +kernel
  have e3 : CFSG.KD.HE7.cmove.IT[1]! % 4 = 2 := by decide +kernel
  have e5 : KernelKDense.wit 2 = wV () := rfl
  simp only [e1] at v1 hn
  obtain ⟨k, hk, hne⟩ := hn e2
  rw [e3, e5] at hne
  have hne' : DVec.res5 (Native.evalWord tWord (Native.evalWord (powL 17 denseZWord) (wV ()))) k ≠
      DVec.res5 (Native.evalWord (powL 17 denseZWord) (wV ())) k := by
    have e4 : Native.evalWord (powL 17 denseZWord ++ tWord) (wV ()) =
        Native.evalWord tWord (Native.evalWord (powL 17 denseZWord) (wV ())) :=
      evalWordC_append _ _ _ _
    rw [← e4]
    exact hne
  unfold denseMoveCheck EdgeNoncomm.moveCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨by decide +kernel, KernelKDenseP.eqv_tWord_wV⟩, List.all_eq_true.2 fun g hg => ?_,
    KernelKDenseP.moveCheckAux_of_res5 hk hne'⟩
  exact v1 g (List.mem_append_right _ hg)

end CertificateChecks.KernelKDenseP.HeSeven

end
