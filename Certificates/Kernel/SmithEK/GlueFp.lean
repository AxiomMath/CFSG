module

public import Certificates.Kernel.SmithEK.ChecksFp
public import Certificates.Kernel.SmithEK.GlueCd
public import CFSG.Certificates.Kernel.SmithEK.FpSound
public import CFSG.LargeExtraspecial.S14SMKTransFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73 CFSG.LargeExtraspecial.S14.SMK
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions Module

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

theorem fp_div_two_pow_xor (a b : ℕ) : ∀ n, (a ^^^ b) / 2 ^ n = a / 2 ^ n ^^^ b / 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      fp_div_two_pow_xor a b n, cd_div_two_xor]

theorem fp_coord_xor (a b i : ℕ) : coord (a ^^^ b) i = coord a i ^^^ coord b i := by
  unfold coord
  have e : (4 : ℕ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
  rw [e, fp_div_two_pow_xor, show (4 : ℕ) = 2 ^ 2 from rfl, cd_xor_mod]

theorem fp_vecOfCode_xor (a b : ℕ) : vecOfCode (a ^^^ b) = vecOfCode a + vecOfCode b := by
  funext i
  apply code_inj
  rw [Pi.add_apply, code_add]
  exact fp_coord_xor a b i.val

theorem fp_vecOfCode_zero : vecOfCode 0 = 0 := by
  funext i
  apply code_inj
  change coord 0 i.val = (0 : F4).code.val
  simp [coord, code_zero]

theorem fp_vecOfCode_fpScale {l : ℕ} (hl : l < 4) (c : ℕ) :
    vecOfCode (fpScale l c) = (⟨⟨l, hl⟩⟩ : F4) • vecOfCode c := by
  have e : fpScale l c = codeOf ((⟨⟨l, hl⟩⟩ : F4) • vecOfCode c) := by
    unfold fpScale
    rw [cdMapC_eq]
    unfold codeOf
    simp only [Pi.smul_apply, smul_eq_mul, code_mul]
    change _ = f4mul l (coord c 0) + 4 * f4mul l (coord c 1) + 16 * f4mul l (coord c 2) +
      64 * f4mul l (coord c 3) + 256 * f4mul l (coord c 4) + 1024 * f4mul l (coord c 5)
    simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.nil_append, cdMul_eq]
    ring
  rw [e, vecOfCode_codeOf]

theorem fp_vecOfCode_four_pow (t : Fin 6) :
    vecOfCode (4 ^ t.val) = fun j => if t = j then 1 else 0 := by
  funext j
  apply code_inj
  have e : coord (4 ^ t.val) j.val = if t = j then 1 else 0 := by
    fin_cases t <;> fin_cases j <;> decide
  change coord (4 ^ t.val) j.val = _
  rw [e]
  split <;> rfl

theorem fp_ne_zero {l : ℕ} (hl : l < 4) (h0 : 0 < l) : (⟨⟨l, hl⟩⟩ : F4) ≠ 0 := by
  intro h
  have := congrArg (fun z : F4 => z.code.val) h
  rw [code_zero] at this
  change l = 0 at this
  omega

theorem fp_uVec {x : ℕ} : uVec x = vecOfCode (pts.L.getD x 0) := by
  unfold uVec
  rw [uPts_eq, cd_toArray_get]

variable
  {A : CFSG.LargeExtraspecial.SMod20.V ≃ₗ[ZMod 2] CFSG.LargeExtraspecial.SMod20.V} {π : Equiv.Perm (Fin 693)}

theorem fp_of_rec {j : ℕ} (hj : j < 5) {PI PJ UM BS BM FX FC FE FL : List ℕ}
    {SP : List (List ℕ)}
    (hk : fpRepK CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) 19 po.PL pb.P wd.W pts.L
      PI PJ UM BS BM FX FC FE FL SP = true)
    (h : InvHyp A π) (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) 19) π) :
    finrank (ZMod 2) (commSpace A) ≤ 8 ∧ NoTwoSub π := by
  obtain ⟨hPI, -, hpairs, hunit, hb8, hbm, hfixK, hnd, hall, hodd, -, hcode, htree, hline,
    hspan⟩ := fpRepK_sound hk
  have himg : ∀ x (hx : x < 693), (π ⟨x, hx⟩).val =
      cdImg CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) 19 x := by
    intro x hx
    rw [← hc ⟨x, hx⟩]
    exact candT_lift hj 19 hx
  have hfx : ∀ q, q ∈ FX ↔ ∃ hq : q < 693, π ⟨q, hq⟩ = ⟨q, hq⟩ := by
    intro q
    constructor
    · intro hq
      obtain ⟨h1, h2⟩ := hall q hq
      exact ⟨h1, Fin.ext (by rw [himg q h1]; exact h2)⟩
    · rintro ⟨hq, he⟩
      apply hfixK q hq
      rw [← himg q hq, he]
  have hne : FX ≠ [] := by
    intro he
    rw [he] at hodd
    simp at hodd
  have hlt : ∀ k < 20, PI.getD k 0 < 891 ∧ PJ.getD k 0 < 891 := fun k hk =>
    ⟨(cdPlK_sound (hpairs k hk)).1, (cdPlK_sound (hpairs k hk)).2.1⟩
  have hpl : ∀ q ∈ (List.range 20).map (fun k => (PI.getD k 0, PJ.getD k 0)),
      q.1 < 891 ∧ q.2 < 891 ∧ ⇑π '' wPlane q.1 = wPlane q.2 ∧
        ∃ m, xorSel BS m = wtArr[q.2]! ^^^ wtArr[q.1]! := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
    rw [List.mem_range] at hk
    obtain ⟨hi, hi'⟩ := hlt k hk
    refine ⟨hi, hi', image_wPlane_eq hi hi' fun kk hkk => ?_, BM.getD k 0, ?_⟩
    · have hm := plane_img hj (hpairs k hk) hkk
      rw [← wPt_val hi hkk, hc] at hm
      exact (uaMem_get hi' (π (wPt _ kk)).2).1 hm
    · rw [hbm k hk, wtArr_wd hi, wtArr_wd hi']
  have hum : ∀ t < 20, ∃ m, xorSel (((List.range 20).map
      (fun k => (PI.getD k 0, PJ.getD k 0))).map fun q => wtArr[q.1]!) m = 2 ^ t := by
    have e : (((List.range 20).map (fun k => (PI.getD k 0, PJ.getD k 0))).map
        fun q => wtArr[q.1]!) = PI.map fun i => wd.W.getD i 0 := by
      apply List.ext_getElem
      · simp [hPI]
      · intro n h1 h2
        have hn : n < 20 := by simpa using h1
        have hn' : n < PI.length := by omega
        rw [List.getElem_map, List.getElem_map, List.getElem_map, List.getElem_range]
        rw [wtArr_wd (hlt n hn).1, List.getD_eq_getElem PI 0 hn']
    intro t ht
    rw [e]
    exact ⟨_, hunit t ht⟩
  have horb : ∀ Q : ℕ → Prop, Q (FX.getD 0 0) → (∀ g ∈ FX, ∀ u ∈ FX, ∀ (hg : g < 693)
      (hu : u < 693), Q u → Q (tvP ⟨g, hg⟩ ⟨u, hu⟩).val) → ∀ v ∈ FX, Q v := by
    intro Q h0 hs
    refine fpTree_induct htree Q h0 fun g hg u hu hQ => ?_
    have hgm : FX.getD g 0 ∈ FX := getD_mem hg
    have hg' := (hall _ hgm).1
    have hu' := (hall _ hu).1
    rw [← (ap_tvTabs_TP hg' hu').1]
    have e := ap_tvTabs ⟨_, hg'⟩ ⟨u, hu'⟩
    simp only at e
    rw [e]
    exact hs _ hgm u hu hg' hu' hQ
  have hfr : ∀ ρ ∈ T46, (∀ x (hx : x < 693), x ∈ FX → ρ ⟨x, hx⟩ = ⟨x, hx⟩) → ρ = 1 := by
    intro ρ hρ hfix
    obtain ⟨hFC, hFCget⟩ := fpCodeK_sound hcode
    have hvec : ∀ k < FX.length, uVec (FX.getD k 0) = vecOfCode (FC.getD k 0) := by
      intro k hk
      rw [hFCget k hk, fp_uVec]
    obtain ⟨hFL, hFLk⟩ := fpLineK_sound hline
    have hcomb : ∀ S : List ℕ, (∀ e ∈ S, e % 64 < FC.length ∧ e / 64 < 4) →
        vecOfCode (fpComb FC S) ∈ Submodule.span F4 {v | ∃ x ∈ FX, v = uVec x} := by
      intro S
      induction S with
      | nil =>
        intro _
        change vecOfCode 0 ∈ _
        rw [fp_vecOfCode_zero]
        exact Submodule.zero_mem _
      | cons e S ih =>
        intro hS
        obtain ⟨he1, he2⟩ := hS e (List.mem_cons_self ..)
        change vecOfCode (fpScale (e / 64) (FC.getD (e % 64) 0) ^^^ fpComb FC S) ∈ _
        rw [fp_vecOfCode_xor, fp_vecOfCode_fpScale he2]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
          (ih fun e' he' => hS e' (List.mem_cons_of_mem _ he'))
        exact ⟨FX.getD (e % 64) 0, getD_mem (by omega), (hvec _ (by omega)).symm⟩
    refine eq_one_of_frame hρ (fun x hx => (hall x hx).1) hnd hne
      (fun x hx => hfix x _ hx) (fun k hk => ?_) (fun y => ?_)
    · obtain ⟨m, hm, n, hn, l, u, hl0, hl4, hu0, hu4, e⟩ := hFLk k (by omega)
      refine ⟨m, hm, n, by omega, ⟨⟨l, hl4⟩⟩, ⟨⟨u, hu4⟩⟩, fp_ne_zero hl4 hl0, fp_ne_zero hu4 hu0,
        ?_⟩
      rw [hvec n (by omega), hvec m (by omega), hvec (k + 1) hk, e, fp_vecOfCode_xor,
        fp_vecOfCode_fpScale, fp_vecOfCode_fpScale]
    · rw [pi_eq_sum_univ y]
      refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
      obtain ⟨hc4, hS⟩ := fpSpanK_sound hspan t.val t.2
      rw [← fp_vecOfCode_four_pow t, ← hc4]
      exact hcomb _ hS
  exact fp_of_frame h hb8 hpl hum hfx hnd hodd horb hfr

theorem fp_rep {j : ℕ} (hj2 : 2 ≤ j) (hj : j < 5) (h : InvHyp A π)
    (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) 19) π) :
    finrank (ZMod 2) (commSpace A) ≤ 8 ∧ NoTwoSub π := by
  match j, hj2, hj with
  | 2, _, _ => exact fp_of_rec (by norm_num) c21276fp_0 h hc
  | 3, _, _ => exact fp_of_rec (by norm_num) c21276fp_1 h hc
  | 4, _, _ => exact fp_of_rec (by norm_num) c21276fp_2 h hc

end CertificateChecks.KernelSmithEK
