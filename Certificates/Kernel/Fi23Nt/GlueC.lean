module

public import Certificates.Kernel.Fi23Nt.GlueB
public import Certificates.Kernel.Fi23Nt.Filt
public import Certificates.Kernel.Fi23Nt.Filt1
public import Certificates.Kernel.Fi23Nt.TabSt
import Mathlib

public section

namespace CertificateChecks.KernelFi23Nt

open CFSG.Sporadic.Fi23 CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Nt
  CFSG.KC.Fi23R CertificateChecks.KernelFi23Q CFSG.KS.Fi23Nt CFSG.KS.E27Lie
  CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist CFSG.KD.Fi23Nt
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open Subgroup (centralizer closure)

#kc_forall_tree ec_all (fun s => CFSG.KD.Fi23Nt.enumCSl s = true) 3 CFSG.KD.Fi23Nt.tw101701ec
#kc_forall_tree sc_all (fun s => CFSG.KD.Fi23Nt.subCSl s = true) 9 CFSG.KD.Fi23Nt.tw101701sc
#kc_forall_tree dc_all (fun s => CFSG.KD.Fi23Nt.cosCSl s = true) 3 CFSG.KD.Fi23Nt.tw101701dc
#kc_forall_tree ep_all (fun s => CFSG.KD.Fi23Nt.enumPSl s = true) 6 CFSG.KD.Fi23Nt.tw101701ep
#kc_forall_tree f_all (fun s => CFSG.KD.Fi23Nt.filtSl s = true) 31 CFSG.KD.Fi23Nt.tw101701f
#kc_forall_tree ps_all (fun s => CFSG.KD.Fi23Nt.posSl s = true) 31 CFSG.KD.Fi23Nt.tw101701ps


theorem card_pass :
    ((Finset.range 31671).filter fun ν => passK POS0 PAR0 LAB0 G st ν = true).card = 486 := by
  have step : ∀ a len : ℕ,
      ((Finset.range (a + len)).filter fun ν => passK POS0 PAR0 LAB0 G st ν = true).card =
        ((Finset.range a).filter fun ν => passK POS0 PAR0 LAB0 G st ν = true).card +
          ((Finset.range len).filter fun l => passK POS0 PAR0 LAB0 G st (a + l) = true).card := by
    intro a len
    simp only [Finset.card_filter]
    rw [Finset.sum_range_add]
  have hsl : ∀ s < 31, ((Finset.range (slLen s)).filter fun l =>
      passK POS0 PAR0 LAB0 G st (s * 1024 + l) = true).card = cnt.getD s 0 :=
    fun s hs => cnt_spec (f_all s hs)
  have hN : ∀ s ≤ 30, ((Finset.range (s * 1024)).filter fun ν =>
      passK POS0 PAR0 LAB0 G st ν = true).card = ∑ t ∈ Finset.range s, cnt.getD t 0 := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      have e := hsl s (by omega)
      rw [slLen_ne (s := s) (by omega)] at e
      rw [Nat.succ_mul, step, ih (by omega), Finset.sum_range_succ, e]
  have e30 := hsl 30 (by norm_num)
  have h30 : slLen 30 = 951 := rfl
  rw [h30] at e30
  have e : (31671 : ℕ) = 30 * 1024 + 951 := by norm_num
  rw [e, step, hN 30 le_rfl, e30, ← Finset.sum_range_succ]
  decide +kernel

noncomputable abbrev gC (j : ℕ) : CFSG.Sporadic.Fi23.J := wE (eCW.getD j [])

noncomputable abbrev gP (j : ℕ) : CFSG.Sporadic.Fi23.J := wE (ePW.getD j [])

theorem tabC : TabData gC (parT eCN eCPar) (ltT eCN eCLt) eCN 3 := by
  have he : ∀ i < eCN, enumIK G eCW 3 eCN eCPar eCImg eCLt i = true := fun i hi =>
    all_of_blk (f := enumIK G eCW 3 eCN eCPar eCImg eCLt) (b := 81) (c := 3) (by norm_num)
      (fun s hs => ec_all s hs) i (by change i < 243 at hi; omega)
  exact (enum_sound (W := eCW) (m := 3) (n := eCN) (PAR := eCPar) (IMG := eCImg) (ORD := eCOrd)
    (LT := eCLt) (by norm_num) (fun j _ => getD_mem_of eCW (woks_of words.2.1) wok_nil j)
    (by change 0 < 243; norm_num) he tw101701oc).1

theorem tabP : TabData gP (parOf ePN (ppK ePPar) (pjK ePPar)) (ltOf 4 ePN (ltK ePLt)) ePN 4 := by
  have he : ∀ i < ePN, enumIK G ePW 4 ePN ePPar ePImg ePLt i = true := fun i hi =>
    all_of_blk (f := enumIK G ePW 4 ePN ePPar ePImg ePLt) (b := 81) (c := 6) (by norm_num)
      (fun s hs => ep_all s hs) i (by change i < 486 at hi; omega)
  exact (enum_sound (W := ePW) (m := 4) (n := ePN) (PAR := ePPar) (IMG := ePImg) (ORD := ePOrd)
    (LT := ePLt) le_rfl (fun j _ => getD_mem_of ePW (woks_of words.2.2.1) wok_nil j)
    (by change 0 < 486; norm_num) he tw101701op).1

theorem factC_k : FactC := by
  have hCW : ∀ w ∈ eCW, WOK w := woks_of words.2.1
  have hT := tabC
  have hn : 0 < eCN := by change 0 < 243; norm_num
  obtain ⟨Q, hQ, hQcl⟩ := hT.exists_subgroup hn
  have hQc : Nat.card Q = 243 := hT.card_subgroup hQ
  have hh : subHK eCN tCA = true := tw101701hc
  have hs : ∀ k < 81, subIK eCN eCPar eCLt tCA (mskK tCA) k = true := fun k hk =>
    all_of_blk (f := subIK eCN eCPar eCLt tCA (mskK tCA)) (b := 9) (c := 9) (by norm_num)
      (fun s hs => by
        have h := sc_all s hs
        unfold subCSl subSlOf at h
        rwa [sB_eq] at h) k (by omega)
  obtain ⟨A₀, hA, hAc, hAcomm, -⟩ := sub_group hT hh hs
  have hlt := (subHK_spec hh).2.1
  have hA₀Q : A₀ ≤ Q := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := (hA x).1 hx
    exact (hQ _).2 ⟨_, hlt k hk, rfl⟩
  have hc : ∀ x < eCN, cosIK eCN eCPar eCLt tCA tCR tCNr tCD x = true := fun x hx =>
    all_of_blk (f := cosIK eCN eCPar eCLt tCA tCR tCNr tCD) (b := 81) (c := 3) (by norm_num)
      (fun s hs => dc_all s hs) x (by change x < 243 at hx; omega)
  have hz : ∀ c < tCNr, centIK eCN eCPar eCLt tCA 10 (lnK 16 tCR c) = true :=
    CFSG.KS.allN_spec tw101701nc
  have hcent : ∀ x ∈ Q, x ∉ A₀ → Nat.card ↥(A₀ ⊓ centralizer ({x} : Set J)) ≤ 9 := by
    intro x hx hxA
    obtain ⟨i, hi, rfl⟩ := (hQ x).1 hx
    have := cent_lt hT hh hs hA hc hz i hi hxA
    omega
  have hQt : Q ≤ centralizer ({t2} : Set J) := by
    rw [hQcl, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact getD_mem_of (P := fun w => wE w ∈ centralizer ({t2} : Set J)) eCW
      (fun w hw => Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff.1 hy]
        exact (t2_spec hCW tw101701t2 w hw).symm) (one_mem _) j
  have hmemA : ∀ i, (∃ k < 81, aK tCA k = i) → tabElt gC (parT eCN eCPar) i ∈ A₀ :=
    fun i ⟨k, hk, hik⟩ => (hA _).2 ⟨k, hk, by rw [hik]⟩
  have hwd : ∀ i < eCN, wE (wdK eCW eCPar eCN i) = tabElt gC (parT eCN eCPar) i :=
    fun i hi => wd_prod hT regE (fun _ _ => rfl) eCN i hi.le hi
  have hv0 : v0 < 31671 := by change 6299 < 31671; norm_num
  have hWok : wokK hW = true := words.2.2.2.2.2.2.1
  obtain ⟨-, hy0⟩ := hy_spec (wok_of hWok)
    (fun t _ => getD_mem_of yW (woks_of words.2.2.2.2.2.2.2.1) wok_nil t) hv0 tw101701hy
  have hlc := tw101701lc
  unfold CFSG.KD.Fi23Nt.lnkC at hlc
  simp only [CFSG.KS.bAnd_iff] at hlc
  obtain ⟨hl1, hl2⟩ := hlc
  have hl1' : lnkUK eCW eCPar eCN tCA (fun v => v) tCY yW = true := hl1
  have hyA : ∀ t, wE (yW.getD t []) ∈ A₀ := fun t =>
    getD_mem_of (P := fun w => wE w ∈ A₀) yW (fun w hw => by
      obtain ⟨i, -, hi, hik, hw'⟩ := forall2_mem (lnk_spec tCY yW hl1') w hw
      simp only [hw']
      rw [hwd i hi]
      exact hmemA i hik) (one_mem _) t
  have hy : ∀ t < 6, ∃ y ∈ A₀, idx 31671 (wE hW * y) v0 = t := fun t ht => ⟨_, hyA t, hy0 t ht⟩
  have hstW : ∀ s ∈ st, WOK s.1 := fun s hs =>
    woks_of words.2.2.2.2.1 s.1 (by rw [fstK_eq]; exact List.mem_map_of_mem hs)
  have hls : lnkUK eCW eCPar eCN tCA (fun v => v) stIdx (fstK st) = true := tw101701ls
  obtain ⟨S, hSd⟩ : ∃ S : List (J × Bool), S = st.map fun s => (wE s.1, s.2) := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : Finset ℕ,
      T = (Finset.range 31671).filter fun ν => passK POS0 PAR0 LAB0 G st ν = true := ⟨_, rfl⟩
  have hSA : ∀ s ∈ S, s.1 ∈ A₀ := by
    intro s hs
    rw [hSd] at hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
    obtain ⟨i, -, hi, hik, hw'⟩ := forall2_mem (lnk_spec stIdx (fstK st) hls) s'.1
      (by rw [fstK_eq]; exact List.mem_map_of_mem hs')
    simp only [hw']
    rw [hwd i hi]
    exact hmemA i hik
  have hp : ∀ x < 31671, posK G POS0 PTS0 PAR0 LAB0 x = true := fun x hx =>
    all_of_slices (f := posK G POS0 PTS0 PAR0 LAB0) (fun s hs => ps_all s hs) hx
  have hν₀S : ∀ s ∈ S,
      (conjPt v0 * conjPt (idx 31671 s.1 v0) = conjPt (idx 31671 s.1 v0) * conjPt v0 ↔
        s.2 = true) := by
    have h := (pass_iff hp hstW hv0).1 tw101701pv
    intro s hs
    rw [hSd] at hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
    exact h s' hs'
  have hT' : ∀ ν < 31671, (∀ s ∈ S,
      (conjPt ν * conjPt (idx 31671 s.1 ν) = conjPt (idx 31671 s.1 ν) * conjPt ν ↔
        s.2 = true)) → ν ∈ T := by
    intro ν hν hS
    rw [hTd]
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hν, (pass_iff hp hstW hν).2 fun s hs => ?_⟩
    exact hS (wE s.1, s.2) (by rw [hSd]; exact List.mem_map_of_mem hs)
  have hTc : T.card ≤ 486 := by
    rw [hTd, card_pass]
  have hTP := tabP
  have hnP : 0 < ePN := by change 0 < 486; norm_num
  obtain ⟨C', hC', hC'cl⟩ := hTP.exists_subgroup hnP
  have hC'c : Nat.card C' = 486 := hTP.card_subgroup hC'
  have hgen := gen_closure hT hn hh hA tw101701gc
  have hl2' : lnkUK eCW eCPar eCN tCA (fun v => appK hW (appK v (rinvK hW))) aGen bW = true := hl2
  have hlb := lnk_spec aGen bW hl2'
  have hlen : aGen.length = 4 := rfl
  have hbW : ∀ i < 4, wE (bW.getD i []) =
      wE hW * tabElt gC (parT eCN eCPar) (aGen.getD i 0) * (wE hW)⁻¹ ∧ bW.getD i [] ∈ bW := by
    intro i hi
    obtain ⟨⟨hlt', -, hw'⟩, hm⟩ := forall2_getD hlb i (by rw [hlen]; exact hi)
    refine ⟨?_, hm⟩
    rw [hw']
    beta_reduce
    rw [wE_conj hWok, hwd _ hlt']
  have hcb := cb_spec (woks_of words.2.2.1) (woks_of words.2.2.2.2.2.2.2.2) tw101701cb
  have hcomm : ∀ w ∈ ePW, ∀ i : Fin 4, wE w * (wE hW * tabElt gC (parT eCN eCPar) (aGen.getD i 0) *
      (wE hW)⁻¹) = wE hW * tabElt gC (parT eCN eCPar) (aGen.getD i 0) * (wE hW)⁻¹ * wE w := by
    intro w hw i
    rw [← (hbW i i.2).1]
    exact hcb w hw _ (hbW i i.2).2
  have hC'B : C' ≤ centralizer ((A₀.map (MulAut.conj (wE hW)).toMonoidHom : Subgroup J) : Set J) := by
    rw [hC'cl, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have hj := getD_mem_of (P := fun w => ∀ i : Fin 4, wE w * (wE hW *
        tabElt gC (parT eCN eCPar) (aGen.getD i 0) * (wE hW)⁻¹) = wE hW *
          tabElt gC (parT eCN eCPar) (aGen.getD i 0) * (wE hW)⁻¹ * wE w) ePW hcomm
      (fun i => by simp [wE]) j
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hy' : y ∈ (A₀.map (MulAut.conj (wE hW)).toMonoidHom) := hy
    rw [hgen, MonoidHom.map_closure] at hy'
    have hle : Subgroup.closure (⇑(MulAut.conj (wE hW)).toMonoidHom '' Set.range fun i : Fin 4 =>
        tabElt gC (parT eCN eCPar) (aGen.getD i 0)) ≤ centralizer ({gP j} : Set J) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      rw [Set.mem_singleton_iff.1 hz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hj i
    exact (Subgroup.mem_centralizer_iff.1 (hle hy') (gP j) rfl).symm
  exact factC_of_math (wE hW) hv0 S T hQt hQc hA₀Q hAcomm hAc hcent hy hSA hν₀S hT' hTc hC'B
    hC'c

end CertificateChecks.KernelFi23Nt

end
