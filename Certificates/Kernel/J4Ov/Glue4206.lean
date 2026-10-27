module

public import Certificates.Kernel.J4Ov.Forest4206
public import Certificates.Kernel.J4Ov.Exc4206
public import Certificates.Kernel.J4Q.C4025
public import CFSG.Certificates.Kernel.J4Q.LettersAZ
public import CFSG.Certificates.Kernel.J4Q.VOrbBFS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenPFam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
import Certificates.Kernel.J4Q.Orb

public section

namespace CertificateChecks.KernelJ4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Quasithin.J4Ov CFSG.KC.J4Q CFSG.KC.LQT.Syl CFSG.KD.J4Ov CertificateChecks.KernelJ4Q
open CFSG.KD.J4Q (c rm one pad A B L0 L1 L2 L0i L1i L2i U0 mkKM_0 mkKM_1 mkKM_2 mkKM_3)
open CFSG.Quasithin.J4Loc (z0)
open CFSG.KC.Loop (strictN)

set_option maxRecDepth 400000

@[expose] def PR4206 (g : J) (m : Nat) : Prop :=
  ∃ X : Array V2, WfA X ∧ encR X = m ∧ Mx g = rowsMatrix X

theorem pr_mul4206 {g h : J} {a b : Nat} (hg : PR4206 g a) (hh : PR4206 h b) :
    PR4206 (g * h) (mulJ c rm a b) := by
  obtain ⟨X, hX, rfl, hgX⟩ := hg
  obtain ⟨Y, hY, rfl, hhY⟩ := hh
  obtain ⟨h1, h2⟩ := mul_enc hK ⟨hX, rfl⟩ ⟨hY, rfl⟩
  exact ⟨_, h1, h2, by rw [map_mul, hgX, hhY, rowsMatrix_mulRows]⟩

theorem pr_eq4206 {g h : J} {a b : Nat} (hg : PR4206 g a) (hh : PR4206 h b)
    (e : Nat.beq a b = true) : g = h := by
  obtain ⟨X, hX, rfl, hgX⟩ := hg
  obtain ⟨Y, hY, rfl, hhY⟩ := hh
  have e' : eqRows X Y = true := by
    rw [eqRows_of ⟨hX, rfl⟩ ⟨hY, rfl⟩]
    exact e
  apply Mx_injective
  rw [hgX, hhY, eqRows_iff.1 e']

theorem pr_inv4206 {g : J} {a n : Nat} (hg : PR4206 g a) (hn : canonJ pad n = true)
    (h : Nat.beq (mulJ c rm a n) one = true) : PR4206 g⁻¹ n := by
  obtain ⟨X, hX, rfl, hgX⟩ := hg
  obtain ⟨hY, hYn⟩ := invRows_enc hK hX hn h
  have e : eqRows (mulRows X (invRows X)) idRows = true := by
    rw [eqRows_of (mul_enc hK ⟨hX, rfl⟩ ⟨hY, hYn⟩) (id_enc hK)]
    exact h
  exact ⟨_, hY, hYn, Mx_inv_of_rows hgX e⟩

theorem pr_word4206 (w : List Int) :
    PR4206 (wordProd xJ w) (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] w) := by
  obtain ⟨h1, h2⟩ := enc_wordRows hK loc_gens loc_invs w
  exact ⟨_, h1, h2, Mx_wordProd matFacts w⟩

theorem pr_path4206 {l : Nat} (h1 : 1 ≤ l) (h7 : l < 7) :
    PR4206 (pathElt (repPaths.getD l [])) (getN one MLs (l - 1)) := by
  have e : 1 + 1 * (l - 1) = l := by omega
  have h := pathM_enc (i := l - 1) (by omega)
  rw [e] at h
  exact ⟨_, h.1, h.2, Mx_kEl matFacts h7⟩

theorem pr_eta4206 (m : Nat) : PR4206 (eta uJ 11 m) (etaK c rm one Us m) := by
  have h := enc_etaRows hK (T := uTab (locMats ()) (locInvs ())) (Ts := Us) uTab_enc m
  exact ⟨_, h.1, h.2, Mx_eta matFacts 11 le_rfl m⟩

theorem getN_eq_getD4206 (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by cases i <;> rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change getN d l i = _
    rw [getN_eq_getD4206 d l i]
    rfl

theorem repData_length4206 : repData.length = 49 := rfl

theorem decode4206 : repData.map (fun r => decodeWord r.xw) = rx4207 := by
  have e : repData.map (fun r => decodeWord r.xw) = (repData.map RepEntry.xw).map decodeWord := by
    rw [List.map_map]
    rfl
  rw [e, repData_strs4207]
  simp only [rx4207, List.map_cons, List.map_nil, decodeWord_ofList]

theorem decode_get4206 {t : Nat} (ht : t < 49) : decodeWord (rep4207 t).xw = rx4207.getD t [] := by
  rw [← decode4206, List.getD_eq_getElem _ _ (by rw [List.length_map, repData_length4206]; exact ht),
    List.getElem_map, rep4207, List.getD_eq_getElem _ _ (by rw [repData_length4206]; exact ht)]

theorem getD_map_nil4206 {α β : Type} (f : List α → List β) (hf : f [] = []) :
    ∀ (l : List (List α)) (t : Nat), (l.map f).getD t [] = f (l.getD t [])
  | [], t => by simp [hf]
  | a :: l, 0 => rfl
  | a :: l, t + 1 => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_map_nil4206 f hf l t

theorem W_get4206 {t : Nat} (ht : t < 49) :
    (W.getD t []).map Int.ofNat = decodeWord (rep4207 t).xw := by
  rw [decode_get4206 ht, ← beq_iff_eq.1 w4206_ok, getD_map_nil4206 _ rfl]

theorem wl_get4206 {t : Nat} (ht : t < 49) : ∀ l ∈ W.getD t [], 1 ≤ l ∧ l ≤ 3 := by
  intro l hl
  have h := List.all_eq_true.1 (allR_spec wl4206_ok t ht) l hl
  simp only [andB_eq, Bool.and_eq_true, Nat.ble_eq] at h
  exact h

theorem l_get4206 {t : Nat} (ht : t < 49) : (rep4207 t).l = if t < 28 then 5 else 6 := by
  rw [← LS_getD ht, eqLK_spec ls4206_ok,
    List.getD_eq_getElem _ _ (by rw [List.length_map, repData_length4206]; exact ht),
    List.getElem_map, rep4207, List.getD_eq_getElem _ _ (by rw [repData_length4206]; exact ht)]

theorem l_bounds4206 {t : Nat} (ht : t < 49) : 5 ≤ (rep4207 t).l ∧ (rep4207 t).l < 7 := by
  rw [l_get4206 ht]
  split_ifs <;> omega

theorem wordProd_cons4206 (l : Nat) (p : List Nat) (hl : 1 ≤ l) :
    wordProd xJ ((l :: p).map Int.ofNat) = xJ (l - 1) * wordProd xJ (p.map Int.ofNat) := by
  have h0 : (0 : Int) < Int.ofNat l := by
    rw [Int.ofNat_eq_coe]
    omega
  simp only [wordProd, List.map_cons, List.prod_cons, if_pos h0]
  rfl

theorem wordProd_mem4206 : ∀ p : List Nat, (∀ l ∈ p, 1 ≤ l ∧ l ≤ 3) →
    wordProd xJ (p.map Int.ofNat) ∈ Hj
  | [], _ => by
    simp only [wordProd, List.map_nil, List.prod_nil]
    exact Hj.one_mem
  | l :: p, hp => by
    have hl := hp l List.mem_cons_self
    rw [wordProd_cons4206 l p hl.1]
    exact Hj.mul_mem (xJ_mem (by omega))
      (wordProd_mem4206 p fun k hk => hp k (List.mem_cons_of_mem _ hk))

theorem inv_smul_row4206 {g : J} {X : Array V2} (hg : Mx g = rowsMatrix X) (v : V2) :
    g⁻¹ • toRow v.toVec = toRow (frApply (frTable X) v).toVec := by
  rw [← ofRow_inj, inv_smul_row, ← Mx_apply, hg, frApply_toVec_eq_vecMul]
  rfl

theorem pathL4206 : ∀ (p : List Nat) (v : V2), v.wf = true → (∀ l ∈ p, 1 ≤ l) →
    ∃ v' : V2, v'.wf = true ∧ v2N v' = pathVK rm one [L0, L1, L2] p (v2N v) ∧
      (wordProd xJ (p.map Int.ofNat))⁻¹ • toRow v.toVec = toRow v'.toVec
  | [], v, hv, _ => ⟨v, hv, rfl, by simp [wordProd]⟩
  | l :: p, v, hv, hp => by
    have hl : 1 ≤ l := hp l List.mem_cons_self
    obtain ⟨hX, hXe⟩ := loc_gens (l - 1)
    obtain ⟨v', hv', he, hs⟩ := pathL4206 p _ (wf_frApply hX v)
      fun k hk => hp k (List.mem_cons_of_mem _ hk)
    refine ⟨v', hv', ?_, ?_⟩
    · rw [he, v2N_frApply hK hX hv, hXe]
      change _ = strictN (vecJ rm (v2N v) (getN one [L0, L1, L2] (l - 1)))
        (pathVK rm one [L0, L1, L2] p)
      rw [strictN_eq]
    · rw [wordProd_cons4206 l p hl, mul_inv_rev, mul_smul,
        inv_smul_row4206 (Mx_xJ' matFacts (l - 1)), hs]

theorem zinv4206 {t : Nat} (ht : t < 49) :
    ∃ x ∈ Hj, (zEl (rep4207 t))⁻¹ • w₀ = x • QT2.rep (rep4207 t).l := by
  refine ⟨(wordProd xJ (decodeWord (rep4207 t).xw))⁻¹, Hj.inv_mem ?_, ?_⟩
  · rw [← W_get4206 ht]
    exact wordProd_mem4206 _ (wl_get4206 ht)
  · rw [zEl, mul_inv_rev, mul_smul]
    rfl

theorem root4206 {t : Nat} (ht : t < 49) : ∃ v : V2, v.wf = true ∧ v2N v = RT.getD t 0 ∧
    toRow v.toVec = (zEl (rep4207 t))⁻¹ • w₀ := by
  have hl := l_get4206 ht
  have hLS := LS_getD ht
  have hKP : KP.getD (LS.getD t 0 - 5) [] = repPaths.getD (rep4207 t).l [] := by
    have hk := kp4206_ok
    simp only [andB_eq, Bool.and_eq_true] at hk
    rw [hl, hLS]
    split_ifs
    · exact eqLK_spec hk.2.1
    · exact eqLK_spec hk.2.2
  obtain ⟨hpw, hpv⟩ := pathVec_enc (repPaths.getD (rep4207 t).l [])
  obtain ⟨v, hv, he, hs⟩ := pathL4206 (W.getD t []) _ hpw fun l hl' => (wl_get4206 ht l hl').1
  refine ⟨v, hv, ?_, ?_⟩
  · rw [he, roots4206 ht, hKP, Nat.eq_of_beq_eq_true r0_4206_ok, hpv]
  · rw [← hs, W_get4206 ht, zEl, mul_inv_rev, mul_smul, ← rep_toVec matFacts (l_bounds4206 ht).2,
      rep_eq, uElt]

@[expose] noncomputable def let4206 (g : Nat) : J := if g < 3 then kJ g else kJ 3 * uJ 0

theorem let_mem4206 {g : Nat} (hg : g < 4) : let4206 g ∈ P0 := by
  unfold let4206
  split_ifs with h
  · exact kJ_mem_P0 (by omega)
  · exact P0.mul_mem (kJ_mem_P0 (by norm_num)) (Subgroup.subset_closure (Or.inl ⟨0, by norm_num, rfl⟩))

theorem let_pr4206 {g : Nat} (hg : g < 4) : PR4206 (let4206 g) (getN one letMs g) := by
  have hk : ∀ i < 4, PR4206 (kJ i) (getN one mkKMs i) := fun i hi => by
    have h := kRows_enc hi
    exact ⟨_, h.1, h.2, by rw [Mx_kJ matFacts hi, kTab_get hi]⟩
  unfold let4206
  split_ifs with h
  · have e : getN one letMs g = getN one mkKMs g := by
      rw [getN_eq_getD4206, getN_eq_getD4206]
      interval_cases g <;> rfl
    rw [e]
    exact hk g hg
  · obtain rfl : g = 3 := by omega
    have hu : PR4206 (uJ 0) U0 := by
      have h := uTab_enc 0 (by decide)
      exact ⟨_, h.1, h.2, Mx_uJ matFacts (by norm_num)⟩
    have e : getN one letMs 3 = mulJ c rm (getN one mkKMs 3) U0 := by
      rw [getN_eq_getD4206, getN_eq_getD4206]
      rfl
    rw [e]
    exact pr_mul4206 (hk 3 (by norm_num)) hu

theorem pt4206 {t : Nat} (ht : t < 49) : ∀ k < (ptsT t).length, ∃ v : V2, v.wf = true ∧
    v2N v = (ptsT t).getD k 0 ∧ ∃ q ∈ P0, q • toRow v.toVec = (zEl (rep4207 t))⁻¹ • w₀ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · obtain ⟨v, hv, he, hr⟩ := root4206 ht
      exact ⟨v, hv, he, 1, P0.one_mem, by rw [one_smul, hr]⟩
    · obtain ⟨p, hp, g, hg, e⟩ := tree4206 ht k hk0 hk
      obtain ⟨v, hv, he, q, hq, hqe⟩ := ih p hp (by omega)
      obtain ⟨X, hX, hXe, hgX⟩ := let_pr4206 hg
      refine ⟨frApply (frTable X) v, wf_frApply hX v, ?_, q * let4206 g,
        P0.mul_mem hq (let_mem4206 hg), ?_⟩
      · rw [v2N_frApply hK hX hv, hXe, he, e]
      · rw [mul_smul, ← inv_smul_row4206 hgX, smul_inv_smul, hqe]

theorem vorb_wf4206 {O : VOrb} {r : V2} {m : Nat} (hok : vorbOK locTabs r O m = true) {q : Nat}
    (hq : q < m) : (O.pts[q]!).wf = true := by
  have h := vorb_at hok hq
  unfold vorbAt at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

open scoped Classical in
theorem cover4206 {lo n cap ℓ : Nat} {O : VOrb} {r : V2} (hn : lo + n ≤ 49)
    (hl : ∀ t, lo ≤ t → t < lo + n → (rep4207 t).l = ℓ)
    (hok : vorbOK locTabs r O cap = true) (hr : QT2.rep ℓ = toRow r.toVec)
    (hF : ((List.range' lo n).map ptsT).flatten.Nodup ∧
      ((List.range' lo n).map ptsT).flatten.length = cap) :
    ∀ h ∈ Hj, ∃ i < 49, ∃ q ∈ P0, q • (h • QT2.rep ℓ) = (zEl (rep4207 i))⁻¹ • w₀ := by
  have hM := matFacts
  have hmem : ∀ x ∈ ((List.range' lo n).map ptsT).flatten, ∃ t, lo ≤ t ∧ t < lo + n ∧
      ∃ k < (ptsT t).length, (ptsT t).getD k 0 = x := by
    intro x hx
    rw [List.mem_flatten] at hx
    obtain ⟨l, hl', hx⟩ := hx
    rw [List.mem_map] at hl'
    obtain ⟨t, ht, rfl⟩ := hl'
    rw [List.mem_range'_1] at ht
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨t, ht.1, ht.2, k, hk, List.getD_eq_getElem _ _ hk⟩
  have hsub : ((List.range' lo n).map ptsT).flatten.toFinset ⊆
      (Finset.range cap).image (fun q => v2N (O.pts[q]!)) := by
    intro x hx
    obtain ⟨t, ht1, ht2, k, hk, rfl⟩ := hmem x (List.mem_toFinset.1 hx)
    obtain ⟨v, hv, he, q, hq, hqe⟩ := pt4206 (by omega : t < 49) k hk
    obtain ⟨y, hy, hye⟩ := zinv4206 (by omega : t < 49)
    have hrow : toRow v.toVec = (q⁻¹ * y) • toRow r.toVec := by
      rw [mul_smul, ← hr, ← hl t ht1 ht2, ← hye, ← hqe, inv_smul_smul]
    obtain ⟨q', hq', e'⟩ := Finset.mem_image.1 (vorb_orbit_subset hM hok
      ⟨q⁻¹ * y, Hj.mul_mem (Hj.inv_mem (P0_le_Hj hq)) hy, hrow⟩)
    have e2 : (O.pts[q']!).toVec = v.toVec := e'
    have e3 := (V2.toVec_inj (vorb_wf4206 hok (Finset.mem_range.1 hq')) hv).1 e2
    exact Finset.mem_image.2 ⟨q', hq', by rw [e3, he]⟩
  have hS : ((Finset.range cap).image (fun q => v2N (O.pts[q]!))).card ≤ cap :=
    Finset.card_image_le.trans (by rw [Finset.card_range])
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [List.toFinset_card_of_nodup hF.1, hF.2]; exact hS)
  intro h hh
  obtain ⟨q', hq', e'⟩ := Finset.mem_image.1 (vorb_orbit_subset hM hok (v := h • QT2.rep ℓ)
    ⟨h, hh, by rw [hr]⟩)
  have hx : v2N (O.pts[q']!) ∈ ((List.range' lo n).map ptsT).flatten.toFinset := by
    rw [heq]
    exact Finset.mem_image.2 ⟨q', hq', rfl⟩
  obtain ⟨t, ht1, ht2, k, hk, hke⟩ := hmem _ (List.mem_toFinset.1 hx)
  obtain ⟨v, -, he, q, hq, hqe⟩ := pt4206 (by omega : t < 49) k hk
  have hv : v = O.pts[q']! := VOrbBFS.v2N_inj (he.trans hke)
  refine ⟨t, by omega, q, hq, ?_⟩
  rw [← e', vecP, ← hv, hqe]

theorem orbit_cover4206 {ℓ : Nat} (hℓ : ℓ = 5 ∨ ℓ = 6) {h : J} (hh : h ∈ Hj) :
    ∃ i < 49, ∃ q ∈ P0, q • (h • (uEl ℓ • w₀)) =
      (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ • w₀ := by
  have hu : uEl ℓ • w₀ = QT2.rep ℓ := rfl
  rw [hu]
  rcases hℓ with rfl | rfl
  · exact cover4206 (lo := 0) (n := 28) (by norm_num)
      (fun t _ ht => by rw [l_get4206 (by omega), if_pos ht]) orb5_vorbOK
      (rep_toVec matFacts (by norm_num)) forest5_4206 h hh
  · exact cover4206 (lo := 28) (n := 21) (by norm_num)
      (fun t ht1 ht2 => by rw [l_get4206 (by omega), if_neg (by omega)]) orb6_vorbOK
      (rep_toVec matFacts (by norm_num)) forest6_4206 h hh

theorem strictB_eq4206 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem pr_z4206 {i : Nat} (hi : i < 49) : PR4206 (zEl (rep4207 i)) (z4207 i) := by
  have hb := l_bounds4206 hi
  obtain ⟨X, h1, h2, h3⟩ := pr_word4206 (decodeWord (rep4207 i).xw)
  rw [decode_get4206 hi] at h2
  exact pr_mul4206 (pr_path4206 (by omega) hb.2) ⟨X, h1, h2, h3⟩

theorem exc_cert4206 {i : Nat} (hi : i < 49) (hexc : (repData.getD i ⟨0, "", true, 0⟩).exc = true) :
    zEl (repData.getD i ⟨0, "", true, 0⟩) * z0 * (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ ∈
      Eg uJ 11 := by
  change zEl (rep4207 i) * z0 * (zEl (rep4207 i))⁻¹ ∈ Eg uJ 11
  change (rep4207 i).exc = true at hexc
  have h := allR_spec exc4206_ok i hi
  unfold exc4206K at h
  rw [hexc] at h
  change strictB (z4207 i) (fun Z => strictB (zi4207 i) fun Zi => excChk4206 Z Zi (rep4207 i).c) =
    true at h
  rw [strictB_eq4206, strictB_eq4206] at h
  unfold excChk4206 at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hcan, hmul, -, hconj⟩ := h
  have hZ := pr_z4206 hi
  have hc := pr_mul4206 (pr_mul4206 hZ (pr_eta4206 1131)) (pr_inv4206 hZ hcan hmul)
  rw [z0, pr_eq4206 hc (pr_eta4206 (rep4207 i).c) hconj]
  exact eta_mem_Eg 11 le_rfl _

end CertificateChecks.KernelJ4Ov

end
