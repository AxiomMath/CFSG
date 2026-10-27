module

public import Certificates.Kernel.J4Q.ZFrRad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZFrameB
public import CFSG.Certificates.Kernel.J4Q.ZFrTab
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZCl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZTab

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem lt_two_pow_of_lt {c : ℕ} (h : c < 2048) : c < 2 ^ 11 := by simpa using h

theorem seq_getD {lv : List (List ℕ)} (hlv : ∀ s ∈ lv, ∀ g ∈ s, g < 3) (t : ℕ) :
    ∀ g ∈ lv.getD t [], g < 3 := by
  intro g hg
  by_cases ht : t < lv.length
  · rw [List.getD_eq_getElem _ _ ht] at hg
    exact hlv _ (List.getElem_mem ht) g hg
  · rw [List.getD_eq_default _ _ (by omega)] at hg
    simp at hg

theorem acts_zfW (hM : MatFacts) :
    ∀ (C : List (List (List ℕ))) (ts : List ℕ), (∀ lv ∈ C, ∀ s ∈ lv, ∀ g ∈ s, g < 3) →
      Acts (el5 (zfW C ts)) (zfP C ts)
  | [], _, _ => by
    rw [show zfW [] _ = [] from rfl, el5_nil]
    exact Acts.one
  | _ :: _, [], _ => by
    rw [show zfW (_ :: _) [] = [] from rfl, el5_nil]
    exact Acts.one
  | lv :: C, t :: ts, hs => by
    change Acts (el5 (zfSeqW (lv.getD t []) ++ zfW C ts)) (compT (zfSeqT (lv.getD t [])) (zfP C ts))
    rw [QT2.el5_append]
    exact (acts_zfSeq hM _ (seq_getD (hs lv List.mem_cons_self) t)).mul
      (acts_zfW hM C ts fun l hl => hs l (List.mem_cons_of_mem _ hl))

theorem fix_zfW (hG : ZfGens) :
    ∀ (C : List (List (List ℕ))) (ts : List ℕ), (∀ lv ∈ C, ∀ s ∈ lv, ∀ g ∈ s, g < 3) →
      actT (zfP C ts) 1 = 1
  | [], _, _ => actT_idT (by norm_num)
  | _ :: _, [], _ => actT_idT (by norm_num)
  | lv :: C, t :: ts, hs => by
    change actT (compT (zfSeqT (lv.getD t [])) (zfP C ts)) 1 = 1
    rw [actT_comp, fix_zfW hG C ts fun l hl => hs l (List.mem_cons_of_mem _ hl)]
    exact fix_zfSeq hG _ (seq_getD (hs lv List.mem_cons_self) t)

theorem comm_eta_one_of_acts {g : J} {τ : List ℕ} (h : Acts g τ) (h1 : actT τ 1 = 1) :
    g * eta uJ 11 1 = eta uJ 11 1 * g := by
  have := h.2 1 (by norm_num)
  rw [h1] at this
  calc g * eta uJ 11 1 = (g * eta uJ 11 1 * g⁻¹) * g := by group
    _ = eta uJ 11 1 * g := by rw [this]

@[expose] def zfZero (C : List (List (List ℕ))) : List ℕ := C.map fun _ => 0

theorem zfZero_facts : ∀ {C : List (List (List ℕ))} {base : List ℕ}, zfChainOK C base = true →
    zfZero C ∈ zfAll C ∧ zfP C (zfZero C) = idT ∧ zfW C (zfZero C) = []
  | [], [], _ => ⟨List.mem_singleton_self _, rfl, rfl⟩
  | lv :: C, b :: base, h => by
    obtain ⟨-, hhead, -, -, -, hC⟩ := zfChainOK_cons h
    obtain ⟨h1, h2, h3⟩ := zfZero_facts hC
    have hl : 0 < lv.length := by
      cases lv with
      | nil => simp at hhead
      | cons a l => simp
    have h0 : lv.getD 0 [] = [] := by
      cases lv with
      | nil => rfl
      | cons a l => simpa using hhead
    refine ⟨?_, ?_, ?_⟩
    · change 0 :: zfZero C ∈ zfAll (lv :: C)
      simp only [zfAll, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨0, hl, zfZero C, h1, rfl⟩
    · change compT (zfSeqT (lv.getD 0 [])) (zfP C (zfZero C)) = idT
      rw [h0, h2]
      exact compT_idT_left lenOK_idT
    · change zfSeqW (lv.getD 0 []) ++ zfW C (zfZero C) = []
      rw [h0, h3]
      rfl
  | [], _ :: _, h => by simp [zfChainOK] at h
  | _ :: _, [], h => by simp [zfChainOK] at h

theorem zf_cover
    (hF : J4Basic) (hG : ZfGens) {C : List (List (List ℕ))} {base : List ℕ}
    (hC : zfChainOK C base = true) (hprod : (C.map List.length).prod = 887040) :
    ∀ x : J, x * eta uJ 11 1 = eta uJ 11 1 * x →
      ∃ ts ∈ zfAll C, ∃ c < 2048, x = eta uJ 11 c * el5 (zfW C ts) := by
  have hM := hF.mat
  have hs := zfChain_seq hC
  have hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true := fun g hg => (hG.2 g hg).1
  have hP : ∀ p ∈ (zfAll C).map (fun ts => (zfP C ts, el5 (zfW C ts))),
      Acts p.2 p.1 ∧ actT p.1 1 = 1 := by
    intro p hp
    obtain ⟨ts, -, rfl⟩ := List.mem_map.1 hp
    exact ⟨acts_zfW hM C ts hs, fix_zfW hG C ts hs⟩
  have hnd : (((zfAll C).map (fun ts => (zfP C ts, el5 (zfW C ts)))).map Prod.fst).Nodup := by
    rw [List.map_map]
    refine List.Nodup.map_on (fun a ha b hb e => zfP_inj hg ?_ hC a ha b hb e) (nodup_zfAll C)
    intro s hs' c hc d hd e
    exact actT_inj_of_acts hM (acts_zfSeq hM s hs') (lt_two_pow_of_lt hc) (lt_two_pow_of_lt hd) e
  have hcard : ((zfAll C).map (fun ts => (zfP C ts, el5 (zfW C ts)))).length * 2048 =
      Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1} : Set J)) := by
    rw [List.length_map, length_zfAll, hprod, card_centralizer_eta_one_b hF]
  intro x hx
  obtain ⟨p, hp, c, hc, rfl⟩ := K_eq_union hM _ hP hnd hcard x hx
  obtain ⟨ts, hts, rfl⟩ := List.mem_map.1 hp
  exact ⟨ts, hts, c, hc, rfl⟩

theorem xor_lt {a b : ℕ} (ha : a < 2048) (hb : b < 2048) : a ^^^ b < 2048 := by
  have := Nat.xor_lt_two_pow (n := 11) (lt_two_pow_of_lt ha) (lt_two_pow_of_lt hb)
  simpa using this

theorem comm_iff_mask (hM : MatFacts) {h v : J} {T : List ℕ}
    (hv : Acts v T) (hvv : v⁻¹ = v) {d : ℕ} (hd : d < 2048)
    (hg : v * h * v * h⁻¹ = eta uJ 11 d) {c : ℕ} (hc : c < 2048) :
    eta uJ 11 c * h * v = v * (eta uJ 11 c * h) ↔ (c ^^^ actT T c) = d := by
  have hT : actT T c < 2048 := by simpa using actT_lt hv.1 c
  have hvh : v * h * v⁻¹ = eta uJ 11 d * h := by
    rw [hvv]
    calc v * h * v = (v * h * v * h⁻¹) * h := by group
      _ = eta uJ 11 d * h := by rw [hg]
  have key : v * (eta uJ 11 c * h) * v⁻¹ = eta uJ 11 (actT T c ^^^ d) * h := by
    calc v * (eta uJ 11 c * h) * v⁻¹ = (v * eta uJ 11 c * v⁻¹) * (v * h * v⁻¹) := by group
      _ = eta uJ 11 (actT T c) * (eta uJ 11 d * h) := by rw [hv.2 c (lt_two_pow_of_lt hc), hvh]
      _ = eta uJ 11 (actT T c ^^^ d) * h := by rw [← mul_assoc, eta_xor (elem_uJ hM) le_rfl]
  constructor
  · intro hcomm
    have e : v * (eta uJ 11 c * h) * v⁻¹ = eta uJ 11 c * h := by
      rw [← hcomm]
      group
    rw [key] at e
    have e2 := eta_inj hM _ (lt_two_pow_of_lt (xor_lt hT hd)) _ (lt_two_pow_of_lt hc)
      (mul_right_cancel e)
    calc c ^^^ actT T c = (actT T c ^^^ d) ^^^ actT T c := by rw [e2]
      _ = d := by rw [Nat.xor_comm (actT T c) d, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro hx
    have e1 : actT T c ^^^ d = c := by
      rw [← hx, Nat.xor_comm c, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    have e : v * (eta uJ 11 c * h) * v⁻¹ = eta uJ 11 c * h := by rw [key, e1]
    calc eta uJ 11 c * h * v = (v * (eta uJ 11 c * h) * v⁻¹) * v := by rw [e]
      _ = v * (eta uJ 11 c * h) := by group

theorem sq_of_mask (hM : MatFacts) {h : J} {τ : List ℕ}
    (hh : Acts h τ) {e : ℕ} (he : h * h = eta uJ 11 e) {c : ℕ} (hc : c < 2048)
    (hce : (c ^^^ actT τ c) = e) : (eta uJ 11 c * h) ^ 2 = 1 := by
  calc (eta uJ 11 c * h) ^ 2 = eta uJ 11 c * (h * eta uJ 11 c * h⁻¹) * (h * h) := by
        rw [sq]
        group
    _ = eta uJ 11 c * eta uJ 11 (actT τ c) * eta uJ 11 e := by
      rw [hh.2 c (lt_two_pow_of_lt hc), he]
    _ = eta uJ 11 ((c ^^^ actT τ c) ^^^ e) := by
      rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl]
    _ = 1 := by rw [hce, Nat.xor_self, eta_zero]

@[expose] noncomputable def zfGvN (t₀ : J) (gW : List ℤ) : ℕ → J
  | 0 => eta uJ 11 1
  | n + 1 => el5 gW * zCj t₀ (n + 1) * (el5 gW)⁻¹

@[expose] noncomputable def zfGv (t₀ : J) (gW : List ℤ) (i : Fin 4) : J := zfGvN t₀ gW i

@[expose] noncomputable def zfElt (sq : List (List ℕ)) (q : ℕ × ℕ) : J :=
  eta uJ 11 q.2 * el5 (zfSeqW (sq.getD q.1 []))

theorem mem_zfMasks {Ts : List (List ℕ)} {d : List ℕ} {c : ℕ} :
    c ∈ zfMasks Ts d ↔ c < 2048 ∧ ∀ i < 4, (c ^^^ actT (Ts.getD i []) c) = d.getD i 0 := by
  unfold zfMasks
  simp [List.mem_filter, List.mem_range, List.all_eq_true]

theorem mem_zfI {Ts : List (List ℕ)} {surv D : List (List ℕ)} {q : ℕ × ℕ} :
    q ∈ zfI Ts surv D ↔ q.1 < surv.length ∧ q.2 ∈ zfMasks Ts (D.getD q.1 []) := by
  obtain ⟨u, c⟩ := q
  unfold zfI
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u', hu', c', hc', rfl, rfl⟩
    exact ⟨hu', hc'⟩
  · rintro ⟨hu, hc⟩
    exact ⟨u, hu, c, hc, rfl, rfl⟩

theorem nodup_zfI (Ts : List (List ℕ)) (surv D : List (List ℕ)) : (zfI Ts surv D).Nodup := by
  unfold zfI
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · refine List.Nodup.map (fun a b h => (Prod.mk.inj h).2) ?_
    exact List.Nodup.filter _ List.nodup_range
  · refine List.nodup_range.imp fun {u u'} hne => ?_
    refine List.disjoint_left.2 fun q hq hq' => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    obtain ⟨c', -, e⟩ := List.mem_map.1 hq'
    exact hne (Prod.mk.inj e).1.symm

theorem classRad_of_zFr4
    (hF : J4Basic) (hG : ZfGens) {V : Subgroup J} (t₀ : J) (T₀ : Array V2)
    (hT₀ : Mx t₀ = rowsMatrix T₀) (gW : List ℤ) (hgW : ∀ l ∈ gW, l ≠ 0) {k : ℕ}
    (hV : V = Subgroup.closure (Set.range fun i : Fin 4 => zCj t₀ i))
    {Ts : List (List ℕ)} {base : List ℕ} {C : List (List (List ℕ))} {surv sq D : List (List ℕ)}
    {E : List ℕ} (hchk : chkZFr k T₀ gW Ts base C surv sq D E = true) : ClassRad V := by
  classical
  have hM := hF.mat
  unfold chkZFr at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlight, hC⟩, hprod⟩, hbt⟩, hsql⟩, hDl⟩, hnd⟩, hsurv⟩, hkL⟩, hidxL⟩ := hchk
  unfold chkZLightT at hlight
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies]
    at hlight
  obtain ⟨⟨⟨⟨⟨hTl, hA⟩, hB⟩, hCm⟩, hYwf⟩, hS⟩ := hlight
  have hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true := fun g hg => (hG.2 g hg).1
  have hconj : el5 gW * t₀ * (el5 gW)⁻¹ = eta uJ 11 1 := by
    apply Mx_injective
    rw [Mx_conj_el5 hM hgW hT₀, Mx_eta hM 11 le_rfl]
    exact congrArg rowsMatrix (eqRows_iff.1 hA)
  have hms : ∀ i, Mx (zfGv t₀ gW i) = rowsMatrix (zMs T₀ gW i) := by
    intro i
    obtain ⟨i, hi⟩ := i
    unfold zfGv zMs
    cases i with
    | zero => exact Mx_eta hM 11 le_rfl 1
    | succ n => exact Mx_conj_el5 hM hgW (Mx_zCj hM hT₀ (n + 1))
  have hmswf : ∀ i, wfRows (zMs T₀ gW i) = true := fun i => (hB i).1.1
  have hsq : ∀ i, eqRows (mulRows (zMs T₀ gW i) (zMs T₀ gW i)) idRows = true :=
    fun i => (hB i).1.2
  have hTab : ∀ i : Fin 4, zTabOK (zMs T₀ gW i) (zMs T₀ gW i) (Ts.getD i []) = true :=
    fun i => (hB i).2
  have hvsq : ∀ i, (zfGv t₀ gW i)⁻¹ = zfGv t₀ gW i := fun i => by
    apply inv_eq_of_mul_eq_one_right
    apply Mx_injective
    rw [map_mul, hms i, ← rowsMatrix_mulRows, eqRows_iff.1 (hsq i), rowsMatrix_idRows, map_one]
  have hTs : ∀ i : Fin 4, Acts (zfGv t₀ gW i) (Ts.getD i []) := fun i =>
    acts_of_rows hM (hms i) (by rw [hvsq i]; exact hms i) (hTab i)
  have hv0 : zfGv t₀ gW 0 = eta uJ 11 1 := rfl
  have hTsOK : ∀ T ∈ Ts, lenOK T = true := by
    intro T hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    have := (hTs ⟨i, by omega⟩).1
    rwa [show Ts.getD i [] = Ts[i] from List.getD_eq_getElem _ _ hi] at this
  set y : J := el5 gW * fiveElt * (el5 gW)⁻¹ with hy
  have hY : Mx y = rowsMatrix (zYR gW) := Mx_conj_el5 hM hgW (Mx_fiveElt hM)
  have hYi : Mx y⁻¹ = rowsMatrix (zYiR gW) := by
    have e : y⁻¹ = el5 gW * fiveElt⁻¹ * (el5 gW)⁻¹ := by
      rw [hy]
      group
    rw [e]
    exact Mx_conj_el5 hM hgW (Mx_fiveElt_inv hM)
  have hy5 : orderOf y = 5 := by
    rw [hy, orderOf_conj_eq]
    exact orderOf_fiveElt hM
  have hsu : ∀ u < surv.length, (((sq.getD u []).all (· < 3) = true ∧
      ∀ i < 4, (D.getD u []).getD i 0 < 2048) ∧
      zfSeqT (sq.getD u []) = zfP C (surv.getD u [])) ∧
      (∀ i : Fin 4, zfGv t₀ gW i * el5 (zfSeqW (sq.getD u [])) * zfGv t₀ gW i *
        (el5 (zfSeqW (sq.getD u [])))⁻¹ = eta uJ 11 ((D.getD u []).getD i 0)) ∧
      ((zfMasks Ts (D.getD u [])).isEmpty = true ∨
        (el5 (zfSeqW (sq.getD u [])) * el5 (zfSeqW (sq.getD u [])) = eta uJ 11 (E.getD u 0) ∧
          ∀ c ∈ zfMasks Ts (D.getD u []), (c ^^^ actT (zfSeqT (sq.getD u [])) c) = E.getD u 0)) := by
    intro u hu
    have h := List.all_eq_true.1 hsurv u (List.mem_range.2 hu)
    unfold zfSurvOK at h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
      List.mem_finRange, true_implies, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h0⟩, -⟩, h2⟩, h3⟩, h4⟩ := h
    have hs3 : ∀ g ∈ sq.getD u [], g < 3 := fun g hg' => by simpa using h1 g hg'
    have hd : ∀ i < 4, (D.getD u []).getD i 0 < 2048 := by
      intro i _
      by_cases hi' : i < (D.getD u []).length
      · rw [List.getD_eq_getElem _ _ hi']
        simpa using h0 _ (List.getElem_mem hi')
      · rw [List.getD_eq_default _ _ (by omega)]
        norm_num
    refine ⟨⟨⟨List.all_eq_true.2 fun x hx => decide_eq_true (h1 x hx), hd⟩, h2⟩, fun i => ?_, ?_⟩
    · apply Mx_injective
      rw [map_mul, map_mul, map_mul, hms i, Mx_zfSeq hM, Mx_zfSeq_inv hM _ hs3,
        Mx_eta hM 11 le_rfl, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
      exact congrArg rowsMatrix (eqRows_iff.1 (h3 i))
    · rcases h4 with h4 | ⟨h5, h6⟩
      · exact Or.inl h4
      · refine Or.inr ⟨?_, fun c hc => by simpa using h6 c hc⟩
        apply Mx_injective
        rw [map_mul, Mx_zfSeq hM, Mx_eta hM 11 le_rfl, ← rowsMatrix_mulRows]
        exact congrArg rowsMatrix (eqRows_iff.1 h5)
  have hs3 : ∀ u < surv.length, ∀ g ∈ sq.getD u [], g < 3 := fun u hu g hg' => by
    simpa using List.all_eq_true.1 (hsu u hu).1.1.1 g hg'
  have hacts : ∀ u < surv.length, Acts (el5 (zfSeqW (sq.getD u []))) (zfSeqT (sq.getD u [])) :=
    fun u hu => acts_zfSeq hM _ (hs3 u hu)
  have hD : ∀ u < surv.length, ∀ i < 4, (D.getD u []).getD i 0 < 2048 :=
    fun u hu => (hsu u hu).1.1.2
  set L := zfI Ts surv D with hL
  have hcomm_iff : ∀ q ∈ L, ∀ i : Fin 4, zfElt sq q * zfGv t₀ gW i = zfGv t₀ gW i * zfElt sq q := by
    intro q hq i
    obtain ⟨hu, hc⟩ := mem_zfI.1 hq
    obtain ⟨hc1, hc2⟩ := mem_zfMasks.1 hc
    exact (comm_iff_mask hM (hTs i) (hvsq i) (hD _ hu i i.2) ((hsu _ hu).2.1 i) hc1).2 (hc2 i i.2)
  have hcl : ∀ x : J, (∀ i, x * zfGv t₀ gW i = zfGv t₀ gW i * x) → x ∈ L.map (zfElt sq) := by
    intro x hx
    have hx1 : x * eta uJ 11 1 = eta uJ 11 1 * x := by
      rw [← hv0]
      exact hx 0
    obtain ⟨ts, hts, c, hc, rfl⟩ := zf_cover hF hG hC hprod x hx1
    have hA := acts_zfW hM C ts (zfChain_seq hC)
    have htab : ∀ i < 4, compT (zfP C ts) (Ts.getD i []) = compT (Ts.getD i []) (zfP C ts) :=
      fun i hi => table_comm_of_commute hM hA (hTs ⟨i, hi⟩) (hx ⟨i, hi⟩)
    have hmem : ts ∈ surv := by
      rw [← hbt]
      refine zfBt_complete hg hTsOK hC hts htab fun T hT => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
      rw [← List.getD_eq_getElem _ [] hi]
      exact htab i (by omega)
    obtain ⟨u, hu, hsu'⟩ := List.getElem_of_mem hmem
    have hsuv : surv.getD u [] = ts := by rw [List.getD_eq_getElem _ _ hu, hsu']
    set h := el5 (zfSeqW (sq.getD u [])) with hh
    have hinvA : Acts h⁻¹ (wordT (invW (zfSeqW (sq.getD u [])))) := by
      have hl := zfSeqW_letters _ (hs3 u hu)
      rw [hh, el5_inv hl, el5, wordProd_gen5_xJ _ (fun l hl' => by
        rw [invW_eq] at hl'
        simp only [invWord, List.mem_map, List.mem_reverse] at hl'
        obtain ⟨x, hx', rfl⟩ := hl'
        exact letters_neg x (hl x hx'))]
      refine Acts_wordProd hM _ fun l hl' => ?_
      rw [invW_eq] at hl'
      simp only [invWord, List.mem_map, List.mem_reverse] at hl'
      obtain ⟨x, hx', rfl⟩ := hl'
      exact letters_neg x (hl x hx')
    have hid : compT (zfSeqT (sq.getD u [])) (wordT (invW (zfSeqW (sq.getD u [])))) = idT := by
      have := (hacts u hu).mul hinvA
      rw [mul_inv_cancel] at this
      exact Acts.unique hM this Acts.one
    set z := el5 (zfW C ts) * h⁻¹ with hz
    have hzA : Acts z idT := by
      have := hA.mul hinvA
      have e1 : zfP C ts = zfSeqT (sq.getD u []) := by
        rw [← hsuv]
        exact (hsu u hu).1.2.symm
      rw [e1, hid] at this
      exact this
    obtain ⟨ts', hts', c', hc', hz'⟩ := zf_cover hF hG hC hprod z
      (comm_eta_one_of_acts hzA (actT_idT (by norm_num)))
    have hA' := (acts_zfW hM C ts' (zfChain_seq hC)).eta_mul hM (eta_mem_Eg 11 le_rfl c')
    rw [← hz'] at hA'
    have hP0 : zfP C ts' = zfP C (zfZero C) := by
      rw [(zfZero_facts hC).2.1]
      exact Acts.unique hM hA' hzA
    have hts0 : ts' = zfZero C :=
      zfP_inj hg (fun s hs' a ha b hb e => actT_inj_of_acts hM (acts_zfSeq hM s hs')
        (lt_two_pow_of_lt ha) (lt_two_pow_of_lt hb) e) hC ts' hts' _ (zfZero_facts hC).1 hP0
    rw [hts0, (zfZero_facts hC).2.2, el5_nil, mul_one] at hz'
    have he : el5 (zfW C ts) = eta uJ 11 c' * h := by
      calc el5 (zfW C ts) = z * h := by rw [hz]; group
        _ = eta uJ 11 c' * h := by rw [hz']
    have hxe : eta uJ 11 c * el5 (zfW C ts) = zfElt sq (u, c ^^^ c') := by
      unfold zfElt
      rw [he, ← mul_assoc, ← eta_xor (elem_uJ hM) le_rfl]
    rw [hxe] at hx ⊢
    refine List.mem_map.2 ⟨(u, c ^^^ c'), mem_zfI.2 ⟨hu, mem_zfMasks.2 ⟨xor_lt hc hc', fun i hi => ?_⟩⟩, rfl⟩
    exact (comm_iff_mask hM (hTs ⟨i, hi⟩) (hvsq ⟨i, hi⟩) (hD u hu i hi) ((hsu u hu).2.1 ⟨i, hi⟩)
      (xor_lt hc hc')).1 (hx ⟨i, hi⟩)
  have hsound : ∀ x ∈ L.map (zfElt sq), ∀ i, x * zfGv t₀ gW i = zfGv t₀ gW i * x := by
    intro x hx i
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact hcomm_iff q hq i
  have h2 : ∀ x ∈ L.map (zfElt sq), x ^ (2 ^ 1) = 1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hu, hc⟩ := mem_zfI.1 hq
    rcases (hsu _ hu).2.2 with h4 | ⟨h5, h6⟩
    · rw [List.isEmpty_iff] at h4
      rw [h4] at hc
      simp at hc
    · exact sq_of_mask hM (hacts _ hu) h5 (mem_zfMasks.1 hc).1 (h6 _ hc)
  have hnodup : (L.map (zfElt sq)).Nodup := by
    refine List.Nodup.map_on ?_ (nodup_zfI Ts surv D)
    intro q hq q' hq' e
    obtain ⟨hu, hc⟩ := mem_zfI.1 hq
    obtain ⟨hu', hc'⟩ := mem_zfI.1 hq'
    have hA1 := (hacts _ hu).eta_mul hM (eta_mem_Eg 11 le_rfl q.2)
    have hA2 := (hacts _ hu').eta_mul hM (eta_mem_Eg 11 le_rfl q'.2)
    have e' : eta uJ 11 q.2 * el5 (zfSeqW (sq.getD q.1 [])) =
        eta uJ 11 q'.2 * el5 (zfSeqW (sq.getD q'.1 [])) := e
    rw [e'] at hA1
    have htt := Acts.unique hM hA1 hA2
    have huu : q.1 = q'.1 := by
      have h1 : ((List.range surv.length).map fun u => zfSeqT (sq.getD u []))[q'.1]'(by simpa using hu')
          = ((List.range surv.length).map fun u => zfSeqT (sq.getD u []))[q.1]'(by simpa using hu) := by
        simp only [List.getElem_map, List.getElem_range]
        exact htt.symm
      exact ((List.Nodup.getElem_inj_iff hnd).1 h1).symm
    have hcc : eta uJ 11 q.2 = eta uJ 11 q'.2 := by
      rw [huu] at e'
      exact mul_right_cancel e'
    exact Prod.ext huu (eta_inj hM _ (lt_two_pow_of_lt (mem_zfMasks.1 hc).1) _
      (lt_two_pow_of_lt (mem_zfMasks.1 hc').1) hcc)
  have hR : List.Forall₂ (fun x r => Mx x = rowsMatrix r) (L.map (zfElt sq)) (L.map (zfRowsOf sq)) := by
    have key : ∀ l : List (ℕ × ℕ), List.Forall₂ (fun x r => Mx x = rowsMatrix r)
        (l.map (zfElt sq)) (l.map (zfRowsOf sq)) := by
      intro l
      induction l with
      | nil => exact List.Forall₂.nil
      | cons q l ih =>
        refine List.Forall₂.cons ?_ ih
        unfold zfElt zfRowsOf
        rw [map_mul, Mx_eta hM 11 le_rfl, Mx_zfSeq hM, ← rowsMatrix_mulRows]
        rfl
    exact key L
  have hRwf : ∀ r ∈ L.map (zfRowsOf sq), wfRows r = true := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hu, hc⟩ := mem_zfI.1 hq
    exact wfRows_mulRows (zEtaRows_wf _ (mem_zfMasks.1 hc).1) (wf_zfSeqR hG _ (hs3 _ hu))
  have hk : ((L.map (zfRowsOf sq)).filter
      fun r => eqRows (mulRows r (zYR gW)) (mulRows (zYR gW) r)).length ≤ k := by
    simpa [List.filter_map, List.length_map, Function.comp_def] using hkL
  have hidx : 16 * k < (L.map (zfElt sq)).length := by
    rw [List.length_map]
    exact hidxL
  have hclosure : ClassRad (Subgroup.closure (Set.range (zfGv t₀ gW))) :=
    classRad_of_zData4 (zfGv t₀ gW) (zMs T₀ gW) hms y (zYR gW) (zYiR gW) hY hYi hYwf zS hCm
      (fun i => by rw [← zProdRows_eq]; exact hS i) hy5 (m := 1) _ _ hcl hsound h2 hnodup hR hRwf hk
      hidx
  refine classRad_of_gens_fin4 (c := fun i : Fin 4 => zCj t₀ i) hV (el5 gW) ?_ ?_ hclosure
  · intro i
    obtain ⟨i, hi⟩ := i
    interval_cases i
    · change zfGvN t₀ gW 0 ∈ _
      have : zfGvN t₀ gW 0 = el5 gW * zCj t₀ 0 * (el5 gW)⁻¹ := hconj.symm
      rw [this]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
    · exact Subgroup.subset_closure ⟨3, rfl⟩
  · intro j
    obtain ⟨j, hj⟩ := j
    interval_cases j
    · change el5 gW * zCj t₀ 0 * (el5 gW)⁻¹ ∈ Subgroup.closure (Set.range (zfGv t₀ gW))
      have : el5 gW * t₀ * (el5 gW)⁻¹ = zfGvN t₀ gW 0 := hconj
      rw [show zCj t₀ 0 = t₀ from rfl, this]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
    · exact Subgroup.subset_closure ⟨3, rfl⟩

end CFSG.QuasithinUnique.A5

end
