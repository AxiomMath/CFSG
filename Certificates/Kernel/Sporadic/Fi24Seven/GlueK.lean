module

public import Certificates.Kernel.Sporadic.Fi24Seven.Glue
public import Certificates.Kernel.Sporadic.Fi24Seven.LightK
public import Certificates.Kernel.Sporadic.Fi24Seven.DataI
public import CFSG.Certificates.Kernel.Spor.SlpInvSound
public import CFSG.Certificates.Kernel.Orders.He.RelsBind
import Certificates.Kernel.Sporadic.Fi24Br.K

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelF24S

open CFSG.KC.SlpM CFSG.KD.F24S CFSG.Sporadic.Fi24.Native CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative CFSG.HardMathSupport.Dickson.I271.Fi7

@[expose] def ChunksOK : Prop := GI = true ∧ ∀ k < nK, CK k = true ∨ CKI k = true

open CFSG.KS.Mat3 in
theorem gens_facts (hg : GI = true) :
    mat3 781 609961 (CFSG.KD.BrFi24.RB 23) * mat3 781 609961 (CFSG.KD.BrFi24.RB 23) = 1 ∧
      mat3 781 609961 (CFSG.KD.BrFi24.RB 24) *
        (mat3 781 609961 (CFSG.KD.BrFi24.RB 24) * mat3 781 609961 (CFSG.KD.BrFi24.RB 24)) = 1 := by
  unfold GI at hg
  obtain ⟨h1, h2⟩ := (andB_iff _ _).1 hg
  have a : mat3 781 609961 (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 23)) =
      mat3 781 609961 (CFSG.KD.BrFi24.RB 23) * mat3 781 609961 (CFSG.KD.BrFi24.RB 23) :=
    (KernelFi24Ext.mul_mt KernelFi24Ext.cn_A KernelFi24Ext.cn_A).2
  have b : mat3 781 609961 (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24) (R 0)) =
      mat3 781 609961 (CFSG.KD.BrFi24.RB 24) * mat3 781 609961 (R 0) :=
    (KernelFi24Ext.mul_mt KernelFi24Ext.cn_B cn_B2.1).2
  have one : mat3 781 609961 CFSG.KD.BrFi24.ONE = 1 := KernelFi24Ext.mt_one
  rw [Nat.eq_of_beq_eq_true h1, one] at a
  rw [Nat.eq_of_beq_eq_true h2, one, cn_B2.2] at b
  exact ⟨a.symm, b.symm⟩

theorem letters_pos : ∀ l, ∀ w ∈ WL l, ∀ c ∈ w, 0 < c / 2 := by
  have h7 := slpC_pos slp7
  have hK := slpC_pos slpK
  intro l w hw c hc
  rcases wl_cases l with e | e | e <;> rw [e] at hw
  · exact h7 w (by rw [appL_eq]; exact List.mem_append_left _ hw) c hc
  · exact h7 w hw c hc
  · exact hK w hw c hc

theorem factsI (hk : ChunksOK) :
    ∀ k < nK, (∀ e ∈ eqK k, semE gW (WL (lyK k)) e.1 = semE gW (WL (lyK k)) e.2) ∧
      ∀ e ∈ neK k, semE gW (WL (lyK k)) e.1 ≠ semE gW (WL (lyK k)) e.2 := by
  have hg := gens_facts hk.1
  have := (slp_recordsI (d := 781) (f := 11) CFSG.KD.BrFi24.consts
    ⟨KernelFi24Ext.cn_A, rfl⟩ ⟨KernelFi24Ext.cn_B, rfl⟩ cn_B2 hg.1 hg.2 (WL := WL) (base := 2174)
    (fun l l' n hn => by rw [semN_base _ l hn, semN_base _ l' hn]) letters_pos (K := nK) (nR := nR)
    (R := R) (LY := lyK) (PC := pcR) (PN := pnR) (IN := inK) (OU := ouK) (ND := ndK) (EQ := eqK)
    (NE := neK) (fun k h => hk.2 k h) plan_ok).2
  rw [gen_eq] at this
  exact this

noncomputable abbrev WsK : Array (List Int) := (W7.map decW).toArray ++ (EK.map decW).toArray

noncomputable abbrev SK : Array Mat781 := semArr gW WsK

theorem wsK_eq : WsK = ((WL 2).map decW).toArray := layer_words EK

theorem slp_wsK : CFSG.Sporadic.Fi23.Native.slpOK WsK = true := by
  rw [wsK_eq]
  exact slpOK_of_slpC slpK

theorem wsK_size : WsK.size = 3820 := by
  simp [WsK, w7_len, ek_len]

theorem goodK {k : Nat} (hk : k < 7640) : Good (mLetters WsK)[k]! (SK.getD k 1) := by
  obtain ⟨⟨-, hI⟩, hs⟩ := mLetters_good slp_wsK
  exact hI k (by rw [hs, wsK_size]; omega)

theorem semEK (u : List Nat) : semE gW (WL 2) u = semWord gW SK (decW u) := by
  unfold semE
  rw [← wsK_eq]

theorem letterK {j : Nat} (hj : 2 < j) : semLetter gW SK (j : Int) = SK.getD (2 * (j - 3)) 1 := by
  unfold semLetter
  rw [if_neg (by simp; omega), if_pos (by omega)]
  simp

theorem letterK_neg {j : Nat} (hj : 2 < j) :
    semLetter gW SK (-(j : Int)) = SK.getD (2 * (j - 3) + 1) 1 := by
  unfold semLetter
  rw [if_neg (by simp; omega), if_neg (by omega)]
  simp

theorem decC_wc (j : Nat) : decC (wc j) = ((j + 3 : Nat) : Int) := decC_even rfl

theorem getD_sub3 (j : Nat) : SK.getD (2 * (j + 3 - 3)) 1 = SK.getD (2 * j) 1 := by
  rw [Nat.add_sub_cancel]

theorem wordK1 (j : Nat) : semWord gW SK (decW [wc j]) = SK.getD (2 * j) 1 := by
  rw [show decW [wc j] = [decC (wc j)] from rfl, decC_wc, semWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, letterK (by omega), getD_sub3]

theorem wordK2 (i j : Nat) :
    semWord gW SK (decW [wc i, wc j]) = SK.getD (2 * i) 1 * SK.getD (2 * j) 1 := by
  rw [show decW [wc i, wc j] = [decC (wc i), decC (wc j)] from rfl, decC_wc, decC_wc, semWord,
    List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one, letterK (by omega), letterK (by omega), getD_sub3, getD_sub3]

theorem wordKoh (h lam : Nat) :
    semWord gW SK (decW (wc h :: wc 64 :: List.replicate lam (wc 66))) =
      SK.getD (2 * h) 1 * (SK.getD 128 1 * SK.getD 132 1 ^ lam) := by
  have e : ∀ n, decW (List.replicate n (wc 66)) = List.replicate n (((66 + 3 : Nat) : Int)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ, ← ih]
      exact congrArg (· :: decW (List.replicate n (wc 66))) (decC_wc 66)
  rw [show decW (wc h :: wc 64 :: List.replicate lam (wc 66)) =
    decC (wc h) :: decC (wc 64) :: decW (List.replicate lam (wc 66)) from rfl, decC_wc, decC_wc, e,
    semWord, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, List.map_replicate,
    List.prod_replicate, letterK (by omega), letterK (by omega), letterK (by omega), getD_sub3,
    getD_sub3, getD_sub3]

theorem relC_cons (x y : Nat) (l : Nat × Bool) (v : List (Nat × Bool)) :
    relC x y (l :: v) = (2 * ((if l.1 = 0 then x else y) + 3) + (if l.2 then 0 else 1)) :: relC x y v := by
  obtain ⟨i, e⟩ := l
  have hb : Nat.beq i 0 = decide (i = 0) := by cases i <;> rfl
  change List.cons (Nat.add (Nat.mul 2 (Nat.add (Bool.rec y x (Nat.beq i 0)) 3)) (Bool.rec 1 0 e)) _ = _
  rw [hb]
  by_cases hi : i = 0 <;> cases e <;> simp [hi] <;> rfl

theorem decW_relC (x y : Nat) (v : List (Nat × Bool)) : decW (relC x y v) = v.map (heLetter x y) := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [relC_cons, List.map_cons, ← ih]
    change decC _ :: decW (relC x y v) = heLetter x y l :: decW (relC x y v)
    congr 1
    obtain ⟨i, e⟩ := l
    unfold heLetter
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decC_odd (j := (if i = 0 then x else y) + 3) rfl]
    · simp only [↓reduceIte, Nat.add_zero]
      rw [decC_even (j := (if i = 0 then x else y) + 3) rfl]

theorem eqK_fact {e : List Nat × List Nat} (hk : ChunksOK)
    (h : hasEq lyK eqK nK 2 e = true) : semWord gW SK (decW e.1) = semWord gW SK (decW e.2) := by
  rw [← semEK, ← semEK]
  obtain ⟨k, hkK, hl, he⟩ := hasEq_spec h
  have := (factsI hk k hkK).1 e he
  rwa [hl] at this

theorem neK_fact {e : List Nat × List Nat} (hk : ChunksOK)
    (h : hasEq lyK neK nK 2 e = true) : semWord gW SK (decW e.1) ≠ semWord gW SK (decW e.2) := by
  rw [← semEK, ← semEK]
  obtain ⟨k, hkK, hl, he⟩ := hasEq_spec h
  have := (factsI hk k hkK).2 e he
  rwa [hl] at this

theorem hasK {e : List Nat × List Nat} (he : e ∈ eqsK) : hasEq lyK eqK nK 2 e = true :=
  allL_spec eqsK_ok e he

theorem nthW_eq (W : List (List Nat)) (j : Nat) : nthW W j = W.getD j [] := by
  induction W generalizing j with
  | nil => rfl
  | cons w W ih =>
    cases j with
    | zero => rfl
    | succ j => change nthW W j = _; rw [ih]; rfl

theorem decW_get (W : List (List Nat)) (i : Nat) : (W.map decW).toArray[i]! = decW (nthW W i) := by
  rw [nthW_eq]
  by_cases h : i < W.length
  · rw [getElem!_pos _ i (by simpa using h), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ h]
  · rw [getElem!_neg _ i (by simpa using h), List.getD_eq_default _ _ (by omega)]
    rfl

theorem memN_spec {n : Nat} : ∀ {l : List Nat}, memN n l = true → n ∈ l
  | [], h => by simp [memN] at h
  | m :: l, h => by
    rcases (orB_iff _ _).1 h with h1 | h1
    · rw [Nat.eq_of_beq_eq_true h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memN_spec h1)

theorem secOK_of_secC {W : List (List Nat)} {gs : List Nat} {lo hi : Nat}
    (h : secC W gs lo hi = true) : secOK (W.map decW).toArray gs lo hi = true := by
  unfold secOK
  rw [List.all_eq_true]
  intro r hr
  rw [List.mem_range] at hr
  have h1 := allL_spec (allLt_spec h r hr)
  rw [List.all_eq_true]
  intro z hz
  rw [decW_get] at hz
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
  have h2 := h1 c hc
  have hs : Nat.shiftRight c 1 = c / 2 := by change c >>> 1 = _; rw [Nat.shiftRight_eq_div_pow]
  dsimp only at h2
  rw [hs] at h2
  obtain ⟨a1, a2⟩ := (andB_iff _ _).1 h2
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decC_natAbs]
  refine ⟨Nat.le_of_ble_eq_true a1, ?_⟩
  rcases (orB_iff _ _).1 a2 with e | e
  · exact Or.inl (List.contains_iff_mem.2 (memN_spec e))
  · obtain ⟨b1, b2⟩ := (andB_iff _ _).1 e
    exact Or.inr ⟨Nat.le_of_ble_eq_true b1, blt_true b2⟩

set_option maxHeartbeats 0 in
theorem header_ok : headerOK (EK.map decW).toArray = true := by
  unfold headerOK
  simp only [conj_eq]
  decide +kernel

theorem mixed_ok (hk : ChunksOK) :
    mixedSecs.all (mixedOK WsK (mLetters WsK)) = true := by
  rw [List.all_eq_true]
  intro m hm
  have hd := allL_spec mixedDataC_ok m hm
  unfold mixedDataC at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hd
  obtain ⟨hs0, h1, h2, h3, h4, h5⟩ := hd
  have hs : secOK WsK m.gs m.lo m.hi = true := by rw [wsK_eq]; exact secOK_of_secC hs0
  have ea := eqK_fact hk (hasK (e := ([wc m.ia], [wc 0])) (by
    simp only [eqsK, List.mem_append, List.mem_flatten, List.mem_map]
    exact Or.inl (Or.inr ⟨_, ⟨m, hm, rfl⟩, by simp⟩)))
  have eb := eqK_fact hk (hasK (e := ([wc m.ib], [wc 1])) (by
    simp only [eqsK, List.mem_append, List.mem_flatten, List.mem_map]
    exact Or.inl (Or.inr ⟨_, ⟨m, hm, rfl⟩, by simp⟩)))
  dsimp only at ea eb
  rw [wordK1, wordK1] at ea eb
  unfold mixedOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hs, h1, h2, h3, h4, ?_, ?_⟩
  · exact eqRows_of_good ((goodK (k := 2 * m.ia) (by omega)).congr ea) (goodK (k := 0) (by norm_num))
  · exact eqRows_of_good ((goodK (k := 2 * m.ib) (by omega)).congr eb) (goodK (k := 2) (by norm_num))

theorem pure_ok (hk : ChunksOK) :
    pureSecs.all (pureOK WsK (mLetters WsK) TauCeti.Sporadic.hePresentation.relatorLetters) = true := by
  rw [CFSG.KD.OrdHe.rels_eq, List.all_eq_true]
  intro p hp
  have hd := allL_spec pureDataC_ok p hp
  unfold pureDataC at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hd
  obtain ⟨hc1, hc2, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := hd
  have hs1 : secOK WsK (pureGens p.lam) p.lo p.hi = true := by rw [wsK_eq]; exact secOK_of_secC hc1
  have hs2 : secOK WsK [p.ix, p.iy] p.hi p.hi2 = true := by rw [wsK_eq]; exact secOK_of_secC hc2
  have hmem : ∀ e ∈ pureEqs p, e ∈ eqsK := fun e he => by
    simp only [eqsK, List.mem_append, List.mem_flatten, List.mem_map]
    exact Or.inr ⟨_, ⟨p, hp, rfl⟩, he⟩
  have eX := eqK_fact hk (hasK (hmem ([wc p.oX], [wc 64]) (by simp [pureEqs])))
  have eY := eqK_fact hk (hasK (hmem ([wc p.oY], [wc 66]) (by simp [pureEqs])))
  have eH := eqK_fact hk (hasK (hmem (wc p.oh :: wc 64 :: List.replicate p.lam (wc 66),
    [wc 67, wc p.oh]) (by simp [pureEqs])))
  dsimp only at eX eY eH
  rw [wordK1, wordK1] at eX eY
  rw [wordKoh, wordK2] at eH
  have hne := neK_fact hk (allL_spec nesK_ok p hp)
  dsimp only at hne
  rw [wordK1] at hne
  have hrel : ∀ v ∈ CFSG.KD.OrdHe.rels, semWord gW SK (v.map (heLetter p.ix p.iy)) = 1 := by
    intro v hv
    have := eqK_fact hk (allL_spec (allL_spec relsK_ok p hp) v hv)
    dsimp only at this
    rwa [decW_relC] at this
  have ok : ∀ v ∈ CFSG.KD.OrdHe.rels, ∀ z ∈ v.map (heLetter p.ix p.iy), OkZ WsK.size z := by
    intro v _ z hz
    obtain ⟨⟨i, e⟩, -, rfl⟩ := List.mem_map.1 hz
    unfold OkZ heLetter
    rw [wsK_size]
    right
    dsimp only
    split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega
  unfold pureOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hs1, hs2, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro v hv
    exact eqRows_of_good ((mWord_good slp_wsK (ok v hv)).congr (hrel v hv)) good_idW
  · rw [eqRows_false_of_good (goodK (k := 2 * p.ix) (by omega)) good_idW hne]
    rfl
  · exact eqRows_of_good ((goodK (k := 2 * p.oX) (by omega)).congr eX) (goodK (k := 128) (by norm_num))
  · exact eqRows_of_good ((goodK (k := 2 * p.oY) (by omega)).congr eY) (goodK (k := 132) (by norm_num))
  · exact eqRows_of_good
      (((goodK (k := 2 * p.oh) (by omega)).mulW ((goodK (k := 128) (by norm_num)).mulW
        (good_powW (goodK (k := 132) (by norm_num)) p.lam))).congr eH)
      ((goodK (k := 134) (by norm_num)).mulW (goodK (k := 2 * p.oh) (by omega)))

theorem fi24kOK_of (hk : ChunksOK) : fi24kOK () = true := by
  have c (i j : Nat) (hij : ([wc i, wc j], [wc j, wc i]) ∈ eqsK) :
      SK.getD (2 * i) 1 * SK.getD (2 * j) 1 = SK.getD (2 * j) 1 * SK.getD (2 * i) 1 := by
    have := eqK_fact hk (hasK hij)
    dsimp only at this
    rwa [wordK2, wordK2] at this
  have r (i j : Nat) (hi : i < 3820) (hj : j < 3820) (hij : ([wc i, wc j], [wc j, wc i]) ∈ eqsK) :
      eqRows 781 (mulW (mLetters WsK)[2 * i]! (mLetters WsK)[2 * j]!)
        (mulW (mLetters WsK)[2 * j]! (mLetters WsK)[2 * i]!) = true :=
    eqRows_of_good (((goodK (k := 2 * i) (by omega)).mulW (goodK (k := 2 * j) (by omega))).congr
      (c i j hij)) ((goodK (k := 2 * j) (by omega)).mulW (goodK (k := 2 * i) (by omega)))
  unfold fi24kOK
  simp only [words_eq, extraK_eq]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨slp_wsK, by simp [w7_len], by simp [ek_len], by decide +kernel, by decide +kernel,
    header_ok, r 1085 67 (by norm_num) (by norm_num) (by simp [eqsK]),
    r 1086 67 (by norm_num) (by norm_num) (by simp [eqsK]),
    r 1082 66 (by norm_num) (by norm_num) (by simp [eqsK]),
    r 1083 66 (by norm_num) (by norm_num) (by simp [eqsK]),
    r 1084 66 (by norm_num) (by norm_num) (by simp [eqsK]), mixed_ok hk, pure_ok hk⟩

end CertificateChecks.KernelF24S

end
