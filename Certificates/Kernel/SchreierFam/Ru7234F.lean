module

public import Certificates.Kernel.SchreierFam.Ru7234K
public import Certificates.Kernel.RuInsp443.Facts
public import CFSG.Certificates.Kernel.Spor.BaseExt
public import CFSG.Certificates.Kernel.Spor.StrongOfFold
public import CFSG.Quasithin.Vol2.KGFactC31RuGens
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzCent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.Ru7234

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.RuInsp CFSG.KC.Misc.M64 CFSG.KC.BfsPin
  CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CertificateChecks.KernelRuInsp CFSG.Quasithin.KGC31

noncomputable abbrev U (p : Nat) : Array Nat := unpack 4060 12 p

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem getD_toArray_map {α β : Type} [Inhabited β] (f : α → β) (L : List α) (d : α) {j : Nat}
    (hj : j < L.length) : (L.map f).toArray[j]! = f (L.getD j d) := by
  rw [getElem!_pos _ j (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp

theorem cn_facts : (∀ j < 5, cn (S j) = true ∧ cn (SI j) = true) ∧ (∀ j < 12, cn (BB j) = true) ∧
    (∀ j < 10, cn (UU j) = true) ∧ cn (TT 0) = true ∧ (∀ k < 64, cn (SP k) = true) ∧
    cn ID = true ∧ idK 4060 12 (mask 12) = true ∧ Nat.beq (SP 0) ID = true := by
  have h := kCn
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun j hj => ?_, fun j hj => allN_spec h2 j hj, fun j hj => allN_spec h3 j hj, h4,
    fun k hk => allN_spec h5 k hk, h6, h7, h8⟩
  have := allN_spec h1 j hj
  simpa only [bAnd_iff] using this

theorem cnS {j : Nat} (hj : j < 5) : cn (S j) = true := (cn_facts.1 j hj).1
theorem cnSI {j : Nat} (hj : j < 5) : cn (SI j) = true := (cn_facts.1 j hj).2
theorem cnB {j : Nat} (hj : j < 12) : cn (BB j) = true := cn_facts.2.1 j hj
theorem cnU {j : Nat} (hj : j < 10) : cn (UU j) = true := cn_facts.2.2.1 j hj
theorem cnSP {k : Nat} (hk : k < 64) : cn (SP k) = true := cn_facts.2.2.2.2.1 k hk

theorem uid : U ID = idA 4060 := idK_sound cn_facts.2.2.2.2.2.2.1

theorem m64S_size : m64S.size = 5 := by simp [m64S, strongM64W]

theorem m64S_get {j : Nat} (hj : j < 5) : m64S[j]! = U (S j) := by
  rw [m64S, getD_toArray_map wA strongM64W [] (by simpa [strongM64W] using hj)]
  exact wA_eq (allN_spec kS j hj)

theorem m64S_inv {j : Nat} (hj : j < 5) : ruInv m64S[j]! = U (SI j) := by
  rw [m64S_get hj, ruInv]
  exact (invEqK_sound (allN_spec kP j hj)).1

theorem m64S_isInv {j : Nat} (hj : j < 5) : isInvA 4060 m64S[j]! (invCand 4060 m64S[j]!) = true := by
  have h := (invEqK_sound (allN_spec kP j hj))
  rw [m64S_get hj, h.1]
  exact h.2

theorem b64A_eq : b64A = BL.map U := by
  have hb : ∀ j < 6, wA (basis64W.getD j []) = U (BB j) := fun j hj => by
    have := allN_spec kB j hj
    rw [bAnd_iff] at this
    exact wA_eq this.1
  change [wA (basis64W.getD 0 []), wA (basis64W.getD 1 []), wA (basis64W.getD 2 []),
    wA (basis64W.getD 3 []), wA (basis64W.getD 4 []), wA (basis64W.getD 5 [])] = _
  rw [hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num),
    hb 4 (by norm_num), hb 5 (by norm_num)]
  rfl

theorem u33A_size : u33A.size = 5 := by simp [u33A, u33W]

theorem u33A_get {j : Nat} (hj : j < 5) : u33A[j]! = U (UU j) := by
  rw [u33A, getD_toArray_map wA u33W [] (by simpa [u33W] using hj)]
  have := allN_spec kU j hj
  rw [bAnd_iff] at this
  exact wA_eq this.1

theorem u33A_inv {j : Nat} (hj : j < 5) : invCand 4060 (U (UU j)) = U (UU (5 + j)) := by
  have := allN_spec kU j hj
  rw [bAnd_iff] at this
  exact (invEqK_sound this.2).1

theorem t64A_eq : t64A = U (TT 0) := wA_eq kT

theorem cn_BL : ∀ p ∈ BL, cn p = true := by
  intro p hp
  simp only [BL, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact cnB (by norm_num)

theorem sp64_eq : sp64 = (List.range 64).map fun k => U (SP k) := by
  rw [sp64, b64A_eq, spanA_eq BL cn_BL]
  refine List.map_congr_left fun k hk => ?_
  rw [Nat.eq_of_beq_eq_true (allN_spec kSP k (List.mem_range.1 hk))]
  rfl

theorem inA_of {x k : Nat} (hk : k < 64) (hx : cn x = true) (h : Nat.beq x (SP k) = true) :
    inA sp64 (U x) = true := by
  rw [inA, sp64_eq, List.any_eq_true]
  refine ⟨U (SP k), List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, ?_⟩
  rw [eqA_unpack (cnSP hk) hx, Nat.eq_of_beq_eq_true h]
  exact Nat.beq_refl _

theorem binds_of {PS : Nat → Nat} {nb BP : Nat} {base : Array Nat} (hS : ∀ j < 5, PS j = S j)
    (hbs : base.size = nb) (hb : ∀ t < nb, base[t]! = pg 12 (mask 12) BP t) :
    Binds 4060 12 PS 5 nb BP m64S base :=
  ⟨by norm_num, by norm_num, by norm_num, m64S_size, fun j hj => by rw [hS j hj]; exact m64S_get hj,
    hbs, hb⟩

theorem bindsS : Binds 4060 12 Ru7234S.S 5 2 Ru7234S.BP m64S #[0, 1] := by
  have h := kBase
  rw [bAnd_iff] at h
  exact binds_of (fun _ _ => rfl) rfl fun t ht => Nat.eq_of_beq_eq_true (allN_spec h.1 t ht)

theorem bindsX : Binds 4060 12 Ru7234X.S 5 4 Ru7234X.BP m64S #[0, 1, 2, 3] := by
  have h := kBase
  rw [bAnd_iff] at h
  exact binds_of (fun j hj => Nat.eq_of_beq_eq_true (allN_spec kSX j hj)) rfl
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec h.2 t ht)

theorem perm_m64S {j : Nat} (hj : j < 5) :
    permOfArr 4060 m64S[j]! = wG (strongM64W.getD j []) := by
  have e : m64S[j]! = wA (strongM64W.getD j []) :=
    getD_toArray_map wA strongM64W [] (by simpa [strongM64W] using hj)
  refine Rep.unique (rep_permOfArr (m64S_isInv hj)).1 ?_
  rw [e]
  exact rep_wA (by interval_cases j <;> decide)

theorem closure_le_ruP :
    Subgroup.closure {g : Equiv.Perm (Fin 4060) | ∃ j < m64S.size, permOfArr 4060 m64S[j]! = g} ≤
      ruP := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rw [m64S_size] at hj
  rw [perm_m64S hj]
  exact wG_mem _

theorem arr4 : ∀ v < 4, (#[0, 1, 2, 3] : Array Nat)[v]! = v := by
  intro v hv
  interval_cases v <;> rfl

theorem sepX :
    Sep 4060 m64S #[0, 1, 2, 3] := by
  intro G hG hfix
  refine CFSG.EvenSporadicStandard.Induction.RuSz.eq_one_of_fix_base (closure_le_ruP hG)
    fun x hx => ?_
  have hb := arr4 x.val hx
  have hlt : (#[0, 1, 2, 3] : Array Nat)[x.val]! < 4060 := by
    rw [hb]
    exact x.2
  have h := hfix x.val (by simpa using hx) hlt
  have e : (⟨(#[0, 1, 2, 3] : Array Nat)[x.val]!, hlt⟩ : Fin 4060) = x := Fin.ext hb
  rw [e] at h
  exact h

theorem chainX :
    rawChainOK 4060 (m64S.extract 0 5) m64S #[0, 1, 2, 3]
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 5 dM64) 4 = true :=
  rawChainTK_sound bindsX Ru7234X.head Ru7234X.tl Ru7234X.hst sepX Ru7234X.hs (by norm_num)

@[expose] def finL (l : List Nat) : List (Fin 4060) :=
  l.map fun x => ⟨x % 4060, Nat.mod_lt _ (by decide)⟩

theorem sepS :
    Sep 4060 m64S #[0, 1] := by
  refine sep_of_ext (by norm_num) (k := 5) (by rw [m64S_size]) (by norm_num)
    (base := finL [0, 1]) (ext := finL [0, 1, 2, 3]) (baseArr := #[0, 1])
    (extArr := #[0, 1, 2, 3]) (by decide) rfl rfl (by decide) chainX
    (fun i hi1 hi2 => ?_) sepX
  have hi : i < 4 := by simpa [finL] using hi2
  have hi2' : 2 ≤ i := by simpa [finL] using hi1
  rw [rawLevels_get (by simpa using hi), (levelTK_sound bindsX Ru7234X.head Ru7234X.tl hi).2]
  have h := allN_spec kLast (i - 2) (by omega)
  have e2 : Nat.add 2 (i - 2) = i := by
    rw [Nat.add_eq]
    omega
  rw [e2] at h
  exact Nat.eq_of_beq_eq_true h

theorem chainS :
    rawChainOK 4060 (m64S.extract 0 5) m64S #[0, 1]
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 5 dM64) 4 = true :=
  rawChainTK_sound bindsS Ru7234S.head Ru7234S.tl Ru7234S.hst sepS Ru7234S.hs (by norm_num)

theorem base_eq : arrBase m64B = #[0, 1] := by decide +kernel

theorem words_eq : noDer5 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 5 dM64 := by decide

theorem chain :
    rawChainOK 4060 (arrO m64S 5) m64S (arrBase m64B) noDer5 4 = true := by
  rw [base_eq, words_eq]
  exact chainS

theorem orbits : (rawOrbitSizes 4060 m64S (arrBase m64B)).prod = 387072 := by
  rw [base_eq, rawOrbitSizesTK_sound bindsS Ru7234S.head Ru7234S.tl]
  exact kProd

theorem mem_m64S {s : Array Nat} (hs : s ∈ m64S.toList) : ∃ j < 5, m64S[j]! = s := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hs
  have hj' : j < m64S.size := by simpa using hj
  refine ⟨j, m64S_size ▸ hj', ?_⟩
  rw [getElem!_pos m64S j hj']
  simpa using e

theorem mem_BL {b : Nat} (hb : b ∈ BL) : ∃ i < 6, BB i = b := by
  simp only [BL, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩
  · exact ⟨4, by norm_num, rfl⟩
  · exact ⟨5, by norm_num, rfl⟩

theorem norms : (m64S.toList.all fun s => normsA s (ruInv s) b64A sp64) = true := by
  rw [List.all_eq_true]
  intro s hs
  obtain ⟨j, hj, rfl⟩ := mem_m64S hs
  rw [m64S_inv hj, m64S_get hj, normsA, b64A_eq, List.all_eq_true]
  intro b hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  obtain ⟨i, hi, rfl⟩ := mem_BL hb'
  have hk := allN_spec (allN_spec kNorm j hj) i hi
  rw [bAnd_iff] at hk
  have c1 := canonK_pcomp (cnS hj) (cnB (by omega : i < 12))
  rw [cjA, compA_unpack (cnS hj) (cnB (by omega : i < 12)), compA_unpack c1 (cnSI hj)]
  exact inA_of (Nat.blt_eq.mp hk.1) (canonK_pcomp c1 (cnSI hj)) hk.2

noncomputable abbrev m64Ch : RawSchreierDatum 4060 :=
  arrChain (by norm_num) m64S 5 (by rw [m64S_size]) m64B (by decide) noDer5

theorem chainArr :
    ChainArrays m64Ch (arrO m64S 5) m64S (arrBase m64B) noDer5 :=
  arrChainArrays _ _ _ (chainCheckFacts chain)

theorem sift_of_word
    {w : List Int} {r : Nat}
    (h : wordEqK 4060 12 (mask 12) ID S SI 5 w r = true) : m64Sift (U r) = true := by
  have hS : m64S.size = 5 ∧ ∀ j < 5, m64S[j]! = unpack 4060 12 (S j) :=
    ⟨m64S_size, fun j hj => m64S_get hj⟩
  obtain ⟨e, hl⟩ := wordEqK_sound hS kP h
  have hrep : Rep 4060 (wordA 4060 m64S (rawInvs 4060 m64S) w)
      (Quiver.SchreierGraph.evalWord (fun h : Fin 5 => permOfArr 4060 m64S[(h : Nat)]!)
        (toLetters 5 w)) :=
    rep_wordA (gs := fun h => permOfArr 4060 m64S[h]!)
      (fun h hh => (rep_permOfArr (m64S_isInv hh)).1)
      (fun h hh => by
        rw [rawInvs_get (by rw [m64S_size]; exact hh)]
        exact (rep_permOfArr (m64S_isInv hh)).2) w hl
  rw [e] at hrep
  refine (siftA_iff_mem_originalSubgroup chainArr (by norm_num) chain hrep).2 ?_
  rw [arrChain_originalSubgroup]
  refine Subgroup.closure_mono ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact ⟨h.val, h.2, rfl⟩

theorem mem_of
    (i : Nat) (hi : i < 11) : m64Sift (U (MT i)) = true :=
  sift_of_word (allN_spec kMem i hi)

theorem sifts :
    b64A.all m64Sift = true ∧ u33A.toList.all m64Sift = true := by
  refine ⟨?_, ?_⟩
  · rw [b64A_eq, List.all_eq_true]
    intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, rfl⟩ := mem_BL hb'
    have h := mem_of i (by omega)
    interval_cases i <;> exact h
  · rw [List.all_eq_true]
    intro t ht
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 ht
    have hj5 : j < 5 := by simpa [u33A_size] using hj
    have et : t = U (UU j) := by
      rw [← u33A_get hj5, getElem!_pos u33A j (by simpa using hj)]
      simpa using e.symm
    rw [et]
    have h := mem_of (6 + j) (by omega)
    interval_cases j <;> exact h

theorem relA_fold : ∀ (r : List (Fin 5 × Bool)) (a : Nat), cn a = true →
    r.foldl (fun acc l => compA 4060 acc
        (if l.2 then u33A[l.1.val]! else ruInv u33A[l.1.val]!)) (U a) =
      U (r.foldl (fun acc l => pcomp 4060 12 (mask 12) acc
        (cond l.2 (UU l.1.val) (UU (5 + l.1.val)))) a) ∧
    cn (r.foldl (fun acc l => pcomp 4060 12 (mask 12) acc
        (cond l.2 (UU l.1.val) (UU (5 + l.1.val)))) a) = true
  | [], _, ha => ⟨rfl, ha⟩
  | l :: r, a, ha => by
    have hl : (if l.2 then u33A[l.1.val]! else ruInv u33A[l.1.val]!) =
        U (cond l.2 (UU l.1.val) (UU (5 + l.1.val))) ∧
        cn (cond l.2 (UU l.1.val) (UU (5 + l.1.val))) = true := by
      cases hb : l.2
      · exact ⟨by rw [if_neg (by simp), ruInv, u33A_get l.1.2, u33A_inv l.1.2]; rfl,
          cnU (by have := l.1.2; omega)⟩
      · exact ⟨by rw [if_pos rfl, u33A_get l.1.2]; rfl, cnU (by have := l.1.2; omega)⟩
    rw [List.foldl_cons, List.foldl_cons, hl.1, compA_unpack ha hl.2]
    exact relA_fold r _ (canonK_pcomp ha hl.2)

theorem relA_eq (r : List (Fin 5 × Bool)) : relA r = U (relK 4060 12 (mask 12) ID UU r) ∧
    cn (relK 4060 12 (mask 12) ID UU r) = true := by
  have h := relA_fold r ID cn_facts.2.2.2.2.2.1
  rw [uid] at h
  exact h

theorem rels : (CFSG.Quasithin.u33PresRels.all fun r => inA sp64 (relA r)) = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hr
  have hlen : CFSG.Quasithin.u33PresRels.length = 15 := by decide +kernel
  have h := (List.all_eq_true.1 kRel) t (List.mem_range.2 (hlen ▸ ht))
  rw [bAnd_iff] at h
  obtain ⟨e, hc⟩ := relA_eq (CFSG.Quasithin.u33PresRels.getD t [])
  rw [← List.getD_eq_getElem _ [] ht, e]
  exact inA_of (Nat.blt_eq.mp h.1) hc h.2

theorem uGens_bind : uGens.size = 11 ∧ ∀ l < 11, uGens[l]! = unpack 4060 12 (G11 l) := by
  have hb : ∀ j < 6, b64A.toArray[j]! = U (BB j) := fun j hj => by
    rw [b64A_eq, getElem!_pos _ j (by simpa [BL] using hj)]
    simp only [List.getElem_toArray, List.getElem_map]
    interval_cases j <;> rfl
  refine ⟨by simp [uGens, u33A_size, b64A_eq, BL], fun l hl => ?_⟩
  have e : uGens[l]! = if l < 5 then u33A[l]! else b64A.toArray[l - 5]! := by
    rw [uGens, getElem!_pos _ l (by simp [u33A_size, b64A_eq, BL]; omega)]
    split_ifs with h5
    · rw [Array.getElem_append_left (by rw [u33A_size]; exact h5), getElem!_pos u33A l
        (by rw [u33A_size]; exact h5)]
    · rw [Array.getElem_append_right (by rw [u33A_size]; omega), getElem!_pos _ (l - 5)
        (by simp [b64A_eq, BL]; omega)]
      simp [u33A_size]
  rw [e]
  split_ifs with h5
  · rw [u33A_get h5]
    interval_cases l <;> rfl
  · rw [hb (l - 5) (by omega)]
    interval_cases l <;> rfl

theorem ins : ((List.range 5).all fun j =>
    eqA 4060 (wordA 4060 uGens (uGens.map ruInv) (strongInU33W.getD j [])) m64S[j]!) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj5 : j < 5 := List.mem_range.1 hj
  obtain ⟨e, -⟩ := wordEqK_sound uGens_bind kG11 (allN_spec kIn j hj5)
  have e' : uGens.map ruInv = rawInvs 4060 uGens := rfl
  rw [e', e, m64S_get hj5, eqA_unpack (cnS hj5) (cnS hj5)]
  exact Nat.beq_refl _

theorem conj_of {i k : Nat} (h : conjOK i k = true) (hk : k < 64) :
    (conjT64W.any fun w => eqA 4060 (cjA (wM w) (ruInv (wM w)) t64A) (U (SP k))) = true := by
  unfold conjOK at h
  simp only [strictB_app, bAnd_iff] at h
  obtain ⟨hi, hw, hwi, hp, hc, hci, he⟩ := h
  have hi' : i < conjT64W.length := by
    have := Nat.blt_eq.mp hi
    simpa [conjT64W] using this
  have hS : m64S.size = 5 ∧ ∀ j < 5, m64S[j]! = unpack 4060 12 (S j) :=
    ⟨m64S_size, fun j hj => m64S_get hj⟩
  rw [List.any_eq_true]
  refine ⟨conjT64W.getD i [], by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi',
    ?_⟩
  have ew : wM (conjT64W.getD i []) = U (wS (conjT64W.getD i [])) :=
    (wordEqK_sound hS kP hw).1
  rw [ew, ruInv, (invEqK_sound hp).1, t64A_eq, cjA, compA_unpack hc cn_facts.2.2.2.1,
    compA_unpack (canonK_pcomp hc cn_facts.2.2.2.1) hci,
    eqA_unpack (canonK_pcomp (canonK_pcomp hc cn_facts.2.2.2.1) hci) (cnSP hk)]
  exact he

theorem trans : (sp64.all fun v => eqA 4060 v (idA 4060) ||
    conjT64W.any fun w => eqA 4060 (cjA (wM w) (ruInv (wM w)) t64A) v) = true := by
  rw [sp64_eq, List.all_eq_true]
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
  have hk' : k < 64 := List.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [← uid, eqA_unpack (cnSP (by norm_num)) cn_facts.2.2.2.2.2.1,
      cn_facts.2.2.2.2.2.2.2]
    rfl
  · have h := allN_spec kConj (k - 1) (by omega)
    have e : k - 1 + 1 = k := by omega
    rw [e] at h
    rw [conj_of h hk', Bool.or_true]

theorem m64Checks_true :
    m64Checks = true := by
  obtain ⟨h4, h5⟩ := sifts
  unfold m64Checks
  rw [chain, orbits, norms, h4, h5, rels, ins, trans]
  rfl

end CertificateChecks.KernelSchreierFam.Ru7234

end
