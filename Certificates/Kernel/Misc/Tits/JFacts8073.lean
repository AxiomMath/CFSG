
module

public import Certificates.Kernel.Misc.Tits.JTable8073

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN

abbrev Cn (p : Nat) : Prop := canonK 1755 11 (mask 11) (1755 * 11) p = true

theorem mem_of_siftJ {X : Nat} {g : Equiv.Perm (Fin 1755)} (hc : Cn X)
    (hr : Rep 1755 (unpack 1755 11 X) g) (h : siftJ X = true) : g ∈ titsJ := by
  obtain ⟨-, -, hX, hlt⟩ := CFSG.KS.SporSch.canonK_facts hc
  have hs := siftK_soundR bindsJ permJ TitsJ.hl rfl hX
    (allN_of_forall fun i hi => by rw [Nat.blt_eq]; exact hlt i hi) h
  exact mem_titsJ_of_sift hr hs

theorem z_mem : titsZ ∈ titsJ := by
  have e := (wordEqK_sound derBind permD zW).1
  have hr : Rep 1755 (unpack 1755 11 Z) titsZ := by
    rw [← e]
    exact titsZ_rep
  exact mem_of_siftJ zC hr zS

@[expose] noncomputable def hGen (k : ℕ) : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsHWords[k]!

@[expose] noncomputable def c0 : Equiv.Perm (Fin 1755) := wordIn 13 titsT [3, 4, 13]

@[expose] noncomputable def cc : Equiv.Perm (Fin 1755) := c0 * c0

theorem compA_idN {n : ℕ} {a : Array ℕ} (ha : a.size = n) : compA n a (idA n) = a := by
  apply Array.ext
  · rw [ha]
    exact Array.size_ofFn
  · intro i h1 h2
    have hi : i < n := by simpa [compA] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, compA_get hi, idA_get hi]

theorem compA_id {a : Array ℕ} (ha : a.size = 1755) : compA 1755 a (idA 1755) = a := compA_idN ha

theorem hWords_letters : ∀ w ∈ titsHWords, lettersOK 13 w = true := by decide
theorem jWords_letters : ∀ w ∈ titsJWords, lettersOK 13 w = true := by decide

theorem hGenArr {k : ℕ} (hk : k < 3) :
    jGenArrs[k]! = unpack 1755 11 (G k) ∧ Rep 1755 jGenArrs[k]! (hGen k) := by
  have e : jGenArrs[k]! = wordArr 1755 titsDerivedArrs titsHWords[k]! := by
    rw [jGenArrs, getElem!_pos _ k (by
      simp only [List.size_toArray, List.length_map, titsHWords, List.length_cons, List.length_nil]
      omega)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [getElem!_pos _ k (by
      simp only [titsHWords, List.length_cons, List.length_nil]
      omega)]
  have hl : lettersOK 13 titsHWords[k]! = true := by
    refine hWords_letters _ ?_
    rw [getElem!_pos _ k (by
      simp only [titsHWords, List.length_cons, List.length_nil]
      omega)]
    exact List.getElem_mem _
  refine ⟨?_, e ▸ rep_wordArr_titsT hl⟩
  rw [e]
  have hD : ∀ j < 13, titsDerivedArrs[j]!.size = 1755 := fun j hj => by
    rw [der_eq hj]
    simp [unpack]
  interval_cases k
  · change compA 1755 titsDerivedArrs[2]! (idA 1755) = unpack 1755 11 (TitsD.S 2)
    rw [compA_id (hD 2 (by norm_num)), der_eq (by norm_num)]
  · change compA 1755 titsDerivedArrs[3]! (idA 1755) = unpack 1755 11 (TitsD.S 3)
    rw [compA_id (hD 3 (by norm_num)), der_eq (by norm_num)]
  · change compA 1755 titsDerivedArrs[12]! (idA 1755) = unpack 1755 11 (TitsD.S 12)
    rw [compA_id (hD 12 (by norm_num)), der_eq (by norm_num)]

theorem cFacts : jC0Arr = unpack 1755 11 C0 ∧ jCArr = unpack 1755 11 C ∧ Rep 1755 jCArr cc ∧
    Cn C0 ∧ Cn C ∧ cc ^ 5 = 1 := by
  have h1 := cW
  have h2 := cC
  have h4 := c5
  have e0 : jC0Arr = unpack 1755 11 C0 := (wordEqK_sound derBind permD h1).1
  have r0 : Rep 1755 jC0Arr c0 := rep_wordArr_titsT (by decide)
  have cC : Cn C := cmpC h2 h2
  have eC : jCArr = unpack 1755 11 C := by
    rw [jCArr, e0, cmpU h2 h2]
    rfl
  have rC : Rep 1755 jCArr cc := rep_compA r0 r0
  refine ⟨e0, eC, rC, h2, cC, ?_⟩
  have r5 := rep_compA (rep_compA (rep_compA (rep_compA rC rC) rC) rC) rC
  have e5 : eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 jCArr jCArr) jCArr) jCArr)
      jCArr) (idA 1755) = true := by
    rw [eC, cmpU cC cC, cmpU (cmpC cC cC) cC, cmpU (cmpC (cmpC cC cC) cC) cC,
      cmpU (cmpC (cmpC (cmpC cC cC) cC) cC) cC,
      CertificateChecks.KernelSporSch.TitsCentral.id_eq,
      eqU (cmpC (cmpC (cmpC (cmpC cC cC) cC) cC) cC) CertificateChecks.KernelSporSch.TitsCentral.canId]
    exact h4
  have := (eqA_iff r5 rep_idA).1 e5
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  exact this

@[expose] noncomputable def gK (k : ℕ) : Equiv.Perm (Fin 1755) := if k < 3 then hGen k else cc

theorem gK_rep {k : ℕ} (hk : k < 4) : Rep 1755 (unpack 1755 11 (G k)) (gK k) := by
  by_cases h3 : k < 3
  · simp only [gK, h3, ↓reduceIte]
    rw [← (hGenArr h3).1]
    exact (hGenArr h3).2
  · have e : k = 3 := by omega
    subst e
    simp only [gK, h3, ↓reduceIte]
    change Rep 1755 (unpack 1755 11 C) cc
    rw [← cFacts.2.1]
    exact cFacts.2.2.1

theorem canK_at {k : ℕ} (hk : k < 4) : Cn (G k) ∧ Cn (GI k) ∧
    permOK 1755 11 (mask 11) (1755 * 11) (G k) (GI k) = true ∧ Cn (TitsJ.S k) :=
  ⟨allN_spec canG k hk, allN_spec canGI k hk, allN_spec permGK k hk, allN_spec canS k hk⟩

theorem conj_mem {k : ℕ} (hk : k < 4) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) :
    gK k * x * (gK k)⁻¹ ∈ titsJ := by
  obtain ⟨c1, c2, c3, -⟩ := canK_at hk
  have rg := gK_rep hk
  have rgi : Rep 1755 (unpack 1755 11 (GI k)) (gK k)⁻¹ :=
    rep_inv_of_isInvA rg (invEqK_sound (n := 1755) (w := 11) c3).2
  have hle : titsJ ≤ titsJ.comap (MulAut.conj (gK k)).toMonoidHom := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
    have hj4 : j < 4 := by simpa [titsJWords] using hj
    obtain ⟨w1, w2⟩ := (bAnd_iff _ _).1 (allN_spec wJ j hj4)
    have es := (wordEqK_sound derBind permD w1).1
    have hl : lettersOK 13 titsJWords[j] = true := jWords_letters _ (List.getElem_mem _)
    have rs : Rep 1755 (unpack 1755 11 (TitsJ.S j)) (wordIn 13 titsT titsJWords[j]) := by
      rw [← es, getElem!_pos titsJWords j hj]
      exact rep_wordArr_titsT hl
    obtain ⟨-, -, -, cS⟩ := canK_at hj4
    have cP : Cn (pcomp 1755 11 (mask 11) (G k) (TitsJ.S j)) := cmpC c1 cS
    have r := rep_compA (rep_compA rg rs) rgi
    rw [cmpU c1 cS, cmpU cP c2] at r
    have hm := mem_of_siftJ (cmpC cP c2) r (allN_spec (allN_spec nK k hk) j hj4)
    exact hm
  exact hle hx

theorem prod_pt {i j : ℕ} (hi : i < 512) (hj : j < 512) {p : ℕ} (hp : p < 1755) :
    (jPel[i]!)[(jPel[j]!)[p]!]! = ((el i * el j) (finPt 1755 p) : ℕ) := by
  rw [rep_base (el_rep hj) p hp, (el_rep hi) (el j (finPt 1755 p))]
  rfl

theorem gens_size : jGenArrs.size = 3 := by
  simp only [jGenArrs, List.size_toArray, List.length_map, titsHWords, List.length_cons,
    List.length_nil]

theorem mul_ok : (allLt 512 fun i => allLt 512 fun j => decide ((jMulT[i]!)[j]! < 512) &&
    titsJBase.all fun p => (jPel[(jMulT[i]!)[j]!]!)[p]! == (jPel[i]!)[(jPel[j]!)[p]!]!) =
    true := by
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  obtain ⟨k, hk, ek, ik⟩ := jIdx4_of (mul_mem (el_mem hi) (el_mem hj))
  have e : (jMulT[i]!)[j]! = k := by
    rw [jMulT, getElem!_ofFn_of_lt _ hi, getElem!_ofFn_of_lt _ hj]
    simp only [Fin.getElem!_fin]
    rw [prod_pt hi hj (p := 5) (by norm_num), prod_pt hi hj (p := 1) (by norm_num),
      prod_pt hi hj (p := 24) (by norm_num), prod_pt hi hj (p := 12) (by norm_num)]
    exact ik
  rw [e]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  refine ⟨hk, fun p hp => ?_⟩
  have hp' : p < 1755 := by
    simp only [titsJBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
    omega
  rw [prod_pt hi hj hp', rep_base (el_rep hk) p hp', ek]

theorem inv_ok : (allLt 512 fun i => decide (jInvT[i]! < 512) &&
    isInvA 1755 jPel[i]! (invCand 1755 jPel[i]!) &&
    eqA 1755 (invCand 1755 jPel[i]!) jPel[jInvT[i]!]!) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have ri := el_rep hi
  have rv := rep_invCandJ ri
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of rv (inv_mem (el_mem hi))
  have e : jInvT[i]! = k := by
    rw [jInvT, getElem!_ofFn_of_lt _ hi]
    exact ik
  rw [e]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hk, isInvA_invCand ri⟩, (eqA_iff rv (el_rep hk)).2 ek.symm⟩

theorem one_ok : jOneI < 512 ∧ eqA 1755 jPel[jOneI]! (idA 1755) = true := by
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of rep_idA (one_mem titsJ)
  have e : jOneI = k := ik
  rw [e]
  exact ⟨hk, (eqA_iff (el_rep hk) rep_idA).2 ek⟩

theorem z_ok : jZI < 512 ∧ eqA 1755 jPel[jZI]! jZArr = true := by
  have rz : Rep 1755 jZArr titsZ := titsZ_rep
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of rz z_mem
  have e : jZI = k := ik
  rw [e]
  exact ⟨hk, (eqA_iff (el_rep hk) rz).2 ek⟩

theorem dist_ok :
    (allLt 512 fun i => allLt 512 fun j => i == j || !(eqA 1755 jPel[i]! jPel[j]!)) = true := by
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  cases h : eqA 1755 jPel[i]! jPel[j]!
  · simp
  · have := el_inj hi hj ((eqA_iff (el_rep hi) (el_rep hj)).1 h)
    simp [this]

theorem genInv_get {k : ℕ} (hk : k < 3) : jGenInvArrs[k]! = invCand 1755 jGenArrs[k]! := by
  rw [jGenInvArrs, getElem!_map_of_lt (by rw [gens_size]; exact hk)]

theorem genInv_ok : (allLt 3 fun k => isInvA 1755 jGenArrs[k]! jGenInvArrs[k]!) = true :=
  allLt_iff.2 fun k hk => by
    rw [genInv_get hk]
    exact isInvA_invCand (hGenArr hk).2

theorem conj_tab {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hg : ∀ x ∈ titsJ, g * x * g⁻¹ ∈ titsJ) {i : ℕ} (hi : i < 512) :
    ∃ k < 512, jIdx (compA 1755 (compA 1755 a jPel[i]!) (invCand 1755 a)) = k ∧
      eqA 1755 (compA 1755 (compA 1755 a jPel[i]!) (invCand 1755 a)) jPel[k]! = true := by
  have r := rep_compA (rep_compA ha (el_rep hi)) (rep_invCandJ ha)
  obtain ⟨k, hk, ek, ik⟩ := jIdx_of r (hg _ (el_mem hi))
  exact ⟨k, hk, ik, (eqA_iff r (el_rep hk)).2 ek.symm⟩

theorem cj_ok : (allLt 3 fun k => allLt 512 fun i => decide ((jCjT[k]!)[i]! < 512) &&
    eqA 1755 (compA 1755 (compA 1755 jGenArrs[k]! jPel[i]!) jGenInvArrs[k]!)
      jPel[(jCjT[k]!)[i]!]!) = true := by
  refine allLt_iff.2 fun k hk => allLt_iff.2 fun i hi => ?_
  have hn : ∀ x ∈ titsJ, hGen k * x * (hGen k)⁻¹ ∈ titsJ := fun x hx => by
    have := conj_mem (k := k) (by omega) hx
    simpa only [gK, hk, ↓reduceIte] using this
  obtain ⟨m, hm, im, em⟩ := conj_tab (hGenArr hk).2 hn hi
  have e : (jCjT[k]!)[i]! = m := by
    rw [jCjT, getElem!_ofFn_of_lt _ hk, getElem!_ofFn_of_lt _ hi]
    simp only [Fin.getElem!_fin]
    rw [genInv_get hk]
    exact im
  rw [e, genInv_get hk]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hm, em⟩

theorem cInv_ok : isInvA 1755 jCArr jCInv = true := isInvA_invCand cFacts.2.2.1

theorem cc_ok : (allLt 512 fun i => decide (jCcT[i]! < 512) &&
    eqA 1755 (compA 1755 (compA 1755 jCArr jPel[i]!) jCInv) jPel[jCcT[i]!]!) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have h3 : ¬ (3 < 3) := by omega
  have hn : ∀ x ∈ titsJ, cc * x * cc⁻¹ ∈ titsJ := fun x hx => by
    have := conj_mem (k := 3) (by omega) hx
    simpa only [gK, h3, ↓reduceIte] using this
  obtain ⟨m, hm, im, em⟩ := conj_tab cFacts.2.2.1 hn hi
  have e : jCcT[i]! = m := by
    rw [jCcT, getElem!_ofFn_of_lt _ hi]
    exact im
  rw [e]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hm, em⟩

theorem c5_ok : eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 jCArr jCArr) jCArr) jCArr)
    jCArr) (idA 1755) = true := by
  have rC := cFacts.2.2.1
  refine (eqA_iff (rep_compA (rep_compA (rep_compA (rep_compA rC rC) rC) rC) rC) rep_idA).2 ?_
  have h := cFacts.2.2.2.2.2
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one] at h
  exact h

theorem table_facts :
    jPel.size = 512 ∧ titsJBase = [5, 1, 24, 12] ∧ jGenArrs.size = 3 ∧
    (allLt 512 fun i => allLt 512 fun j => decide ((jMulT[i]!)[j]! < 512) &&
      titsJBase.all fun p => (jPel[(jMulT[i]!)[j]!]!)[p]! == (jPel[i]!)[(jPel[j]!)[p]!]!) = true ∧
    (allLt 512 fun i => decide (jInvT[i]! < 512) &&
      isInvA 1755 jPel[i]! (invCand 1755 jPel[i]!) &&
      eqA 1755 (invCand 1755 jPel[i]!) jPel[jInvT[i]!]!) = true ∧
    jOneI < 512 ∧ eqA 1755 jPel[jOneI]! (idA 1755) = true ∧
    jZI < 512 ∧ eqA 1755 jPel[jZI]! jZArr = true ∧
    (allLt 512 fun i => allLt 512 fun j => i == j || !(eqA 1755 jPel[i]! jPel[j]!)) = true ∧
    (allLt 3 fun k => isInvA 1755 jGenArrs[k]! jGenInvArrs[k]!) = true ∧
    (allLt 3 fun k => allLt 512 fun i => decide ((jCjT[k]!)[i]! < 512) &&
      eqA 1755 (compA 1755 (compA 1755 jGenArrs[k]! jPel[i]!) jGenInvArrs[k]!)
        jPel[(jCjT[k]!)[i]!]!) = true ∧
    isInvA 1755 jCArr jCInv = true ∧
    (allLt 512 fun i => decide (jCcT[i]! < 512) &&
      eqA 1755 (compA 1755 (compA 1755 jCArr jPel[i]!) jCInv) jPel[jCcT[i]!]!) = true ∧
    eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 jCArr jCArr) jCArr) jCArr) jCArr)
      (idA 1755) = true :=
  ⟨jPel_size, rfl, gens_size, mul_ok, inv_ok, one_ok.1, one_ok.2, z_ok.1, z_ok.2, dist_ok,
    genInv_ok, cj_ok, cInv_ok, cc_ok, c5_ok⟩

end CertificateChecks.KernelMisc.TitsJT

end
