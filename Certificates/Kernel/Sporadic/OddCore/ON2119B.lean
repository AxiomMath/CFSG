module

public import Certificates.Kernel.Sporadic.ON3.Strong
public import CFSG.Sporadic.Schreier.ONLocalOrders
public import CFSG.Sporadic.ONOddCore.InvolutionCheckInputs

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelSpor.ON2119

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3
open CertificateChecks.KernelSpor.ON (TT UU)

@[expose] def Good
    (t : Array Nat) (F : Nat → Nat) : Prop :=
  t.size = 245520 ∧ (∃ g ∈ Pv, PRep N t g) ∧ ∀ x < 245520, t[x]! = F x ∧ F x < 245520

section Good


theorem good_word {w : List Int} (hw : plettersOK 7 w = true) :
    Good (wordArr w) (fun x => w.foldr (GZ TT UU) x) := by
  have hl : Let7 w := by
    intro l hl
    simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    exact hw l hl
  exact ⟨pword_size _, ⟨evalS w, evalS_mem w, prep_wordArr hw⟩, fun x hx => wordArr_get hl hx⟩

theorem good_pid : Good (pid nPts) (fun x => x) :=
  ⟨by simp [pid, nPts], ⟨1, one_mem _, prep_pid⟩, fun x hx => ⟨pid_get' hx, hx⟩⟩

theorem good_pcomp {t u : Array Nat} {F G : Nat → Nat} (ht : Good t F) (hu : Good u G) :
    Good (pcomp nPts t u) (fun x => F (G x)) := by
  obtain ⟨-, ⟨g, hg, hpg⟩, hF⟩ := ht
  obtain ⟨-, ⟨h, hh, hph⟩, hG⟩ := hu
  refine ⟨by simp [pcomp, nPts], ⟨g * h, mul_mem hg hh, prep_pcomp hpg hph⟩, fun x hx => ?_⟩
  rw [pcomp_get' hx, (hG x hx).1, (hF _ (hG x hx).2).1]
  exact ⟨rfl, (hF _ (hG x hx).2).2⟩

theorem good_inv {t : Array Nat} {F U : Nat → Nat} (ht : Good t F)
    (hU : ∀ x < 245520, U x < 245520 ∧ U (F x) = x) :
    Good (pinvCand nPts t) U ∧ pisInv nPts t (pinvCand nPts t) = true := by
  obtain ⟨hs, ⟨g, hg, hpg⟩, hF⟩ := ht
  have e : t = Array.ofFn (n := 245520) fun i => F i.val := arr_ext hs fun x hx => (hF x hx).1
  have hget : ∀ y < 245520, (pinvCand nPts t)[y]! = U y := fun y hy => by
    rw [e]
    exact CFSG.KS.CB.pinvCand_get (fun x hx => (hF x hx).2) (fun x hx => (hU x hx).2) hy
  have hinv : pisInv nPts t (pinvCand nPts t) = true := by
    unfold pisInv
    rw [allBelowN_iff]
    intro i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hi' : i < 245520 := hi
    rw [(hF i hi').1, hget _ (hF i hi').2, (hU i hi').2]
    exact ⟨(hF i hi').2, rfl⟩
  have hsz : (pinvCand nPts t).size = 245520 := by
    have heq : pinvCand nPts t = (List.range' 0 nPts).foldl (fun r i => r.set! t[i]! i)
        (Array.replicate nPts 0) := by
      unfold pinvCand
      simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        List.forIn_pure_yield_eq_foldl]
    have hfold : ∀ (l : List Nat) (r : Array Nat),
        (l.foldl (fun r i => r.set! t[i]! i) r).size = r.size := by
      intro l
      induction l with
      | nil => intro r; rfl
      | cons a l ih =>
        intro r
        rw [List.foldl_cons, ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    rw [heq, hfold, Array.size_replicate]
  exact ⟨⟨hsz, ⟨g⁻¹, inv_mem hg, prep_inv_of_pisInv hpg hinv⟩,
    fun y hy => ⟨hget y hy, (hU y hy).1⟩⟩, hinv⟩

theorem good_pword {S Si : Array (Array Nat)} {G GI : Nat → Nat → Nat} {k : Nat}
    (hS : ∀ h < k, Good S[h]! (G h)) (hSi : ∀ h < k, Good Si[h]! (GI h)) :
    ∀ w : List Int, plettersOK k w = true →
      Good (pword nPts S Si w) (fun x => w.foldr (GZ G GI) x)
  | [], _ => good_pid
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlk⟩, hw'⟩ := hw
    have ih := good_pword hS hSi w (by simpa [plettersOK] using hw')
    have hlet : Good (pletter S Si l) (GZ G GI l) := by
      unfold pletter
      by_cases hp : 0 < l
      · have e : GZ G GI l = G (l.toNat - 1) := by
          funext y
          simp [GZ, hp]
        simp only [hp, ↓reduceIte]
        rw [e]
        exact hS _ (by omega)
      · have e : GZ G GI l = GI ((-l).toNat - 1) := by
          funext y
          simp [GZ, hp]
        simp only [hp, ↓reduceIte]
        rw [e]
        exact hSi _ (by omega)
    exact good_pcomp hlet ih

theorem prodArr_nil (n : Nat) (gs : Array (Array Nat)) : prodArr n gs [] = pid n := rfl

theorem prodArr_cons (n : Nat) (gs : Array (Array Nat)) (j : Nat) (w : List Nat) :
    prodArr n gs (j :: w) = pcomp n gs[j]! (prodArr n gs w) := rfl

theorem repeat_zero {α : Type} (f : α → α) (a : α) : Nat.repeat f 0 a = a := rfl

theorem repeat_succ {α : Type} (f : α → α) (m : Nat) (a : α) :
    Nat.repeat f (m + 1) a = f (Nat.repeat f m a) := rfl

theorem good_prodArr {gs : Array (Array Nat)} {G : Nat → Nat → Nat} {k : Nat}
    (hgs : ∀ j < k, Good gs[j]! (G j)) (w : List Nat) (hw : ∀ j ∈ w, j < k) :
    Good (prodArr nPts gs w) (fun x => w.foldr (fun j y => G j y) x) := by
  induction w with
  | nil =>
    rw [prodArr_nil]
    exact good_pid
  | cons j w ih =>
    have h := good_pcomp (hgs j (hw j List.mem_cons_self))
      (ih fun i hi => hw i (List.mem_cons_of_mem _ hi))
    rw [prodArr_cons]
    exact h

theorem good_repeat {t : Array Nat} {F : Nat → Nat} (ht : Good t F) (m : Nat) :
    Good (Nat.repeat (pcomp nPts t) m (pid nPts)) (fun x => Nat.repeat F m x) := by
  induction m with
  | zero =>
    rw [repeat_zero]
    exact good_pid
  | succ m ih =>
    have h := good_pcomp ht ih
    rw [repeat_succ]
    exact h

theorem peq_good {t u : Array Nat} {F G : Nat → Nat} (ht : Good t F) (hu : Good u G)
    (h0 : F 0 = G 0) (h1 : F 227759 = G 227759) (h2 : F 100817 = G 100817) :
    peq nPts t u = true := by
  obtain ⟨-, ⟨g, hg, hpg⟩, hF⟩ := ht
  obtain ⟨-, ⟨h, hh, hph⟩, hG⟩ := hu
  refine (peq_iff hpg hph).2 (eq_of_three hg hh ?_ ?_ ?_) <;> apply Fin.ext <;>
    rw [← hpg, ← hph]
  · rw [(hF 0 (by norm_num)).1, (hG 0 (by norm_num)).1, h0]
  · rw [(hF 227759 (by norm_num)).1, (hG 227759 (by norm_num)).1, h1]
  · rw [(hF 100817 (by norm_num)).1, (hG 100817 (by norm_num)).1, h2]

theorem peq_good_false {t u : Array Nat} {F G : Nat → Nat} (ht : Good t F) (hu : Good u G)
    {x : Nat} (hx : x < 245520) (h : F x ≠ G x) : peq nPts t u = false := by
  rw [Bool.eq_false_iff]
  intro hp
  have := allBelowN_spec hp hx
  rw [beq_iff_eq, (ht.2.2 x hx).1, (hu.2.2 x hx).1] at this
  exact h this

@[expose] def bW (h : Nat) : List Int := if h < 3 then Data.MWords[h]! else Data.pairConjugatorWord

@[expose] noncomputable def bF (h x : Nat) : Nat := (bW h).foldr (GZ TT UU) x

@[expose] noncomputable def bFI (h x : Nat) : Nat := (invW (bW h)).foldr (GZ TT UU) x

@[expose] noncomputable def tF (j x : Nat) : Nat := (Data.TWords[j]!).foldr (GZ TT UU) x

theorem bW_let {h : Nat} (hh : h < 4) : plettersOK 7 (bW h) = true ∧ LetM 7 (bW h) := by
  interval_cases h <;> exact ⟨by decide, fun l hl => by revert l; decide⟩

theorem bW_pair : InvPair 245520 4 bF bFI := by
  intro h hh y hy
  obtain ⟨a, b, c, d⟩ := invPair_word tt_pair (bW_let hh).2 y hy
  exact ⟨a, b, c, d⟩

theorem mw_size : Data.MWords.size = 3 := by decide +kernel

theorem tw_size : Data.TWords.size = 6 := by decide +kernel

theorem mwords_size : (wordArrs Data.MWords).size = 3 := by
  rw [wordArrs, CFSG.ONSchreier.pwords_eq, Array.size_map, mw_size]

theorem bA_get {h : Nat} (hh : h < 4) : (wordArrs Data.MWords ++ #[cArr])[h]! = wordArr (bW h) := by
  rw [getElem!_pos _ h (by simp [mwords_size]; omega)]
  by_cases h3 : h < 3
  · rw [Array.getElem_append_left (by rw [mwords_size]; exact h3),
      ← getElem!_pos _ h (by rw [mwords_size]; exact h3),
      wordArrs_get (by rw [mw_size]; exact h3), bW]
    simp only [h3, ↓reduceIte]
  · have e : h = 3 := by omega
    subst e
    rw [Array.getElem_append_right (by rw [mwords_size])]
    simp [mwords_size, bW, cArr]

theorem good_bA {h : Nat} (hh : h < 4) : Good (wordArrs Data.MWords ++ #[cArr])[h]! (bF h) := by
  rw [bA_get hh]
  exact good_word (bW_let hh).1

theorem bI_get {h : Nat} (hh : h < 4) :
    (pinvs nPts (wordArrs Data.MWords ++ #[cArr]))[h]! =
      pinvCand nPts (wordArrs Data.MWords ++ #[cArr])[h]! := by
  unfold pinvs
  rw [getElem!_pos _ h (by simp [mwords_size]; omega), Array.getElem_map,
    ← getElem!_pos _ h (by simp [mwords_size]; omega)]

theorem good_bI {h : Nat} (hh : h < 4) :
    Good (pinvs nPts (wordArrs Data.MWords ++ #[cArr]))[h]! (bFI h) ∧
      pisInv nPts (wordArrs Data.MWords ++ #[cArr])[h]!
        (pinvs nPts (wordArrs Data.MWords ++ #[cArr]))[h]! = true := by
  rw [bI_get hh]
  exact good_inv (good_bA hh) fun x hx => ⟨(bW_pair h hh x hx).2.1, (bW_pair h hh x hx).2.2.1⟩

theorem good_tA {j : Nat} (hj : j < 6) : Good (wordArrs Data.TWords)[j]! (tF j) := by
  rw [wordArrs_get (by rw [tw_size]; exact hj)]
  have hw : plettersOK 7 Data.TWords[j]! = true := by interval_cases j <;> decide
  exact good_word hw

theorem repWords_lt' {i : Nat} (hi : i < 7) : ∀ j ∈ repWords[i]!, j < 6 := by
  interval_cases i <;> decide

@[expose] noncomputable def rF (i x : Nat) : Nat := (repWords[i]!).foldr (fun j y => tF j y) x

theorem good_r {i : Nat} (hi : i < 7) :
    Good (prodArr nPts (wordArrs Data.TWords) repWords[i]!) (rF i) :=
  good_prodArr (k := 6) (fun _ hj => good_tA hj) _ (repWords_lt' hi)

@[expose] noncomputable def vF (k x : Nat) : Nat := (vWords[k]!).foldr (GZ bF bFI) x
@[expose] noncomputable def vFI (k x : Nat) : Nat := (invW vWords[k]!).foldr (GZ bF bFI) x

theorem vW_let {k : Nat} (hk : k < 3) : plettersOK 4 vWords[k]! = true ∧ LetM 4 vWords[k]! := by
  interval_cases k <;> exact ⟨by decide, fun l hl => by revert l; decide⟩

theorem good_v {k : Nat} (hk : k < 3) :
    Good (pword nPts (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) vWords[k]!) (vF k) :=
  good_pword (k := 4) (fun _ hh => good_bA hh) (fun _ hh => (good_bI hh).1) _ (vW_let hk).1

theorem good_vI {k : Nat} (hk : k < 3) :
    Good (pinvCand nPts (pword nPts (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) vWords[k]!)) (vFI k) ∧
      pisInv nPts (pword nPts (wordArrs Data.MWords ++ #[cArr])
        (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) vWords[k]!)
        (pinvCand nPts (pword nPts (wordArrs Data.MWords ++ #[cArr])
          (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) vWords[k]!)) = true :=
  good_inv (good_v hk) fun x hx =>
    ⟨(invPair_word bW_pair (vW_let hk).2 x hx).2.1, (invPair_word bW_pair (vW_let hk).2 x hx).2.2.1⟩

@[expose] noncomputable def zF (x : Nat) : Nat := Data.zWord.foldr (GZ TT UU) x

theorem good_z : Good zArr zF := good_word (by decide)

@[expose] noncomputable def oF (i k x : Nat) : Nat := rF i (vF k (zF (vFI k x)))

theorem good_odd {i k : Nat} (hi : i < 7) (hk : k < 3) :
    Good (oddArr (wordArrs Data.TWords) (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) zArr i k) (oF i k) := by
  have h := good_pcomp (good_r hi) (good_pcomp (good_v hk) (good_pcomp good_z (good_vI hk).1))
  exact h

end Good

theorem base_r : (List.range 7).all (fun i => [0, 227759, 100817].all fun b =>
    Nat.beq (rF i (rF i b)) b) = true := by
  decide +kernel

theorem move_r : (List.range 7).all (fun i => !Nat.beq (rF i 227759) 227759) = true := by
  decide +kernel

theorem base_z : [0, 227759, 100817].all (fun b => Nat.beq (rF 3 b) (zF b)) = true := by
  decide +kernel

theorem base_odd : oddTests.all (fun (t : Nat × Nat × Nat) => [0, 227759, 100817].all fun b =>
      Nat.beq (Nat.repeat (oF t.1 t.2.1) t.2.2 b) b) = true := by
  decide +kernel

theorem base_rtab : (List.range 6).all (fun j => (List.range 32).all fun i =>
    bAnd(Nat.blt (Data.T32Chain.generators[j]!)[i]! 32,
      Nat.beq (tF j Data.TPoints[i]!) Data.TPoints[(Data.T32Chain.generators[j]!)[i]!]!)) =
    true := by
  decide +kernel

theorem tp_size : Data.TPoints.size = 32 := by decide +kernel

theorem tp_lt : ∀ i < Data.TPoints.size, Data.TPoints[i]! < 245520 := by decide +kernel

section Fusion


theorem tpoints_pos : (posArr nPts Data.TPoints).size = nPts ∧
    ∀ i < Data.TPoints.size, (posArr nPts Data.TPoints)[Data.TPoints[i]!]! = i :=
  posArr_spec (by decide +kernel) (by decide +kernel)

theorem rtab_ok {j : Nat} (hj : j < 6) :
    peq 32 (rTab (wordArrs Data.TWords)[j]!) Data.T32Chain.generators[j]! = true := by
  have hb := List.all_eq_true.1 (List.all_eq_true.1 base_rtab j (List.mem_range.2 hj))
  unfold peq rTab restrictTab rPos
  rw [allBelowN_iff]
  intro i hi
  have hi32 : i < Data.TPoints.size := by rw [tp_size]; exact hi
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 (hb i (List.mem_range.2 hi))
  have hp : Data.TPoints[i]! < 245520 := tp_lt i hi32
  have hs : (Data.T32Chain.generators[j]!)[i]! < Data.TPoints.size := by
    rw [tp_size]; rw [Nat.blt_eq] at h1; exact h1
  rw [getElem!_pos _ i (by simpa using hi32), Array.getElem_map, ← getElem!_pos _ i hi32,
    ((good_tA hj).2.2 _ hp).1, Nat.eq_of_beq_eq_true h2, tpoints_pos.2 _ hs]
  exact beq_self_eq_true _

theorem base3 {F G : Nat → Nat}
    (h : [0, 227759, 100817].all (fun b => Nat.beq (F b) (G b)) = true) :
    F 0 = G 0 ∧ F 227759 = G 227759 ∧ F 100817 = G 100817 := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem fusion2119 : fusionCheck (wordArrs Data.TWords) (wordArrs Data.MWords ++ #[cArr])
    (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) zArr = true := by
  unfold fusionCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  and_intros
  · rw [wordArrs, CFSG.ONSchreier.pwords_eq, Array.size_map, tw_size]
  · simp [mwords_size]
  · simp [pinvs, mwords_size]
  · rw [allBelowN_iff]
    exact fun j hj => rtab_ok hj
  · rw [allBelowN_iff]
    exact fun j hj => (good_bI hj).2
  · obtain ⟨a, b, c⟩ := base3 base_z
    exact peq_good (good_r (by norm_num)) good_z a b c
  · rw [allBelowN_iff]
    intro i hi
    have hb := List.all_eq_true.1 base_r i (List.mem_range.2 hi)
    have hm := List.all_eq_true.1 move_r i (List.mem_range.2 hi)
    obtain ⟨a, b, c⟩ := base3 (F := fun x => rF i (rF i x)) (G := fun x => x) hb
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨peq_good (good_pcomp (good_r hi) (good_r hi)) good_pid a b c,
      peq_good_false (good_r hi) good_pid (x := 227759) (by norm_num) ?_⟩
    intro he
    have he' : rF i 227759 = 227759 := he
    rw [he', Nat.beq_refl] at hm
    exact absurd hm (by decide)
  · rw [Array.all_eq_true']
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hw
    have hk3 : k < 3 := by simpa [vWords] using hk
    have := (vW_let hk3).1
    rwa [getElem!_pos vWords k hk] at this
  · rw [Array.all_eq_true']
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hw
    have hk3 : k < 3 := by simpa [vWords] using hk
    have := (good_vI hk3).2
    rwa [getElem!_pos vWords k hk] at this
  · rw [List.all_eq_true]
    rintro ⟨i, k, m⟩ hmem
    have hb := List.all_eq_true.1 base_odd (i, k, m) hmem
    have hi : i < 7 := by simp [oddTests] at hmem; omega
    have hk : k < 3 := by simp [oddTests] at hmem; omega
    obtain ⟨a, b, c⟩ := base3 (F := fun x => Nat.repeat (oF i k) m x) (G := fun x => x) hb
    exact peq_good (good_repeat (good_odd hi hk) m) good_pid a b c

end Fusion

end CertificateChecks.KernelSpor.ON2119

end
