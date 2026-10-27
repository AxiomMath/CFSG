module

public import Certificates.Kernel.Sporadic.ONEN.Defs
public import Certificates.Kernel.ONSeven.G17390Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONEN

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.TW CFSG.KS.PW CFSG.RankThree.Native
open CFSG.Sporadic.ON
open CFSG.Sporadic.ON.Native (nPts)
open CertificateChecks.KernelSpor.ONS (WW arr_get inv_get pisInv_word evalS_apply
  evalS_inv_apply letM_of_pletters)
open CertificateChecks.KernelSpor.ON (TT)
open CertificateChecks.KernelSpor.ON3 (invW)

theorem tW_ok : ∀ h < 6, plettersOK 7 (tW h) = true := by decide +kernel

theorem nW_ok : ∀ i < 4, plettersOK 7 (nW i) = true := by decide +kernel

theorem eW_ok : ∀ j < 2, ∀ k < 3, plettersOK 6 (eW j k) = true := by decide +kernel

theorem abW_ok : plettersOK 4 onAWord = true ∧ plettersOK 4 onBWord = true ∧
    plettersOK 7 [1] = true ∧ plettersOK 7 [2] = true := by decide +kernel

theorem tW_eq : ∀ h < 6, Data.TWords[h]! = tW h := by decide +kernel

theorem nW_eq : ∀ i < 4, onNormWords[i]! = nW i := by decide +kernel

theorem eW_eq : ∀ j < 2, ∀ k < 3, (onE8Words[j]!)[k]! = eW j k := by decide +kernel

theorem tag_eq : ∀ i < 4, onNormTags[i]! = onNormTags.toList.getD i 0 ∧
    onNormTags.toList.getD i 0 < 2 := by decide +kernel

theorem WW_one (x : Nat) : WW [1] x = TT 0 x := rfl

theorem WW_two (x : Nat) : WW [2] x = TT 1 x := rfl

theorem letters_of {m : Nat} {w : List Int} (h : plettersOK m w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m := by
  intro l hl
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact h l hl

theorem map_get13790 {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {i : Nat} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem onTArrs_get {h : Nat} (hh : h < 6) : onTArrs[h]! = wordArr (tW h) := by
  rw [onTArrs, wordArrs, pwords_get (by exact hh), tW_eq h hh]
  rfl

theorem onTArrs_size : onTArrs.size = 6 := by
  rw [onTArrs, wordArrs, CFSG.KS.PW.pwords_eq, Array.size_map]
  rfl

theorem onTInvArrs_get {h : Nat} (hh : h < 6) : onTInvArrs[h]! = pinvCand nPts (wordArr (tW h)) := by
  rw [onTInvArrs, pinvs, map_get13790 _ _ (by rw [onTArrs_size]; exact hh), onTArrs_get hh]

theorem onNormArrs_get {i : Nat} (hi : i < 4) : onNormArrs[i]! = wordArr (nW i) := by
  rw [onNormArrs, map_get13790 _ _ (by exact hi), nW_eq i hi]

theorem onNormArrs_size : onNormArrs.size = 4 := by
  rw [onNormArrs, Array.size_map]
  rfl

theorem onNormInvArrs_get {i : Nat} (hi : i < 4) :
    onNormInvArrs[i]! = pinvCand nPts (wordArr (nW i)) := by
  rw [onNormInvArrs, pinvs, map_get13790 _ _ (by rw [onNormArrs_size]; exact hi),
    onNormArrs_get hi]

theorem pisInv_wordArr {w : List Int} (hw : plettersOK 7 w = true) :
    pisInv nPts (wordArr w) (pinvCand nPts (wordArr w)) = true :=
  pisInv_word (letM_of_pletters hw)

section Rec


@[expose] def Rp (A : Array Nat) (g : Equiv.Perm (Fin N)) (F : Nat → Nat) : Prop :=
  PRep N A g ∧ g ∈ Pv ∧ ∀ x < N, A[x]! = F x

@[expose] def RpE (A : Array Nat) (F : Nat → Nat) : Prop := ∃ g, Rp A g F

theorem rp_word {w : List Int} (hw : plettersOK 7 w = true) : Rp (wordArr w) (evalS w) (WW w) := by
  have e : wordArr w = onSevenArr w := rfl
  refine ⟨fun x => ?_, evalS_mem w, fun x hx => ?_⟩
  · rw [e, arr_get (letM_of_pletters hw) x.2, evalS_apply hw]
  · rw [e, arr_get (letM_of_pletters hw) hx]

theorem rp_inv {w : List Int} (hw : plettersOK 7 w = true) :
    Rp (pinvCand nPts (wordArr w)) (evalS w)⁻¹ (WW (invW w)) := by
  have e : wordArr w = onSevenArr w := rfl
  refine ⟨fun x => ?_, inv_mem (evalS_mem w), fun x hx => ?_⟩
  · rw [e, inv_get (letM_of_pletters hw) x.2, evalS_inv_apply hw]
  · rw [e, inv_get (letM_of_pletters hw) hx]

theorem rp_pid : Rp (pid nPts) 1 (fun x => x) :=
  ⟨prep_pid, one_mem _, fun _ hx => pid_get' hx⟩

theorem rp_pcomp {A B : Array Nat} {g h : Equiv.Perm (Fin N)} {F G : Nat → Nat} (hA : Rp A g F)
    (hB : Rp B h G) : Rp (pcomp nPts A B) (g * h) (fun x => F (G x)) := by
  refine ⟨prep_pcomp hA.1 hB.1, mul_mem hA.2.1 hB.2.1, fun x hx => ?_⟩
  have hlt : B[x]! < N := hB.1.lt hx
  rw [pcomp_get' hx, hA.2.2 _ hlt, hB.2.2 x hx]

theorem rpE_pcomp {A B : Array Nat} {F G : Nat → Nat} (hA : RpE A F) (hB : RpE B G) :
    RpE (pcomp nPts A B) (fun x => F (G x)) := by
  obtain ⟨g, hg⟩ := hA
  obtain ⟨h, hh⟩ := hB
  exact ⟨g * h, rp_pcomp hg hh⟩

theorem rp_pword {m : Nat} {S Si : Array (Array Nat)} {gs : Nat → Equiv.Perm (Fin N)}
    {G GI : Nat → Nat → Nat} (hS : ∀ h < m, Rp S[h]! (gs h) (G h))
    (hSi : ∀ h < m, Rp Si[h]! (gs h)⁻¹ (GI h)) {w : List Int} (hw : plettersOK m w = true) :
    RpE (pword nPts S Si w) (fun x => w.foldr (GZ G GI) x) := by
  have hL : LettersOK N m S Si G GI := fun j hj x hx =>
    ⟨(hS j hj).2.2 x hx, (hSi j hj).2.2 x hx, (hS j hj).2.2 x hx ▸ (hS j hj).1.lt hx,
      (hSi j hj).2.2 x hx ▸ (hSi j hj).1.lt hx⟩
  refine ⟨_, prep_pword (fun h hh => (hS h hh).1) (fun h hh => (hSi h hh).1) w hw,
    (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _),
    fun x hx => (pword_get hL w (letters_of hw) x hx).1⟩
  rintro _ ⟨h, rfl⟩
  exact (hS h h.2).2.1

theorem rpT {h : Nat} (hh : h < 6) : Rp onTArrs[h]! (evalS (tW h)) (tP h) := by
  rw [onTArrs_get hh]
  exact rp_word (tW_ok h hh)

theorem rpTI {h : Nat} (hh : h < 6) : Rp onTInvArrs[h]! (evalS (tW h))⁻¹ (tPI h) := by
  rw [onTInvArrs_get hh]
  exact rp_inv (tW_ok h hh)

theorem rpN {i : Nat} (hi : i < 4) : Rp onNormArrs[i]! (evalS (nW i)) (nP i) := by
  rw [onNormArrs_get hi]
  exact rp_word (nW_ok i hi)

theorem rpNI {i : Nat} (hi : i < 4) : Rp onNormInvArrs[i]! (evalS (nW i))⁻¹ (nPI i) := by
  rw [onNormInvArrs_get hi]
  exact rp_inv (nW_ok i hi)

theorem rpE {j k : Nat} (hj : j < 2) (hk : k < 3) : RpE (onE8Arr j k) (eP j k) := by
  unfold onE8Arr
  rw [eW_eq j hj k hk]
  exact rp_pword (gs := fun h => evalS (tW h)) (fun _ hh => rpT hh) (fun _ hh => rpTI hh)
    (eW_ok j hj k hk)

theorem rpW {w : List Int} (hw : plettersOK 4 w = true) :
    RpE (pword nPts onNormArrs onNormInvArrs w) (fun x => w.foldr (GZ nP nPI) x) :=
  rp_pword (gs := fun i => evalS (nW i)) (fun _ hi => rpN hi) (fun _ hi => rpNI hi) hw

theorem peq_true_of {A B : Array Nat} {F G : Nat → Nat} (hA : RpE A F) (hB : RpE B G)
    (h0 : F 0 = G 0) (h1 : F 227759 = G 227759) (h2 : F 100817 = G 100817) :
    peq nPts A B = true := by
  obtain ⟨g, hg, hgP, hgF⟩ := hA
  obtain ⟨h, hh, hhP, hhF⟩ := hB
  refine (peq_iff hg hh).2 (eq_of_three hgP hhP ?_ ?_ ?_) <;> apply Fin.ext
  · exact (hg.apply (by norm_num)).symm.trans ((hgF 0 (by norm_num)).trans
      (h0.trans ((hhF 0 (by norm_num)).symm.trans (hh.apply (by norm_num)))))
  · exact (hg.apply (by norm_num)).symm.trans ((hgF 227759 (by norm_num)).trans
      (h1.trans ((hhF 227759 (by norm_num)).symm.trans (hh.apply (by norm_num)))))
  · exact (hg.apply (by norm_num)).symm.trans ((hgF 100817 (by norm_num)).trans
      (h2.trans ((hhF 100817 (by norm_num)).symm.trans (hh.apply (by norm_num)))))

end Rec

theorem peq_false_of {A B : Array Nat} {F G : Nat → Nat} (hA : ∀ x < N, A[x]! = F x)
    (hB : ∀ x < N, B[x]! = G x) (h : diff3 F G = true) : peq nPts A B = false := by
  rw [Bool.eq_false_iff]
  intro hp
  have e : ∀ x < N, Nat.beq (F x) (G x) = true := fun x hx => by
    have hx' := allBelowN_iff.1 hp x hx
    rw [beq_iff_eq, hA x hx, hB x hx] at hx'
    rw [hx']
    exact Nat.beq_refl _
  unfold diff3 at h
  rw [e 0 (by norm_num), e 227759 (by norm_num), e 100817 (by norm_num)] at h
  simp at h

section Conj


theorem e_spec {j x : Nat} (h : ch13790E j x = true) :
    eP j 0 (eP j 0 x) = x ∧ eP j 1 (eP j 1 x) = x ∧ eP j 2 (eP j 2 x) = x ∧
      eP j 0 (eP j 1 x) = eP j 1 (eP j 0 x) ∧ eP j 0 (eP j 2 x) = eP j 2 (eP j 0 x) ∧
      eP j 1 (eP j 2 x) = eP j 2 (eP j 1 x) := by
  simp only [ch13790E, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem pt_of {A : Array Nat} {F : Nat → Nat} (h : RpE A F) : ∀ x < N, A[x]! = F x := by
  obtain ⟨_, -, -, hF⟩ := h
  exact hF

theorem pe8_ok {j : Nat} (hj : j < 2)
    (hE : (ch13790E j 0 && ch13790E j 227759 && ch13790E j 100817) = true)
    (hD : ch13790D j = true) : pe8OK (onE8Arr j 0) (onE8Arr j 1) (onE8Arr j 2) = true := by
  simp only [Bool.and_eq_true] at hE
  obtain ⟨⟨a0, a1⟩, a2⟩ := hE
  obtain ⟨x0, y0, z0, xy0, xz0, yz0⟩ := e_spec a0
  obtain ⟨x1, y1, z1, xy1, xz1, yz1⟩ := e_spec a1
  obtain ⟨x2, y2, z2, xy2, xz2, yz2⟩ := e_spec a2
  simp only [ch13790D, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨⟨⟨⟨d1, d2⟩, d3⟩, d4⟩, d5⟩, d6⟩, d7⟩ := hD
  have rx := rpE hj (k := 0) (by norm_num)
  have ry := rpE hj (k := 1) (by norm_num)
  have rz := rpE hj (k := 2) (by norm_num)
  have ri : RpE (pid nPts) (fun x => x) := ⟨1, rp_pid⟩
  have pi : ∀ x < N, (pid nPts)[x]! = id x := fun _ hx => pid_get' hx
  simp only [pe8OK, pinvol, pcommute, pelems4, Bool.and_eq_true, Bool.not_eq_true',
    List.all_cons, List.all_nil, Bool.and_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact peq_true_of (rpE_pcomp rx rx) ri x0 x1 x2
  · exact peq_true_of (rpE_pcomp ry ry) ri y0 y1 y2
  · exact peq_true_of (rpE_pcomp rz rz) ri z0 z1 z2
  · exact peq_true_of (rpE_pcomp rx ry) (rpE_pcomp ry rx) xy0 xy1 xy2
  · exact peq_true_of (rpE_pcomp rx rz) (rpE_pcomp rz rx) xz0 xz1 xz2
  · exact peq_true_of (rpE_pcomp ry rz) (rpE_pcomp rz ry) yz0 yz1 yz2
  · exact peq_false_of (pt_of rx) pi d1
  · exact peq_false_of (pt_of ry) pi d2
  · exact peq_false_of (pt_of ry) (pt_of rx) d3
  · exact peq_false_of (pt_of rz) pi d4
  · exact peq_false_of (pt_of rz) (pt_of rx) d5
  · exact peq_false_of (pt_of rz) (pt_of ry) d6
  · exact peq_false_of (pt_of rz) (pt_of (rpE_pcomp rx ry)) d7

theorem rp8 {X Y Z : Array Nat} {fx fy fz : Nat → Nat} (rx : RpE X fx) (ry : RpE Y fy)
    (rz : RpE Z fz) {m : Nat} (hm : m < 8) :
    ∃ f ∈ pelems8 X Y Z, RpE f (fun x => (el8F fx fy fz x).getD m 0) := by
  have ri : RpE (pid nPts) (fun x => x) := ⟨1, rp_pid⟩
  interval_cases m
  · exact ⟨_, by simp [pelems8, pelems4], ri⟩
  · exact ⟨_, by simp [pelems8, pelems4], rx⟩
  · exact ⟨_, by simp [pelems8, pelems4], ry⟩
  · exact ⟨_, by simp [pelems8, pelems4], rpE_pcomp rx ry⟩
  · exact ⟨_, by simp [pelems8, pelems4], rpE_pcomp (F := fun x => x) (G := fz) ri rz⟩
  · exact ⟨_, by simp [pelems8, pelems4], rpE_pcomp rx rz⟩
  · exact ⟨_, by simp [pelems8, pelems4], rpE_pcomp ry rz⟩
  · exact ⟨_, by simp [pelems8, pelems4],
      rpE_pcomp (F := fun x => fx (fy x)) (G := fz) (rpE_pcomp rx ry) rz⟩

theorem any8 {X Y Z C : Array Nat} {fx fy fz FC : Nat → Nat} (rx : RpE X fx) (ry : RpE Y fy)
    (rz : RpE Z fz) (rc : RpE C FC)
    (h : ((List.range 8).any fun m =>
      Nat.beq (FC 0) ((el8F fx fy fz 0).getD m 0) &&
      Nat.beq (FC 227759) ((el8F fx fy fz 227759).getD m 0) &&
      Nat.beq (FC 100817) ((el8F fx fy fz 100817).getD m 0)) = true) :
    (pelems8 X Y Z).any (fun f => peq nPts C f) = true := by
  obtain ⟨m, hm, hP⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at hP
  obtain ⟨⟨p0, p1⟩, p2⟩ := hP
  obtain ⟨f, hf, rf⟩ := rp8 rx ry rz (List.mem_range.1 hm)
  exact List.any_eq_true.2 ⟨f, hf, peq_true_of rc rf (Nat.eq_of_beq_eq_true p0)
    (Nat.eq_of_beq_eq_true p1) (Nat.eq_of_beq_eq_true p2)⟩

theorem pnorm_ok {i : Nat} (hi : i < 4)
    (hN : (ch13790N i 0 && ch13790N i 1 && ch13790N i 2) = true) :
    pnormOK onNormArrs[i]! onNormInvArrs[i]! (onE8Arr onNormTags[i]! 0)
      (onE8Arr onNormTags[i]! 1) (onE8Arr onNormTags[i]! 2) = true := by
  obtain ⟨htag, hj⟩ := tag_eq i hi
  rw [htag]
  simp only [Bool.and_eq_true] at hN
  obtain ⟨⟨n0, n1⟩, n2⟩ := hN
  have rn : RpE onNormArrs[i]! (nP i) := ⟨_, rpN hi⟩
  have rni : RpE onNormInvArrs[i]! (nPI i) := ⟨_, rpNI hi⟩
  have rx := rpE hj (k := 0) (by norm_num)
  have ry := rpE hj (k := 1) (by norm_num)
  have rz := rpE hj (k := 2) (by norm_num)
  simp only [pnormOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨any8 rx ry rz (rpE_pcomp (rpE_pcomp rn rx) rni) n0,
    any8 rx ry rz (rpE_pcomp (rpE_pcomp rn ry) rni) n1,
    any8 rx ry rz (rpE_pcomp (rpE_pcomp rn rz) rni) n2⟩

theorem sound13790
    (hA : ∀ x, x = 0 ∨ x = 227759 ∨ x = 100817 → ch13790A x = true)
    (hE : ∀ j < 2, (ch13790E j 0 && ch13790E j 227759 && ch13790E j 100817) = true)
    (hD : (ch13790D 0 && ch13790D 1) = true)
    (hN : ∀ i < 4, (ch13790N i 0 && ch13790N i 1 && ch13790N i 2) = true) :
    onEightNormalizersCheck = true := by
  have ha : ∀ x, x = 0 ∨ x = 227759 ∨ x = 100817 →
      onAWord.foldr (GZ nP nPI) x = WW [1] x ∧ onBWord.foldr (GZ nP nPI) x = WW [2] x := by
    intro x hx
    have h := hA x hx
    simp only [ch13790A, Bool.and_eq_true] at h
    exact ⟨(Nat.eq_of_beq_eq_true h.1).trans (WW_one x).symm,
      (Nat.eq_of_beq_eq_true h.2).trans (WW_two x).symm⟩
  have h0 := ha 0 (Or.inl rfl)
  have h1 := ha 227759 (Or.inr (Or.inl rfl))
  have h2 := ha 100817 (Or.inr (Or.inr rfl))
  simp only [Bool.and_eq_true] at hD
  simp only [onEightNormalizersCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨onTArrs_size, ?_⟩, onNormArrs_size⟩, ?_⟩,
    pe8_ok (by norm_num) (hE 0 (by norm_num)) hD.1⟩,
    pe8_ok (by norm_num) (hE 1 (by norm_num)) hD.2⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allBelowN_iff.2 fun h hh => ?_
    rw [onTInvArrs_get hh, onTArrs_get hh]
    exact pisInv_wordArr (tW_ok h hh)
  · refine allBelowN_iff.2 fun i hi => ?_
    rw [onNormInvArrs_get hi, onNormArrs_get hi]
    exact pisInv_wordArr (nW_ok i hi)
  · exact allBelowN_iff.2 fun i hi => pnorm_ok hi (hN i hi)
  · exact peq_true_of (rpW abW_ok.1) ⟨_, rp_word abW_ok.2.2.1⟩ h0.1 h1.1 h2.1
  · exact peq_true_of (rpW abW_ok.2.1) ⟨_, rp_word abW_ok.2.2.2⟩ h0.2 h1.2 h2.2

end Conj

end CertificateChecks.KernelSpor.ONEN

end
