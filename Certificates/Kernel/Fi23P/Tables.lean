module

public import Certificates.Kernel.Fi23P.ImgChk
public import Certificates.Kernel.Fi23C.Group
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KD.Fi23P CFSG.KS.TW CFSG.Sporadic.Th.Native
  CFSG.KS.Raw.Orb
  CFSG.Sporadic.Fi23.Native CFSG.Monster.Existence.Fi23Sp8.Native
  CFSG.Sporadic.Bridge.Fi23GPL.Native CertificateChecks.KernelFi23M CertificateChecks.KernelFi23C

noncomputable abbrev G4 : Array Table :=
  #[orbLit.alpha, orbLit.alpha, orbLit.beta, invT 31671 orbLit.beta]

noncomputable abbrev IT : Array Table := (imgWords ()).map (wordT 31671 (seedLetter G4))

noncomputable abbrev IV : Array Table := IT.map (invT 31671)

theorem seedLetter_G4 : seedLetter G4 = genTables orbLit := by
  funext z
  unfold seedLetter genTables
  by_cases h1 : z = 1
  · simp [h1]
  · by_cases h2 : z = -1
    · simp [h2]
    · by_cases h3 : z = 2
      · simp [h3]
      · simp [h1, h2, h3]

theorem imgWords_size : (imgWords ()).size = 10 := by
  rw [CertificateChecks.KernelKDenseP.TwoPoint.fi_img_words, Array.size_ofFn]

theorem imgWords_get {k : Nat} (hk : k < 10) : (imgWords ())[k]! = WD k := by
  rw [getElem!_pos (imgWords ()) k (by rw [imgWords_size]; exact hk)]
  simp only [CertificateChecks.KernelKDenseP.TwoPoint.fi_img_words, Array.getElem_ofFn]

@[expose] def SL (z : Int) : Prop := z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2

theorem SL_of {z : Int} (h : (z == 1 || z == -1 || z == 2 || z == -2) = true) : SL z := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  unfold SL
  tauto

theorem conj_parts {k : Nat} (hk : k < 10) : WD k = PD k ++ dPow () ++ invWord (PD k) ∧
    ∀ z ∈ PD k, SL z := by
  have h := List.all_eq_true.1 conj_ok k (List.mem_range.2 hk)
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun z hz => SL_of (h.2 z hz)⟩

theorem dPow_SL : ∀ z ∈ dPow (), SL z := by
  intro z hz
  unfold dPow at hz
  rw [List.mem_flatten] at hz
  obtain ⟨l, hl, hz⟩ := hz
  rw [List.eq_of_mem_replicate hl] at hz
  unfold dLetters at hz
  rw [List.mem_map] at hz
  obtain ⟨x, -, rfl⟩ := hz
  unfold SL
  split_ifs <;> simp

theorem invWord_SL {u : List Int} (h : ∀ z ∈ u, SL z) : ∀ z ∈ invWord u, SL z := by
  intro z hz
  unfold invWord at hz
  rw [List.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rcases h x (List.mem_reverse.1 hx) with rfl | rfl | rfl | rfl <;> unfold SL <;> simp

theorem WD_SL {k : Nat} (hk : k < 10) : ∀ z ∈ WD k, SL z := by
  obtain ⟨e, hp⟩ := conj_parts hk
  rw [e]
  intro z hz
  simp only [List.mem_append] at hz
  rcases hz with (hz | hz) | hz
  · exact hp z hz
  · exact dPow_SL z hz
  · exact invWord_SL hp z hz

theorem seed_TR {z : Int} (hz : SL z) : TR 31671 (seedLetter G4 z) (tb G (regZ z)) := by
  rw [seedLetter_G4]
  exact genTables_TR (by rcases hz with rfl | rfl | rfl | rfl <;> decide)
    (by rcases hz with rfl | rfl | rfl | rfl <;> decide)

noncomputable abbrev wSd (w : List Int) (x : Nat) : Nat := w.foldr (fun z y => tb G (regZ z) y) x

theorem wordT_TR' {w : List Int} (hw : ∀ z ∈ w, SL z) :
    TR 31671 (wordT 31671 (seedLetter G4) w) (wSd w) :=
  wordT_TR (by norm_num) w fun z hz => seed_TR (hw z hz)

section


noncomputable def sz (z : Int) : PG :=
  if z = 1 then wα else if z = -1 then wα⁻¹ else if z = 2 then wβ else wβ⁻¹

theorem acts_sz {z : Int} (hz : SL z) : ActsAs (phiX (sz z)) (tb G (regZ z)) := by
  rcases hz with rfl | rfl | rfl | rfl
  · simpa [sz, regZ] using phiX_wα
  · simpa [sz, regZ, map_inv] using acts_alpha_inv
  · simpa [sz, regZ] using phiX_wβ
  · simpa [sz, regZ, map_inv] using acts_beta_inv

theorem acts_word : ∀ w : List Int, (∀ z ∈ w, SL z) →
    ActsAs (phiX (w.map sz).prod) (wSd w)
  | [], _ => fun _ _ => rfl
  | z :: w, hw => by
    rw [List.map_cons, List.prod_cons, map_mul]
    exact (acts_sz (hw z List.mem_cons_self)).mul
      (acts_word w fun y hy => hw y (List.mem_cons_of_mem z hy))

theorem xS_mem {k : Nat} (hk : k < 10) : xS k ∈ Xc := Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem xS_inv_acts {k : Nat} (hk : k < 10) : ActsAs (xS k)⁻¹ (tb G k) :=
  (xS_acts hk).inv (rng k (by omega)) fun _ hx => x_inv hk hx

theorem base_pt {k j : Nat} (hk : k < 10) (hj : j < 6) : wSd (WD k) j = tb G k j := by
  have h := allN_iff.1 (allN_iff.1 base_ok k hk) j hj
  unfold wSd
  rw [foldr_regZ]
  exact Nat.eq_of_beq_eq_true h


theorem img_eq {k : Nat} (hk : k < 10) : phiX ((WD k).map sz).prod = xS k := by
  have hP := acts_word (WD k) (WD_SL hk)
  have hp : (xS k)⁻¹ * phiX ((WD k).map sz).prod = 1 := by
    refine fix_base (Subgroup.mul_mem _ (Subgroup.inv_mem _ (xS_mem hk)) (phiX_mem _)) ?_
    intro j hj
    have e := ((xS_inv_acts hk).mul hP) j (by omega)
    dsimp only at e
    rw [e, base_pt hk hj, x_inv hk (by omega)]
  rw [inv_mul_eq_one] at hp
  exact hp.symm

theorem img_acts {k : Nat} (hk : k < 10) {x : Nat} (hx : x < 31671) : wSd (WD k) x = tb G k x := by
  have h := acts_word (WD k) (WD_SL hk) x hx
  rw [img_eq hk, xS_acts hk x hx] at h
  exact h.symm

end

theorem XK_eq {k x : Nat} (hk : k < 10) (hx : x < 31671) : XK k x = tb G k x := by
  unfold XK
  rw [if_pos ⟨hk, hx⟩]

theorem ap_ge {T : Table} (hT : T.size = 31671) {x : Nat} (hx : ¬ x < 31671) : ap T x = 0 := by
  unfold ap
  rw [getElem!_neg T x (by omega)]
  rfl

theorem IT_size : IT.size = 10 := by simp [imgWords_size]

theorem IT_get {k : Nat} (hk : k < 10) :
    IT[k]! = wordT 31671 (seedLetter G4) (WD k) := by
  rw [getElem!_pos IT k (by rw [IT_size]; exact hk), Array.getElem_map, ← imgWords_get hk,
    getElem!_pos (imgWords ()) k (by rw [imgWords_size]; exact hk)]

section


theorem IT_TR {k : Nat} (hk : k < 10) : TR 31671 IT[k]! (tb G k) := by
  rw [IT_get hk]
  exact tr_congr (wordT_TR' (WD_SL hk)) fun i hi => img_acts hk hi

theorem IV_TR {k : Nat} (hk : k < 10) : TR 31671 IV[k]! (tb G k) := by
  rw [getElem!_pos IV k (by simp [imgWords_size]; exact hk), Array.getElem_map,
    ← getElem!_pos IT k (by rw [IT_size]; exact hk)]
  exact invT_TR (by norm_num) (IT_TR hk) fun i hi =>
    ⟨rng k (by omega) i hi, x_inv hk hi, x_inv hk hi⟩

theorem ap_of_TR {T : Table} {k : Nat} (hk : k < 10) (h : TR 31671 T (tb G k)) (x : Nat) :
    ap T x = XK k x := by
  by_cases hx : x < 31671
  · rw [(h.2 x hx).1, XK_eq hk hx]
  · rw [ap_ge h.1 hx]
    unfold XK
    rw [if_neg (fun h' => hx h'.2)]

theorem IT_ap (k x : Nat) : ap IT[k]! x = XK k x := by
  by_cases hk : k < 10
  · exact ap_of_TR hk (IT_TR hk) x
  · rw [getElem!_neg IT k (by rw [IT_size]; omega)]
    unfold XK
    rw [if_neg (fun h' => hk h'.1)]
    rfl

theorem IV_ap (k x : Nat) : ap IV[k]! x = XK k x := by
  by_cases hk : k < 10
  · exact ap_of_TR hk (IV_TR hk) x
  · rw [getElem!_neg IV k (by simp [imgWords_size]; omega)]
    unfold XK
    rw [if_neg (fun h' => hk h'.1)]
    rfl

end

theorem prefWord_eq {k : Nat} (hk : k < 10) : prefWord k = PD k := by
  unfold prefWord prefLen
  rw [imgWords_get hk]

theorem piPt_eq {k : Nat} (hk : k < 10) : piPt G4 k = piL.getD k 0 := by
  unfold piPt
  obtain ⟨-, hp⟩ := conj_parts hk
  rw [prefWord_eq hk, ((wordT_TR' hp).2 0 (by norm_num)).1]
  unfold wSd
  rw [foldr_regZ]
  exact Nat.eq_of_beq_eq_true (allN_iff.1 pi_ok k hk)

theorem piPt0 : piPt G4 0 = 4777 := piPt_eq (by norm_num)

theorem piPt8 : piPt G4 8 = 16688 := piPt_eq (by norm_num)

section


theorem sz_neg {z : Int} (hz : SL z) : sz (-z) = (sz z)⁻¹ := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [sz]

theorem invWord_cons (z : Int) (u : List Int) : invWord (z :: u) = invWord u ++ [-z] := by
  simp [invWord]

theorem prod_invWord : ∀ {u : List Int}, (∀ z ∈ u, SL z) →
    ((invWord u).map sz).prod = ((u.map sz).prod)⁻¹
  | [], _ => by simp [invWord]
  | z :: u, hu => by
    rw [invWord_cons, List.map_append, List.prod_append,
      prod_invWord fun y hy => hu y (List.mem_cons_of_mem z hy)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [sz_neg (hu z List.mem_cons_self), mul_inv_rev]

theorem prod_dPow :
    ((dPow ()).map sz).prod = (dWord.map fun x => if x = 0 then wα else wβ).prod ^ 7 := by
  have e : ((dLetters ()).map sz).prod = (dWord.map fun x => if x = 0 then wα else wβ).prod := by
    unfold dLetters
    rw [List.map_map]
    congr 1
  unfold dPow
  rw [List.map_flatten, List.prod_flatten, List.map_replicate, List.map_replicate,
    List.prod_replicate, e]

theorem phiX_dPow : phiX ((dPow ()).map sz).prod = phiX wD := by
  refine ActsAs.ext ?_ phiX_wD
  rw [prod_dPow, map_pow]
  exact acts_dWord7


theorem xS_cp {k : Nat} (hk : k < 10) : xS k = cp (piL.getD k 0) := by
  obtain ⟨e, hp⟩ := conj_parts hk
  have h0 : (phiX ((PD k).map sz).prod ⟨0, hn⟩).val = piL.getD k 0 := by
    rw [acts_word (PD k) hp 0 (by norm_num)]
    unfold wSd
    rw [foldr_regZ]
    exact Nat.eq_of_beq_eq_true (allN_iff.1 pi_ok k hk)
  rw [← img_eq hk, e, List.map_append, List.map_append, List.prod_append, List.prod_append,
    prod_invWord hp, map_mul, map_mul, phiX_dPow, ← cp_zero, ← h0, cp_eqv _ hn, map_inv]

end

end CertificateChecks.KernelFi23P

end
