
module

public import Certificates.Kernel.He7223.GlueB
public import CFSG.Certificates.Kernel.Misc.F2MatGroup

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7223

open CFSG.KC.Enum CFSG.KS CFSG.KC.WordPts CFSG.KC.F2Mat CFSG.KC.M1F2 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.He CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
  CFSG.Sporadic.Schreier CertificateChecks.KernelLC.HeFix

theorem eMat_E
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ eNorm ebasis_E) {g : List ℤ} (hxg : x = elt g)
    (hg : lettersOK 2 g = true) {M : ℕ} (h : matE g M = true) :
    eMat ebasis_E ⟨x, hx⟩ = matOfF 6 M := by
  subst hxg
  have h' : matK 8330 14 LU LUI bsL eW 6 g M = true := by rw [eW_eq]; exact h
  exact eMat_of_matK (bsL_eq ▸ baseFaithful_heP) letRep_LU eW_letters3 eW_mem eW_len ebasis_E
    (lettersOK_mono (by rw [gens3_length]; norm_num) hg) (elt_mem_heP hg) h'

theorem eMat_Q
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ eNorm ebasis_Q) {g : List ℤ} (hxg : x = elt g)
    (hg : lettersOK 2 g = true) {M : ℕ} (h : matQ g M = true) :
    eMat ebasis_Q ⟨x, hx⟩ = matOfF 4 M := by
  subst hxg
  have h' : matK 8330 14 LU LUI bsL qW 4 g M = true := by rw [qW_eq]; exact h
  exact eMat_of_matK (bsL_eq ▸ baseFaithful_heP) letRep_LU qW_letters3 qW_mem qW_len ebasis_Q
    (lettersOK_mono (by rw [gens3_length]; norm_num) hg) (elt_mem_heP hg) h'

theorem closure_le_heAut
    {S : Set (Equiv.Perm (Fin 8330))} (hS : ∀ x ∈ S, ∃ w, lettersOK 2 w = true ∧ elt w = x) :
    Subgroup.closure S ≤ heAutGroup :=
  (Subgroup.closure_le _).mpr fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hS x hx
    exact heP_le_heAutGroup (elt_mem_heP hw)

theorem getD_letters {B : List (List ℤ)} (hB : ∀ wd ∈ B, lettersOK 2 wd = true) {i : ℕ}
    (hi : i < B.length) : lettersOK 2 (B.getD i []) = true :=
  hB _ (getD_mem hi)

theorem eW_letters2 : ∀ wd ∈ eW, lettersOK 2 wd = true := by rw [eW_eq]; exact EB_letters

theorem qW_letters2 : ∀ wd ∈ qW, lettersOK 2 wd = true := by rw [qW_eq]; exact QB_letters

theorem LG_mem : ∀ j < 3, lg j ∈ lsGenW := by
  rw [lsGenW_eq]
  intro j hj
  interval_cases j <;> simp

theorem lsGenW_cases {w : List ℤ} (hw : w ∈ lsGenW) : ∃ j < 3, w = lg j := by
  rw [lsGenW_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

theorem lGrp_le_heAut :
    lGrp ≤ heAutGroup :=
  closure_le_heAut fun _ ⟨w, hw, hx⟩ => by
    obtain ⟨j, hj, rfl⟩ := lsGenW_cases hw
    exact ⟨_, LG_letters j hj, hx⟩

theorem lg_mem_lGrp {j : ℕ} (hj : j < 3) : elt (lg j) ∈ lGrp :=
  Subgroup.subset_closure ⟨lg j, LG_mem j hj, rfl⟩

theorem lg_mem_eNorm {j : ℕ}
    (hj : j < 3) : elt (lg j) ∈ eNorm ebasis_E :=
  lsGen_mem_eNorm _ (LG_mem j hj)

theorem matE_lg : ∀ j < 3, matE (lg j) (gen LS j) = true := by
  intro j hj
  interval_cases j
  · exact ch7223mL0
  · exact ch7223mL1
  · exact ch7223mL2

@[expose] noncomputable def colE (X : ℕ) : Equiv.Perm (Fin 8330) :=
  eElt (fun i : Fin 6 => elt (eW.getD i [])) fun r => matOfF 6 X r 0

theorem colE_step {j : ℕ}
    (hj : j < 3) {X Y : ℕ} (hY : mulF 6 (gen LS j) X = Y) (hX : colE X ∈ lGrp) :
    colE Y ∈ lGrp := by
  have hconj := conj_eq_eElt_mulVec ebasis_E ⟨elt (lg j), lg_mem_eNorm hj⟩
    (fun r => matOfF 6 X r 0)
  rw [eMat_E (lg_mem_eNorm hj) rfl (LG_letters j hj) (matE_lg j hj)] at hconj
  have hv : (Matrix.mulVec (matOfF 6 (gen LS j)) fun r => matOfF 6 X r 0) =
      fun r => matOfF 6 Y r 0 := by
    rw [← hY, matOfF_mulF]
    funext r
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hv] at hconj
  unfold colE
  rw [← hconj]
  exact lGrp.mul_mem (lGrp.mul_mem (lg_mem_lGrp hj) hX) (lGrp.inv_mem (lg_mem_lGrp hj))

theorem colE_xor {X Y Z : ℕ}
    (hZ : X ^^^ Y = Z) (hX : colE X ∈ lGrp) (hY : colE Y ∈ lGrp) : colE Z ∈ lGrp := by
  have e : (fun r => matOfF 6 Z r 0) = (fun r => matOfF 6 X r 0) + fun r => matOfF 6 Y r 0 := by
    rw [← hZ]
    funext r
    rw [Pi.add_apply, matOfF_apply, matOfF_apply, matOfF_apply, Nat.testBit_xor, bz_xor]
  unfold colE
  rw [e, eElt_add ebasis_E.sq ebasis_E.comm]
  exact lGrp.mul_mem hX hY

theorem selW_EB : selW EB 63 = EB := by decide +kernel

theorem EB_len : EB.length = 6 := by decide +kernel

theorem colE_ones :
    colE 1090785345 ∈ lGrp := by
  have hl2 : ∀ wd ∈ [lg 0, lg 1, lg 0, lg 1], lettersOK 2 wd = true := by decide +kernel
  have hl : ∀ wd ∈ [lg 0, lg 1, lg 0, lg 1], lettersOK gens3.length wd = true := fun wd hw =>
    lettersOK_mono (by rw [gens3_length]; norm_num) (hl2 wd hw)
  have hs : ∀ wd ∈ selW EB 63, lettersOK gens3.length wd = true := by
    rw [selW_EB]
    exact letters3 EB_letters
  have hpt := eqPtsK_sound letRep_LU hl hs ch7223eL
  have hlP : ∀ x ∈ [lg 0, lg 1, lg 0, lg 1].map (evalSignedWord gens3), x ∈ heP := by
    intro x hx
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.mp hx
    exact elt_mem_heP (hl2 wd hwd)
  have hlm : ∀ wd ∈ [lg 0, lg 1, lg 0, lg 1], elt wd ∈ lGrp := by
    intro wd hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact lg_mem_lGrp (by norm_num)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact lg_mem_lGrp (by norm_num)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact lg_mem_lGrp (by norm_num)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact lg_mem_lGrp (by norm_num)
    exact absurd hw List.not_mem_nil
  have hsP : ((selW EB 63).map (evalSignedWord gens3)).prod ∈ heP := by
    rw [selW_EB]
    exact heP.list_prod_mem fun x hx => by
      obtain ⟨wd, hwd, rfl⟩ := List.mem_map.mp hx
      exact mem_heP_of EB_letters wd hwd
  have heq := eq_of_pts (bsL_eq ▸ baseFaithful_heP) (heP.list_prod_mem hlP) hsP hpt
  rw [prod_selW gens3 EB_len, ← eW_eq] at heq
  have hb : (fun r => matOfF 6 1090785345 r 0) = bitVec 6 63 := by decide +kernel
  unfold colE
  rw [hb]
  change eElt (fun i : Fin 6 => evalSignedWord gens3 (eW.getD i [])) (bitVec 6 63) ∈ lGrp
  rw [← heq]
  refine lGrp.list_prod_mem fun x hx => ?_
  obtain ⟨wd, hwd, rfl⟩ := List.mem_map.mp hx
  exact hlm wd hwd

theorem colE_unit (i : Fin 6) {X : ℕ} (hX : (fun r => matOfF 6 X r 0) = Pi.single i 1)
    (h : colE X ∈ lGrp) : elt (eW.getD i []) ∈ lGrp := by
  unfold colE at h
  rwa [hX, eElt_single] at h

theorem E_le_lGrp :
    ∀ i : Fin 6, elt (eW.getD i []) ∈ lGrp := by
  have h63 := colE_ones
  have h15 := colE_step (j := 0) (by norm_num) (Y := 266305) (by decide +kernel) h63
  have h25 := colE_step (j := 0) (by norm_num) (Y := 17039361) (by decide +kernel) h15
  have h8 := colE_step (j := 1) (by norm_num) (Y := 262144) (by decide +kernel) h25
  have h1 := colE_step (j := 2) (by norm_num) (Y := 1) (by decide +kernel) h8
  have h5 := colE_step (j := 1) (by norm_num) (Y := 4097) (by decide +kernel) h63
  have h40 := colE_step (j := 2) (by norm_num) (Y := 1074003968) (by decide +kernel) h5
  have h46 := colE_step (j := 2) (by norm_num) (Y := 1074008128) (by decide +kernel) h40
  have h36 := colE_step (j := 0) (by norm_num) (Y := 1073745920) (by decide +kernel) h46
  have h2 := colE_step (j := 0) (by norm_num) (Y := 64) (by decide +kernel) h36
  have h11 := colE_step (j := 0) (by norm_num) (Y := 262209) (by decide +kernel) h1
  have h4 := colE_step (j := 1) (by norm_num) (Y := 4096) (by decide +kernel) h11
  have h14 := colE_step (j := 2) (by norm_num) (Y := 266304) (by decide +kernel) h25
  have h37 := colE_step (j := 2) (by norm_num) (Y := 1073745921) (by decide +kernel) h14
  have h24 := colE_xor (Z := 17039360) (by decide +kernel) h25 h1
  have h16 := colE_xor (Z := 16777216) (by decide +kernel) h24 h8
  have h32 := colE_xor (Z := 1073741824) (by decide +kernel) h37 h5
  intro i
  fin_cases i
  · exact colE_unit 0 (by decide +kernel) h1
  · exact colE_unit 1 (by decide +kernel) h2
  · exact colE_unit 2 (by decide +kernel) h4
  · exact colE_unit 3 (by decide +kernel) h8
  · exact colE_unit 4 (by decide +kernel) h16
  · exact colE_unit 5 (by decide +kernel) h32

theorem eSub_le_lGrp :
    eSub ebasis_E ≤ lGrp := by
  rw [eSub_eq_closure]
  exact (Subgroup.closure_le _).mpr fun _ ⟨i, hi⟩ => hi ▸ E_le_lGrp i

theorem lGrp_eq :
    lGrp = Subgroup.closure (Set.range ![elt (lg 0), elt (lg 1), elt (lg 2)] ∪
      Set.range fun i : Fin 6 => elt (eW.getD i [])) := by
  apply le_antisymm
  · refine Subgroup.closure_mono fun x ⟨w, hw, hx⟩ => Or.inl ?_
    obtain ⟨j, hj, rfl⟩ := lsGenW_cases hw
    subst hx
    interval_cases j
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rcases hx with ⟨j, rfl⟩ | ⟨i, rfl⟩
    · fin_cases j <;> exact lg_mem_lGrp (by norm_num)
    · exact E_le_lGrp i

theorem cent_E'
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hc : x ∈ Subgroup.centralizer (eSub ebasis_E : Set (Equiv.Perm (Fin 8330)))) :
    x ∈ eSub ebasis_E :=
  cent_E hx fun i => (Subgroup.mem_centralizer_iff.mp hc _
    (mem_eSub ebasis_E ⟨i, by have := i.2; omega⟩)).symm

theorem cent_Q'
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hc : x ∈ Subgroup.centralizer (eSub ebasis_Q : Set (Equiv.Perm (Fin 8330)))) :
    x ∈ eSub ebasis_Q :=
  cent_Q hx fun i => (Subgroup.mem_centralizer_iff.mp hc _
    (mem_eSub ebasis_Q ⟨i, by have := i.2; omega⟩)).symm

theorem card_nsGrp :
    Nat.card nsGrp = 138240 := by
  have ha : ∀ j, ![elt (nsW.getD 6 []), elt (nsW.getD 11 [])] j ∈ eNorm ebasis_E :=
    Fin.forall_fin_two.mpr nsGen_mem_eNorm
  have hR : nsGrp ≤ heAutGroup := by
    refine closure_le_heAut fun x hx => ?_
    rcases hx with ⟨j, rfl⟩ | ⟨i, rfl⟩
    · fin_cases j
      · exact ⟨_, GW_letters2 0 (by norm_num), by rw [nsW_eq.1]; rfl⟩
      · exact ⟨_, GW_letters2 1 (by norm_num), by rw [nsW_eq.2]; rfl⟩
    · exact ⟨_, getD_letters eW_letters2 (by rw [eW_len]; exact i.2), rfl⟩
  have h := card_closure_of_recK ebasis_E _ ha (fun x hx hc => cent_E' (hR hx) hc)
    (G := gen NS) (fun j => by
      fin_cases j
      · exact eMat_E (ha 0) (congrArg elt nsW_eq.1) (GW_letters2 0 (by norm_num)) ch7223mNs0
      · exact eMat_E (ha 1) (congrArg elt nsW_eq.2) (GW_letters2 1 (by norm_num)) ch7223mNs1)
    (by norm_num) (by norm_num) ch7223ns_head ch7223ns_recs
  exact h.trans (by norm_num)

theorem card_n7Grp :
    Nat.card n7Grp = 21504 := by
  have ha : ∀ j, ![elt (n7W.getD 3 []), elt (n7W.getD 9 [])] j ∈ eNorm ebasis_Q :=
    Fin.forall_fin_two.mpr n7Gen_mem_eNorm
  have hR : n7Grp ≤ heAutGroup := by
    refine closure_le_heAut fun x hx => ?_
    rcases hx with ⟨j, rfl⟩ | ⟨i, rfl⟩
    · fin_cases j
      · exact ⟨_, GW_letters2 2 (by norm_num), by rw [n7W_eq.1]; rfl⟩
      · exact ⟨_, GW_letters2 3 (by norm_num), by rw [n7W_eq.2]; rfl⟩
    · exact ⟨_, getD_letters qW_letters2 (by rw [qW_len]; exact i.2), rfl⟩
  have h := card_closure_of_recK ebasis_Q _ ha (fun x hx hc => cent_Q' (hR hx) hc)
    (G := gen N7) (fun j => by
      fin_cases j
      · exact eMat_Q (ha 0) (congrArg elt n7W_eq.1) (GW_letters2 2 (by norm_num)) ch7223mN70
      · exact eMat_Q (ha 1) (congrArg elt n7W_eq.2) (GW_letters2 3 (by norm_num)) ch7223mN71)
    (by norm_num) (by norm_num) ch7223n7_head ch7223n7_recs
  exact h.trans (by norm_num)

theorem card_lGrp :
    Nat.card lGrp = 69120 := by
  have ha : ∀ j, ![elt (lg 0), elt (lg 1), elt (lg 2)] j ∈ eNorm ebasis_E := fun j => by
    fin_cases j <;> exact lg_mem_eNorm (by norm_num)
  have h := card_closure_of_recK ebasis_E _ ha
    (fun x hx hc => cent_E' (lGrp_le_heAut (by rw [lGrp_eq]; exact hx)) hc)
    (G := gen LS) (fun j => by
      fin_cases j
      · exact eMat_E (ha 0) rfl (LG_letters 0 (by norm_num)) ch7223mL0
      · exact eMat_E (ha 1) rfl (LG_letters 1 (by norm_num)) ch7223mL1
      · exact eMat_E (ha 2) rfl (LG_letters 2 (by norm_num)) ch7223mL2)
    (by norm_num) (by norm_num) ch7223ls_head ch7223ls_recs
  rw [lGrp_eq]
  exact h.trans (by norm_num)

theorem bBL_lt : ∀ i : Fin 6, bBL.getD i 0 < 8330 := by decide

@[expose] def bF (i : Fin 6) : Fin 8330 := ⟨bBL.getD i 0, bBL_lt i⟩

theorem bF_inj : Function.Injective bF := by
  intro i j h
  have h' : bBL.getD i 0 = bBL.getD j 0 := congrArg Fin.val h
  revert i j
  decide

theorem bF_mem (i : Fin 6) : ((bF i : Fin 8330) : ℕ) ∈ bB := by
  revert i
  decide

theorem exists_bF {p : Fin 8330} (hp : (p : ℕ) ∈ bB) : ∃ m, p = bF m := by
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  have hi6 : i < 6 := hi
  refine ⟨⟨i, hi6⟩, Fin.ext ?_⟩
  change (p : ℕ) = bBL.getD i 0
  rw [bBL_eq, List.getD_eq_getElem _ _ hi, hpi]

@[expose] noncomputable def rhoB (x : Equiv.Perm (Fin 8330)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r i => if x (bF i) = bF r then 1 else 0

theorem rhoB_one : rhoB 1 = 1 := by
  ext r i
  simp only [rhoB, Matrix.of_apply, Equiv.Perm.one_apply, Matrix.one_apply, bF_inj.eq_iff]
  by_cases h : r = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem rhoB_mul (x : Equiv.Perm (Fin 8330)) {y : Equiv.Perm (Fin 8330)}
    (hy : ∀ i, ∃ m, y (bF i) = bF m) : rhoB (x * y) = rhoB x * rhoB y := by
  ext r i
  obtain ⟨m, hm⟩ := hy i
  simp only [rhoB, Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.mul_apply, hm]
  rw [Finset.sum_eq_single m (fun k _ hk => by rw [if_neg (fun h => hk (bF_inj h).symm), mul_zero])
    (fun h => absurd (Finset.mem_univ m) h), if_pos rfl, mul_one]

theorem rhoB_eq_one_iff (x : Equiv.Perm (Fin 8330)) :
    rhoB x = 1 ↔ ∀ p : Fin 8330, (p : ℕ) ∈ bB → x p = p := by
  constructor
  · intro h p hp
    obtain ⟨m, rfl⟩ := exists_bF hp
    have e := congrFun (congrFun h m) m
    simp only [rhoB, Matrix.of_apply, Matrix.one_apply_eq] at e
    by_contra hne
    rw [if_neg hne] at e
    exact absurd e (by decide)
  · intro h
    ext r i
    simp only [rhoB, Matrix.of_apply, h (bF i) (bF_mem i), Matrix.one_apply, bF_inj.eq_iff]
    by_cases hri : r = i
    · simp [hri]
    · simp [hri, Ne.symm hri]

theorem lGrp_maps (x : Equiv.Perm (Fin 8330)) (hx : x ∈ lGrp) :
    ∀ i, ∃ m, x (bF i) = bF m := by
  unfold lGrp at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro i
    exact exists_bF (lsGen_maps_bB w hw (bF i) (bF_mem i))
  | one => exact fun i => ⟨i, rfl⟩
  | mul x y _ _ ihx ihy =>
    intro i
    obtain ⟨m, hm⟩ := ihy i
    obtain ⟨m', hm'⟩ := ihx m
    exact ⟨m', by rw [Equiv.Perm.mul_apply, hm, hm']⟩
  | inv x _ ihx =>
    intro i
    choose σ hσ using ihx
    have hinj : Function.Injective σ := fun a b hab =>
      bF_inj (x.injective (by rw [hσ, hσ, hab]))
    obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.mp hinj i
    exact ⟨m, by rw [← hm, ← hσ m, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]⟩

theorem rhoB_lg {j : ℕ}
    (hj : j < 3) (h : permBK (lg j) (gen BB j) = true) :
    rhoB (elt (lg j)) = matOfF 6 (gen BB j) := by
  ext r i
  simp only [rhoB, Matrix.of_apply]
  rw [matOfF_apply, ← testBit_colF 6 _ i r r.2, ← bit_eq_testBit]
  have h1 := allN_ct h i i.2
  unfold permBK at h1
  rw [strictB_eq'] at h1
  have h2 := allN_ct h1 r r.2
  have hev := evW_eq letRep_LU (lettersOK_mono (by rw [gens3_length]; norm_num)
    (LG_letters j hj)) (bF i)
  have hiff : elt (lg j) (bF i) = bF r ↔
      evW 8330 14 LU LUI (lg j) (bBL.getD i 0) = bBL.getD r 0 := by
    rw [Fin.ext_iff]
    change ((elt (lg j) (bF i) : Fin 8330) : ℕ) = _ ↔ _
    have hv : ((elt (lg j) (bF i) : Fin 8330) : ℕ) = evW 8330 14 LU LUI (lg j) (bBL.getD i 0) :=
      hev.symm
    rw [hv]
    rfl
  cases hb : CFSG.KLie.CT.bit (CFSG.KC.WordPts.colF 6 (gen BB j) i) r <;> rw [hb] at h2
  · have h2' : CFSG.KLie.CT.notB (Nat.beq (evW 8330 14 LU LUI (lg j) (bBL.getD i 0))
        (bBL.getD r 0)) = true := h2
    have hne : evW 8330 14 LU LUI (lg j) (bBL.getD i 0) ≠ bBL.getD r 0 := by
      intro he
      rw [he, Nat.beq_refl] at h2'
      exact absurd h2' (by decide)
    rw [if_neg (fun he => hne (hiff.mp he))]
    rfl
  · have h2' : Nat.beq (evW 8330 14 LU LUI (lg j) (bBL.getD i 0)) (bBL.getD r 0) = true := h2
    rw [if_pos (hiff.mpr (Nat.eq_of_beq_eq_true h2'))]
    rfl

theorem card_lFix :
    Nat.card {x : lGrp // ∀ p : Fin 8330, (p : ℕ) ∈ bB → (x : Equiv.Perm (Fin 8330)) p = p} =
      192 := by
  let ψ : lGrp →* Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    { toFun := fun x => rhoB x
      map_one' := rhoB_one
      map_mul' := fun x y => rhoB_mul x (lGrp_maps y y.2) }
  let g : Fin 3 → lGrp := fun j => ⟨elt (lg j), lg_mem_lGrp j.2⟩
  obtain ⟨h0, h12⟩ := andB_true ch7223lB
  obtain ⟨h1, h2⟩ := andB_true h12
  have hg : ∀ j : Fin 3, ψ (g j) = matOfF 6 (gen BB j) := fun j => by
    fin_cases j
    · exact rhoB_lg (by norm_num) h0
    · exact rhoB_lg (by norm_num) h1
    · exact rhoB_lg (by norm_num) h2
  have hgen : Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} = ⊤ := by
    rw [eq_top_iff, ← closure_preimage_eq_top (H := lGrp) (S := {x | ∃ w ∈ lsGenW, elt w = x}) rfl]
    refine Subgroup.closure_mono fun x hx => Or.inl ?_
    obtain ⟨w, hw, hx⟩ := hx
    obtain ⟨j, hj, rfl⟩ := lsGenW_cases hw
    exact ⟨⟨j, hj⟩, Subtype.ext hx⟩
  have hr := card_range_of_recK ψ g hg hgen (by norm_num) (by norm_num) ch7223bb_head
    ch7223bb_recs
  have hc := card_eq_card_ker_mul ψ
  rw [hr, card_lGrp] at hc
  have hk : Nat.card ψ.toHomUnits.ker =
      Nat.card {x : lGrp // ∀ p : Fin 8330, (p : ℕ) ∈ bB → (x : Equiv.Perm (Fin 8330)) p = p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (mem_ker_toHomUnits ψ x).trans (rhoB_eq_one_iff x))
  omega

end CertificateChecks.KernelHe7223

end
