module

public import Certificates.Kernel.HN1408.R0KChk
public import Certificates.Kernel.HN1408.AKFacts
public import Certificates.Kernel.HN1408.TableIGlue
public import Certificates.Kernel.HN1408.CayleyGlue

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.R0K

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KD.HN1408
open CFSG.KD.HN1408.CzT CFSG.KD.HN1408.AK

noncomputable abbrev Cz : Subgroup (Equiv.Perm (Fin 1408)) :=
  P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))

theorem anyK_of : ∀ {n : Nat} {f : Nat → Bool} {p : Nat}, p < n → f p = true → anyK n f = true
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, f, p, hp, hf => by
    change bIf(f n, true, anyK n f) = true
    cases hfn : f n
    · have hp' : p < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | h
        · exact h
        · rw [h, hfn] at hf
          exact absurd hf Bool.false_ne_true
      exact anyK_of hp' hf
    · rfl

theorem isBase_self (a b : Nat) : isBase a b a b = true := by
  unfold isBase
  rw [Nat.beq_refl, Nat.beq_refl]

theorem bIf_fst {c d : Bool} (h : c = true) : bIf(c, true, d) = true := by
  rw [h]

theorem bIf_snd {c d : Bool} (h : d = true) : bIf(c, true, d) = true := by
  cases c
  · exact h
  · rfl

theorem ptv {R : Nat} {r : Equiv.Perm (Fin 1408)} (hR : RepC R r) (y : Fin 1408) :
    (r y).val = pt R y.val :=
  (repC_pt hR y.isLt).symm

theorem pt2 {X Y x : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h)
    (hx : x < 1408) : pt X (pt Y x) = ((g * h) ⟨x, hx⟩).val := by
  rw [Equiv.Perm.mul_apply, ptv hX, ptv hY]

theorem eqB (hP : Nat.card ↥P1408 = 177408000) {g v : Equiv.Perm (Fin 1408)} (hg : g ∈ Cz)
    (hv : v ∈ Cz) (h0 : (g ⟨0, by norm_num⟩).val = (v ⟨0, by norm_num⟩).val)
    (h1 : (g ⟨1, by norm_num⟩).val = (v ⟨1, by norm_num⟩).val) : g = v :=
  eq_of_base hP hg hv (Fin.ext h0) (Fin.ext h1)

theorem repZ : RepC (WK wordZ) elemZ := repC_word (by decide)

theorem z_cz : elemZ ∈ Cz := by
  rw [← u0_eq]
  exact uE_cent (by norm_num)

theorem rU : ∀ l, l < 6 → RepC (U l) (uE l) := fun _ hl => repU hl

theorem itv (k : Nat) (y : Fin 1408) :
    (itE k y).val = itP (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) k y.val :=
  (itP_eq (rU 0 (by norm_num)) (rU 1 (by norm_num)) (rU 2 (by norm_num)) (rU 3 (by norm_num))
    (rU 4 (by norm_num)) (rU 5 (by norm_num)) k y.val y.isLt).symm

theorem itq (k x : Nat) (hx : x < 1408) :
    itP (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) k x = (itE k ⟨x, hx⟩).val :=
  itP_eq (rU 0 (by norm_num)) (rU 1 (by norm_num)) (rU 2 (by norm_num)) (rU 3 (by norm_num))
    (rU 4 (by norm_num)) (rU 5 (by norm_num)) k x hx

theorem cnt1 : TI1.cnt = 256 := (headI_spec kH1).2.2.1

theorem nW_len : nWords1.length = 7 := (headI_spec kH1).1

theorem gi1 {j : Nat} (hj : j < 7) : TI1.GI j = WK (nWords1.getD j []) :=
  ((headI_spec kH1).2.1 j hj).1

theorem cn1 {p : Nat} (hp : p < 256) : Cn (TI1.T p) := r1.2.2 p (by rw [cnt1]; exact hp)

theorem enum1 : IsEnumSet 1408 (hRec 1408 11 TI1.cnt TI1.T TI1.PL).1
    (wordSubgroup nWords1 : Set (Equiv.Perm (Fin 1408))) := by
  rw [← r1.2.1]
  exact (enumW_spec' r1.1).2.1

theorem rec_mem {p : Nat} (hp : p < 256) : ∃ g ∈ wordSubgroup nWords1, RepC (TI1.T p) g := by
  have hp' : p < TI1.cnt := by rw [cnt1]; exact hp
  obtain ⟨g, hg, hr⟩ := enum1.rep p (by rw [hRec_size]; exact hp')
  rw [hRec_get hp'] at hr
  exact ⟨g, hg, cn1 hp, hr⟩

theorem rec_cov {g : Equiv.Perm (Fin 1408)} (hg : g ∈ wordSubgroup nWords1) :
    ∃ p < 256, RepC (TI1.T p) g := by
  obtain ⟨k, hk, hr⟩ := enum1.cov g hg
  rw [hRec_size] at hk
  rw [hRec_get hk] at hr
  rw [cnt1] at hk
  exact ⟨k, hk, cn1 hk, hr⟩

theorem r0_card : Nat.card ↥(wordSubgroup nWords1) = 256 := (enumW_spec' r1.1).1

theorem gen_letters1 {j : Nat} (hj : j < 7) : lettersOK (nWords1.getD j []) = true := by
  interval_cases j <;> decide

theorem repX {j : Nat} (hj : j < 7) : RepC (TI1.GI j) (elemW (nWords1.getD j [])) := by
  rw [gi1 hj]
  exact repC_word (gen_letters1 hj)

theorem nWords1_mem {w : List Nat} (hw : w ∈ nWords1) : ∃ j < 7, nWords1.getD j [] = w := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  exact ⟨j, by rw [← nW_len]; exact hj, List.getD_eq_getElem _ _ hj⟩

theorem genX_mem {j : Nat} (hj : j < 7) : elemW (nWords1.getD j []) ∈ wordSubgroup nWords1 := by
  rw [List.getD_eq_getElem _ _ (by rw [nW_len]; exact hj)]
  exact elemW_mem_wordSubgroup (List.getElem_mem _)

theorem gen_commZ {j : Nat} (hj : j < 7) : commP (TI1.GI j) (WK wordZ) = true := by
  have t := kT1
  simp only [bAnd_iff] at t
  have h := allN_spec t.1 j hj
  simp only [bAnd_iff] at h
  exact h.2

theorem r0_le : wordSubgroup nWords1 ≤ Cz := by
  unfold wordSubgroup
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := nWords1_mem hw
  exact mem_cent_of (repX hj) (elemW_mem _) (gen_commZ hj)

theorem sq_parts : ∀ p < 256,
    bIf(isBase (pt (TI1.T p) (pt (TI1.T p) 0)) (pt (TI1.T p) (pt (TI1.T p) 1)) 0 1, true,
      isBase (pt (TI1.T p) (pt (TI1.T p) 0)) (pt (TI1.T p) (pt (TI1.T p) 1))
        (pt (WK wordZ) 0) (pt (WK wordZ) 1)) = true := by
  have h := ch441665sq
  unfold sqK at h
  simp only [strictB_app] at h
  exact fun p hp => allN_spec h p hp

theorem r0_sq (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)}
    (hg : g ∈ wordSubgroup nWords1) : g * g = 1 ∨ g * g = elemZ := by
  obtain ⟨p, hp, hr⟩ := rec_cov hg
  have hgC := r0_le hg
  rcases mkIf (sq_parts p hp) with ⟨hb, -⟩ | ⟨-, hb⟩
  · left
    obtain ⟨b0, b1⟩ := isBase_of hb
    rw [pt2 hr hr (x := 0) (by norm_num)] at b0
    rw [pt2 hr hr (x := 1) (by norm_num)] at b1
    exact eqB hP (mul_mem hgC hgC) (one_mem _) b0 b1
  · right
    obtain ⟨b0, b1⟩ := isBase_of hb
    rw [pt2 hr hr (x := 0) (by norm_num), repC_pt repZ (x := 0) (by norm_num)] at b0
    rw [pt2 hr hr (x := 1) (by norm_num), repC_pt repZ (x := 1) (by norm_num)] at b1
    exact eqB hP (mul_mem hgC hgC) z_cz b0 b1

theorem norm_parts : ∀ l < 2, ∀ j < 7, normRow TI1.T (CzT.G l) (TI1.GI j) = true := by
  have h := ch441665norm
  unfold normK at h
  simp only [strictB_app] at h
  intro l hl j hj
  exact allN_spec (allN_spec h l hl) j hj

theorem normRow_parts {T : Nat → Nat} {C X : Nat} (h : normRow T C X = true) :
    (∃ p < 256, isBase (pt (T p) (pt C 0)) (pt (T p) (pt C 1)) (pt C (pt X 0))
      (pt C (pt X 1)) = true) ∧
    (∃ q < 256, isBase (pt C (pt (T q) 0)) (pt C (pt (T q) 1)) (pt X (pt C 0))
      (pt X (pt C 1)) = true) := by
  unfold normRow at h
  simp only [strictB_app] at h
  obtain ⟨a, b⟩ := mkA h
  exact ⟨anyK_spec a, anyK_spec b⟩

theorem norm_conj (hP : Nat.card ↥P1408 = 177408000) {l j : Nat} (hl : l < 2) (hj : j < 7) :
    elemW (classz.centGens.getD l []) * elemW (nWords1.getD j []) *
        (elemW (classz.centGens.getD l []))⁻¹ ∈ wordSubgroup nWords1 ∧
      (elemW (classz.centGens.getD l []))⁻¹ * elemW (nWords1.getD j []) *
        elemW (classz.centGens.getD l []) ∈ wordSubgroup nWords1 := by
  obtain ⟨⟨p, hp, hb⟩, ⟨q, hq, hb'⟩⟩ := normRow_parts (norm_parts l hl j hj)
  obtain ⟨t, ht, hrt⟩ := rec_mem hp
  obtain ⟨s, hs, hrs⟩ := rec_mem hq
  have hC := repC_G hl
  have hX := repX hj
  have cC : elemW (classz.centGens.getD l []) ∈ Cz := le_cent (gen_mem hl)
  have xC := r0_le (genX_mem hj)
  obtain ⟨b0, b1⟩ := isBase_of hb
  rw [pt2 hrt hC (x := 0) (by norm_num), pt2 hC hX (x := 0) (by norm_num)] at b0
  rw [pt2 hrt hC (x := 1) (by norm_num), pt2 hC hX (x := 1) (by norm_num)] at b1
  have e := eqB hP (mul_mem (r0_le ht) cC) (mul_mem cC xC) b0 b1
  obtain ⟨c0, c1⟩ := isBase_of hb'
  rw [pt2 hC hrs (x := 0) (by norm_num), pt2 hX hC (x := 0) (by norm_num)] at c0
  rw [pt2 hC hrs (x := 1) (by norm_num), pt2 hX hC (x := 1) (by norm_num)] at c1
  have e' := eqB hP (mul_mem cC (r0_le hs)) (mul_mem xC cC) c0 c1
  constructor
  · rw [← e, mul_inv_cancel_right]
    exact ht
  · rw [mul_assoc, ← e', inv_mul_cancel_left]
    exact hs

theorem conj_closure {c : Equiv.Perm (Fin 1408)}
    (h : ∀ j < 7, c * elemW (nWords1.getD j []) * c⁻¹ ∈ wordSubgroup nWords1) :
    ∀ x ∈ wordSubgroup nWords1, c * x * c⁻¹ ∈ wordSubgroup nWords1 := by
  intro x hx
  have hle : closure (elemW '' {w | w ∈ nWords1}) ≤
      (wordSubgroup nWords1).comap (MulAut.conj c).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := nWords1_mem hw
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h j hj
  have := hle hx
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem gen_norm (hP : Nat.card ↥P1408 = 177408000) {l : Nat} (hl : l < 2) :
    elemW (classz.centGens.getD l []) ∈
      normalizer (wordSubgroup nWords1 : Set (Equiv.Perm (Fin 1408))) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact conj_closure (fun j hj => (norm_conj hP hl hj).1) x
  · intro hx
    have h := conj_closure (c := (elemW (classz.centGens.getD l []))⁻¹)
      (fun j hj => by rw [inv_inv]; exact (norm_conj hP hl hj).2) _ hx
    have e : (elemW (classz.centGens.getD l []))⁻¹ * (elemW (classz.centGens.getD l []) * x *
        (elemW (classz.centGens.getD l []))⁻¹) * (elemW (classz.centGens.getD l []))⁻¹⁻¹ = x := by
      group
    rwa [e] at h

theorem r0_normal (hP : Nat.card ↥P1408 = 177408000) {c : Equiv.Perm (Fin 1408)} (hc : c ∈ Cz)
    {x : Equiv.Perm (Fin 1408)} (hx : x ∈ wordSubgroup nWords1) :
    c * x * c⁻¹ ∈ wordSubgroup nWords1 := by
  have hle : czC ≤ normalizer (wordSubgroup nWords1 : Set (Equiv.Perm (Fin 1408))) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ : ∃ l < 2, classz.centGens.getD l [] = w := by
      have hw' : w ∈ classz.centGens := hw
      simp only [classz, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    exact gen_norm hP hl
  have hc' : c ∈ czC := by
    rw [(czT_eq hP).1]
    exact hc
  exact (mem_normalizer_iff.1 (hle hc') x).1 hx

theorem inter_parts : ∀ k < 64,
    bIf(anyK 256 fun p => isBase (pt (TI1.T p) 0) (pt (TI1.T p) 1)
        (itP (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) k 0) (itP (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) k 1),
      Nat.beq (bilC k 1) 0, bIf(Nat.beq (bilC k 1) 0, false, true)) = true := by
  have h := ch441665inter
  unfold withU interK at h
  simp only [strictB_app] at h
  exact fun k hk => allN_spec h k hk

theorem inter_iff (hP : Nat.card ↥P1408 = 177408000) {k : Nat} (hk : k < 64) :
    itE k ∈ wordSubgroup nWords1 ↔ bilC k 1 = 0 := by
  rcases mkIf (inter_parts k hk) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨fun _ => Nat.eq_of_beq_eq_true hb, fun _ => ?_⟩
    obtain ⟨p, hp, hbs⟩ := anyK_spec ha
    obtain ⟨t, ht, hrt⟩ := rec_mem hp
    obtain ⟨b0, b1⟩ := isBase_of hbs
    rw [repC_pt hrt (x := 0) (by norm_num), itq k 0 (by norm_num)] at b0
    rw [repC_pt hrt (x := 1) (by norm_num), itq k 1 (by norm_num)] at b1
    rw [← eqB hP (r0_le ht) (itE_cent k) b0 b1]
    exact ht
  · have hne := mkNot hb
    refine ⟨fun hm => ?_, fun h0 => ?_⟩
    · obtain ⟨p, hp, hr⟩ := rec_cov hm
      have : (anyK 256 fun p => isBase (pt (TI1.T p) 0) (pt (TI1.T p) 1)
          (itP (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) k 0)
          (itP (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) k 1)) = true := by
        refine anyK_of hp ?_
        beta_reduce
        rw [repC_pt hr (x := 0) (by norm_num), repC_pt hr (x := 1) (by norm_num),
          itq k 0 (by norm_num), itq k 1 (by norm_num)]
        exact isBase_self _ _
      rw [ha] at this
      exact absurd this Bool.false_ne_true
    · rw [h0, Nat.beq_refl] at hne
      exact absurd hne (by decide)

theorem eich_parts : ∀ p < 256, ∃ u < 64, etaB u = true ∧
    eichB (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) 1 (TI1.T p) u = true := by
  have h := ch441665eich
  unfold withU eichK at h
  simp only [strictB_app] at h
  intro p hp
  obtain ⟨u, hu, hb⟩ := anyK_spec (allN_spec h p hp)
  obtain ⟨a, b⟩ := mkA hb
  exact ⟨u, hu, a, b⟩

theorem surj_parts : ∀ u < 64, etaB u = true → ∃ p < 256,
    eichB (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) 1 (TI1.T p) u = true := by
  have h := ch441665surj
  unfold withU surjK at h
  simp only [strictB_app] at h
  intro u hu he
  rcases mkIf (allN_spec h u hu) with ⟨-, h2⟩ | ⟨h2, -⟩
  · exact anyK_spec h2
  · rw [he] at h2
    exact absurd h2 (by decide)

theorem eichB_parts {X0 X1 X2 X3 X4 X5 w R u : Nat} (h : eichB X0 X1 X2 X3 X4 X5 w R u = true) :
    ∀ k < 64, pt R (itP X0 X1 X2 X3 X4 X5 k 0) = itP X0 X1 X2 X3 X4 X5 (eichC w u k) (pt R 0) ∧
      pt R (itP X0 X1 X2 X3 X4 X5 k 1) = itP X0 X1 X2 X3 X4 X5 (eichC w u k) (pt R 1) := by
  unfold eichB at h
  simp only [strictB_app] at h
  intro k hk
  obtain ⟨a, b⟩ := mkA (allN_spec h k hk)
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem eich_rel (hP : Nat.card ↥P1408 = 177408000) {r : Equiv.Perm (Fin 1408)}
    (hr : r ∈ wordSubgroup nWords1) {R u : Nat} (hR : RepC R r)
    (h : eichB (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) 1 R u = true) {k : Nat} (hk : k < 64) :
    r * itE k = itE (eichC 1 u k) * r := by
  obtain ⟨e0, e1⟩ := eichB_parts h k hk
  refine eqB hP (mul_mem (r0_le hr) (itE_cent k)) (mul_mem (itE_cent _) (r0_le hr)) ?_ ?_
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ptv hR, itv, itv, ptv hR]
    exact e0
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ptv hR, itv, itv, ptv hR]
    exact e1

theorem eich_ex (hP : Nat.card ↥P1408 = 177408000) {r : Equiv.Perm (Fin 1408)}
    (hr : r ∈ wordSubgroup nWords1) :
    ∃ u < 64, etaB u = true ∧ ∀ k < 64, r * itE k = itE (eichC 1 u k) * r := by
  obtain ⟨p, hp, hR⟩ := rec_cov hr
  obtain ⟨u, hu, he, hb⟩ := eich_parts p hp
  exact ⟨u, hu, he, fun k hk => eich_rel hP hr hR hb hk⟩

theorem surj_ex (hP : Nat.card ↥P1408 = 177408000) {u : Nat} (hu : u < 64) (he : etaB u = true) :
    ∃ r ∈ wordSubgroup nWords1, ∀ k < 64, r * itE k = itE (eichC 1 u k) * r := by
  obtain ⟨p, hp, hb⟩ := surj_parts u hu he
  obtain ⟨r, hr, hR⟩ := rec_mem hp
  exact ⟨r, hr, fun k hk => eich_rel hP hr hR hb hk⟩

theorem faith_parts : czScan T0 T1 (faithRow (TI1.GI 0) (TI1.GI 1) (TI1.GI 2) (TI1.GI 3)
    (TI1.GI 4) (TI1.GI 5) (TI1.GI 6) (WK wordZ) 256 TI1.T) = true := by
  have h := ch441665faith
  unfold faithK at h
  simp only [strictB_app] at h
  exact h

theorem mzB_of {A B H : Nat} {g h : Equiv.Perm (Fin 1408)}
    (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (g ⟨x, hx⟩).val) (hH : RepC H h)
    (hc : g * h = h * g ∨ g * h = elemZ * h * g) :
    mzB A B H (WK wordZ) (pt A (pt B 0)) (pt A (pt B 1)) = true := by
  have evv : ∀ y : Fin 1408, pt A (pt B y.val) = (g y).val := fun y => hev y.val y.isLt
  have l0 : ∀ x (hx : x < 1408), pt A (pt B (pt H x)) = ((g * h) ⟨x, hx⟩).val := by
    intro x hx
    rw [repC_pt hH hx, evv, Equiv.Perm.mul_apply]
  have r0 : ∀ x (hx : x < 1408), pt H (pt A (pt B x)) = ((h * g) ⟨x, hx⟩).val := by
    intro x hx
    rw [hev x hx, ← ptv hH, Equiv.Perm.mul_apply]
  have z0 : ∀ x (hx : x < 1408), pt (WK wordZ) ((h * g) ⟨x, hx⟩).val =
      ((elemZ * h * g) ⟨x, hx⟩).val := by
    intro x hx
    rw [← ptv repZ]
    simp only [Equiv.Perm.mul_apply]
  unfold mzB
  simp only [strictB_app]
  rw [l0 0 (by norm_num), l0 1 (by norm_num), r0 0 (by norm_num), r0 1 (by norm_num),
    z0 0 (by norm_num), z0 1 (by norm_num)]
  rcases hc with hc | hc
  · rw [hc]
    exact bIf_fst (isBase_self _ _)
  · rw [hc]
    exact bIf_snd (isBase_self _ _)

theorem faith (hP : Nat.card ↥P1408 = 177408000) {c : Equiv.Perm (Fin 1408)} (hc : c ∈ Cz)
    (hx : ∀ j < 7, c * elemW (nWords1.getD j []) = elemW (nWords1.getD j []) * c ∨
      c * elemW (nWords1.getD j []) = elemZ * elemW (nWords1.getD j []) * c) :
    c ∈ wordSubgroup nWords1 := by
  refine scan_sound hP (Q := fun g => (∀ j < 7, g * elemW (nWords1.getD j []) =
      elemW (nWords1.getD j []) * g ∨
      g * elemW (nWords1.getD j []) = elemZ * elemW (nWords1.getD j []) * g) →
    g ∈ wordSubgroup nWords1) faith_parts ?_ c hc hx
  intro i hi jj hjj hrow hq
  have hev : ∀ x (hx : x < 1408), pt (T0 i) (pt (T1 jj) x) = ((t0P i * t1P jj) ⟨x, hx⟩).val :=
    fun x hx => ev_eq hi hjj hx
  unfold faithRow at hrow
  simp only [strictB_app] at hrow
  rcases mkIf hrow with ⟨-, hany⟩ | ⟨hf, -⟩
  · obtain ⟨p, hp, hb⟩ := anyK_spec hany
    obtain ⟨t, ht, hrt⟩ := rec_mem hp
    have e : t0P i * t1P jj = t := base_eq hP ((mem_iff hP).2 ⟨i, hi, jj, hjj, rfl⟩) (r0_le ht)
      hev (repC_pt hrt (x := 0) (by norm_num)).symm (repC_pt hrt (x := 1) (by norm_num)).symm hb
    rw [e]
    exact ht
  · rw [mzB_of hev (repX (j := 0) (by norm_num)) (hq 0 (by norm_num)),
      mzB_of hev (repX (j := 1) (by norm_num)) (hq 1 (by norm_num)),
      mzB_of hev (repX (j := 2) (by norm_num)) (hq 2 (by norm_num)),
      mzB_of hev (repX (j := 3) (by norm_num)) (hq 3 (by norm_num)),
      mzB_of hev (repX (j := 4) (by norm_num)) (hq 4 (by norm_num)),
      mzB_of hev (repX (j := 5) (by norm_num)) (hq 5 (by norm_num)),
      mzB_of hev (repX (j := 6) (by norm_num)) (hq 6 (by norm_num))] at hf
    exact absurd hf (by decide)

theorem f_letters : ∀ w ∈ fWords, lettersOK w = true := by decide

theorem f_len : fWords.length = 2 := rfl

theorem fz_parts : ∀ j < 2, commP (WK (fWords.getD j [])) (WK wordZ₁) = true := by
  have h := ch441665fz
  unfold commWK at h
  exact fun j hj => allN_spec h j hj

theorem f_le : wordSubgroup fWords ≤ P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) := by
  unfold wordSubgroup
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hw : w ∈ fWords)
  have hj' : j < 2 := by rw [← f_len]; exact hj
  rw [← List.getD_eq_getElem _ [] hj]
  refine mem_inf.2 ⟨elemW_mem _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hw' : lettersOK (fWords.getD j []) = true := by interval_cases j <;> decide
  have hz1 : RepC (WK wordZ₁) elemZ₁ := repC_word (by decide)
  exact comm_of_commP (repC_word hw') hz1 (fz_parts j hj')

@[expose] def a5Enc (s : ↥(alternatingGroup (Fin 5))) : Nat :=
  ((s : Equiv.Perm (Fin 5)) ⟨0, by decide⟩).val + 5 * ((s : Equiv.Perm (Fin 5)) ⟨1, by decide⟩).val +
    25 * ((s : Equiv.Perm (Fin 5)) ⟨2, by decide⟩).val +
    125 * ((s : Equiv.Perm (Fin 5)) ⟨3, by decide⟩).val +
    625 * ((s : Equiv.Perm (Fin 5)) ⟨4, by decide⟩).val

theorem a5Enc_dg (s : ↥(alternatingGroup (Fin 5))) (d : Fin 5) :
    dg5 (a5Enc s) d.val = ((s : Equiv.Perm (Fin 5)) d).val := by
  have h0 := ((s : Equiv.Perm (Fin 5)) ⟨0, by decide⟩).isLt
  have h1 := ((s : Equiv.Perm (Fin 5)) ⟨1, by decide⟩).isLt
  have h2 := ((s : Equiv.Perm (Fin 5)) ⟨2, by decide⟩).isLt
  have h3 := ((s : Equiv.Perm (Fin 5)) ⟨3, by decide⟩).isLt
  have h4 := ((s : Equiv.Perm (Fin 5)) ⟨4, by decide⟩).isLt
  unfold dg5 a5Enc
  obtain ⟨d, hd⟩ := d
  interval_cases d
  · change _ / 1 % 5 = _
    omega
  · change _ / 5 % 5 = _
    omega
  · change _ / 25 % 5 = _
    omega
  · change _ / 125 % 5 = _
    omega
  · change _ / 625 % 5 = _
    omega

theorem a5Enc_inj : Function.Injective a5Enc := by
  intro s t h
  apply Subtype.ext
  apply Equiv.ext
  intro d
  apply Fin.ext
  rw [← a5Enc_dg s d, ← a5Enc_dg t d, h]

theorem a5Enc_mul (s t : ↥(alternatingGroup (Fin 5))) :
    a5Enc (s * t) = a5Mul (a5Enc s) (a5Enc t) := by
  unfold a5Mul
  rw [a5Enc_dg t ⟨0, by decide⟩, a5Enc_dg t ⟨1, by decide⟩, a5Enc_dg t ⟨2, by decide⟩,
    a5Enc_dg t ⟨3, by decide⟩, a5Enc_dg t ⟨4, by decide⟩, a5Enc_dg s, a5Enc_dg s, a5Enc_dg s,
    a5Enc_dg s, a5Enc_dg s]
  rfl

@[expose] def a5Code : CodeM ↥(alternatingGroup (Fin 5)) := ⟨a5Enc, a5Mul, a5Enc_inj, a5Enc_mul⟩

theorem f_cay : cayleyOK aCap 60 fWords imgA5 = true :=
  cayleyOK_of a5Code f_letters ch441665fHd ch441665fRec rfl (by decide) (by decide) ch441665fCay

end CFSG.KD.HN1408.R0K

end
