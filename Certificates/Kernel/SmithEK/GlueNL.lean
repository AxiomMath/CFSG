module

public import Certificates.Kernel.SmithEK.ChecksNL
public import Certificates.Kernel.SmithEK.GlueNT
public import Certificates.Kernel.Misc.FischerDelta
public import CFSG.LargeExtraspecial.SMod20AutPlane
public import CFSG.LargeExtraspecial.S14SMKTransFp
public import CFSG.Certificates.Kernel.SmithL6KTSound
import all CFSG.Fischer.F4
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73 CFSG.LargeExtraspecial.SMod20
  CFSG.LargeExtraspecial.SMod20.Aut Matrix

open CFSG.LargeExtraspecial.S14.SMK (IsTab)

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts ptIdx uVec
  tvTabs

theorem isTab_idTab : IsTab idTab 1 := by
  intro x
  unfold idTab
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ x.2]
  rfl

theorem isTab_compTab {s t : Array Nat} {σ τ : Equiv.Perm (Fin 693)} (hs : IsTab s σ)
    (ht : IsTab t τ) : IsTab (compTab s t) (σ * τ) := by
  intro x
  unfold compTab
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ x.2]
  change s[t[x.val]!]! = (σ (τ x)).val
  rw [ht x]
  exact hs (τ x)

theorem invTab_foldl {s : Array Nat} {σ : Equiv.Perm (Fin 693)} (hs : IsTab s σ) :
    ∀ n ≤ 693,
      ((List.range n).foldl (fun r x => r.set! s[x]! x) (Array.replicate 693 0)).size = 693 ∧
      ∀ y : Fin 693,
        ((List.range n).foldl (fun r x => r.set! s[x]! x) (Array.replicate 693 0))[y.val]! =
          if (σ⁻¹ y).val < n then (σ⁻¹ y).val else 0
  | 0, _ => by
    refine ⟨by simp, fun y => ?_⟩
    rw [List.range_zero, List.foldl_nil, if_neg (Nat.not_lt_zero _),
      getElem!_pos _ y.val (by simp), Array.getElem_replicate]
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := invTab_foldl hs n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((List.range n).foldl (fun r x => r.set! s[x]! x) (Array.replicate 693 0)) = r
      at h1 h2
    have hn' : n < 693 := by omega
    rw [hs ⟨n, hn'⟩]
    refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, h1], fun y => ?_⟩
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ y.val (by
      rw [Array.size_setIfInBounds, h1]; exact y.2), Array.getElem_setIfInBounds]
    by_cases hy : σ ⟨n, hn'⟩ = y
    · have hv : (σ⁻¹ y).val = n := by rw [← hy, perm_inv_apply_self]
      rw [if_pos (congrArg Fin.val hy), if_pos (by omega), hv]
    · have hne : (σ ⁻¹ y).val ≠ n := by
        intro h
        apply hy
        rw [← Fin.ext (h.trans rfl : (σ⁻¹ y).val = (⟨n, hn'⟩ : Fin 693).val),
          perm_apply_inv_self]
      rw [if_neg (fun h => hy (Fin.ext h)), ← getElem!_pos r y.val (by rw [h1]; exact y.2), h2]
      by_cases hl : (σ⁻¹ y).val < n
      · rw [if_pos hl, if_pos (by omega)]
      · rw [if_neg hl, if_neg (by omega)]
    · rw [h1]
      exact y.2

theorem isTab_invTab {s : Array Nat} {σ : Equiv.Perm (Fin 693)} (hs : IsTab s σ) :
    IsTab (invTab s) σ⁻¹ := by
  intro y
  unfold invTab
  rw [(invTab_foldl hs 693 le_rfl).2 y, if_pos (σ⁻¹ y).2]

theorem invPairOK_of {t r : Array Nat} {σ : Equiv.Perm (Fin 693)} (ht : IsTab t σ)
    (hr : IsTab r σ⁻¹) : invPairOK t r = true := by
  unfold invPairOK
  rw [allIn_eq_true]
  intro x _ hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨by rw [ht ⟨x, hx⟩]; exact (σ _).2, by rw [hr ⟨x, hx⟩]; exact (σ⁻¹ _).2⟩, ?_⟩, ?_⟩
  · rw [ht ⟨x, hx⟩, hr (σ ⟨x, hx⟩), perm_inv_apply_self]
  · rw [hr ⟨x, hx⟩, ht (σ⁻¹ ⟨x, hx⟩), perm_apply_inv_self]

theorem normOK_of {t : Array Nat} {σ : Equiv.Perm (Fin 693)} (ht : IsTab t σ)
    (hσ : IsPolarAut σ) : normOK tvTabs t = true := by
  unfold normOK
  rw [allIn_eq_true]
  intro p _ hp
  rw [allIn_eq_true]
  intro x _ hx
  rw [beq_iff_eq, ap_tvTabs ⟨p, hp⟩ ⟨x, hx⟩, ht (tvP ⟨p, hp⟩ ⟨x, hx⟩), hσ.map_tvP, ht ⟨p, hp⟩,
    ht ⟨x, hx⟩, ap_tvTabs (σ ⟨p, hp⟩) (σ ⟨x, hx⟩)]

@[expose] def deltaM2 : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.diagonal fun i => if i.val < 2 then F4.ω else 1

@[expose] noncomputable def deltaGL2 : GL (Fin 6) F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero deltaM2 (by
    rw [deltaM2, Matrix.det_diagonal, Fin.prod_univ_six]
    decide)

theorem deltaGL2_val : ((deltaGL2 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = deltaM2 :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem omega_cube : F4.ω * F4.ω ^ 2 = 1 := by decide

theorem deltaGL2_isom : IsIsom ((deltaGL2 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
  intro x y
  rw [herm_eq, herm_eq, deltaGL2_val]
  apply Finset.sum_congr rfl
  intro i _
  rw [deltaM2, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
  by_cases hi : i.val < 2
  · simp only [hi, ite_true]
    rw [mul_pow, mul_mul_mul_comm, omega_cube, one_mul]
  · simp [hi]

@[expose] noncomputable def deltaGU2 : GU0 := ⟨deltaGL2, deltaGL2_isom⟩

theorem deltaGU2_cube : deltaGU2 ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  change deltaGL2.val ^ 3 = 1
  rw [deltaGL2_val, deltaM2, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Pi.pow_apply]
  split_ifs <;> decide

noncomputable abbrev permD : Equiv.Perm (Fin 693) := piGU deltaGU2

noncomputable abbrev permF : Equiv.Perm (Fin 693) := semiPerm 1 frob4

theorem permD_inv : permD⁻¹ = permD * permD := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ← pow_three', ← map_pow, deltaGU2_cube, map_one]

theorem foldl_six (F : Nat → Nat) :
    (List.range 6).foldl (fun acc i => acc + F i * 4 ^ i) 0 =
      F 0 + 4 * F 1 + 16 * F 2 + 64 * F 3 + 256 * F 4 + 1024 * F 5 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  omega

theorem coord_codeOf' (v : Fin 6 → F4) :
    coord (codeOf v) 0 = (v 0).code.val ∧ coord (codeOf v) 1 = (v 1).code.val ∧
      coord (codeOf v) 2 = (v 2).code.val ∧ coord (codeOf v) 3 = (v 3).code.val ∧
      coord (codeOf v) 4 = (v 4).code.val ∧ coord (codeOf v) 5 = (v 5).code.val :=
  ⟨coord_codeOf v 0, coord_codeOf v 1, coord_codeOf v 2, coord_codeOf v 3, coord_codeOf v 4,
    coord_codeOf v 5⟩

theorem frobC_codeOf (v : Fin 6 → F4) : frobC (codeOf v) = codeOf (fvec frob4 v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := coord_codeOf' v
  unfold frobC
  rw [foldl_six, h0, h1, h2, h3, h4, h5]
  simp only [codeOf, fvec_apply, frob4_apply, pow_two, code_mul]

theorem code_dl (i : Fin 6) (x : F4) : ((if i.val < 2 then F4.ω else 1) * x).code.val =
    if i.val < 2 then f4mul 2 x.code.val else x.code.val := by
  split_ifs
  · exact code_mul F4.ω x
  · rw [one_mul]

theorem dltC_codeOf (v : Fin 6 → F4) : dltC (codeOf v) = codeOf (deltaM2 *ᵥ v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := coord_codeOf' v
  unfold dltC
  rw [foldl_six, h0, h1, h2, h3, h4, h5]
  simp only [deltaM2, Matrix.mulVec_diagonal, codeOf, code_dl]
  rfl

theorem isTab_D : IsTab (ptMapT dltC) permD := by
  intro x
  unfold ptMapT
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ x.2]
  change uPos[normC (dltC uPts[x.val]!)]! = (deltaGU2 • x).val
  rw [smul_val, uPts_get x, dltC_codeOf, uPos_normC]
  rfl

theorem isTab_F : IsTab (ptMapT frobC) permF := by
  intro x
  unfold ptMapT
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ x.2]
  change uPos[normC (frobC uPts[x.val]!)]! = _
  rw [semiPerm_val, uPts_get x, frobC_codeOf, uPos_normC, semiVec]
  simp

theorem isPolarAut_semiPerm (A : GU0) (φ : F4 ≃+* F4) : IsPolarAut (semiPerm A φ) := by
  refine ⟨fun a b => semiPerm_orth A φ a b, fun a b => ?_⟩
  have h := congrArg (fun g : Equiv.Perm (Fin 693) => g (semiPerm A φ b)) (semiPerm_tvP A φ a)
  simp only [Equiv.Perm.mul_apply, perm_inv_apply_self] at h
  exact h

@[expose] noncomputable def liftP : Nat → Equiv.Perm (Fin 693)
  | 0 => 1
  | 1 => tvP 1 * tvP 13
  | 2 => permF
  | 3 => permD * permF * permD⁻¹
  | _ => permD * permD * permF * (permD * permD)⁻¹

theorem isTab_stab : IsTab (stabTab tvTabs 0) (tvP 1 * tvP 13) := by
  intro x
  unfold stabTab
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ x.2]
  change ap tvTabs[stabWords[0]!.1]! (ap tvTabs[stabWords[0]!.2]! x.val) = _
  have e : stabWords[0]! = (1, 13) := by decide
  have h13 : ap tvTabs[13]! x.val = (tvP 13 x).val := ap_tvTabs (13 : Fin 693) x
  have h1 : ap tvTabs[1]! (tvP 13 x).val = (tvP 1 (tvP 13 x)).val := ap_tvTabs (1 : Fin 693) _
  rw [e]
  change ap tvTabs[1]! (ap tvTabs[13]! x.val) = _
  rw [h13, h1]
  rfl

theorem isTab_liftP {j : Nat} (hj : j < 5) : IsTab (liftTab tvTabs j) (liftP j) := by
  interval_cases j
  · exact isTab_idTab
  · exact isTab_stab
  · exact isTab_F
  · exact isTab_compTab (isTab_compTab isTab_D isTab_F) (isTab_invTab isTab_D)
  · exact isTab_compTab (isTab_compTab (isTab_compTab isTab_D isTab_D) isTab_F)
      (isTab_invTab (isTab_compTab isTab_D isTab_D))

theorem isPolarAut_liftP {j : Nat} (hj : j < 5) : IsPolarAut (liftP j) := by
  have hD : IsPolarAut permD := CFSG.KD.Misc.Polar.isPolarAut_piGU deltaGU2
  have hF : IsPolarAut permF := isPolarAut_semiPerm 1 frob4
  interval_cases j
  · exact isPolarAut_one
  · exact (isPolarAut_tvP 1).mul (isPolarAut_tvP 13)
  · exact hF
  · exact (hD.mul hF).mul hD.inv
  · exact ((hD.mul hD).mul hF).mul (hD.mul hD).inv

theorem idxN_eq (L : List Nat) (c : Nat) : idxN L c = L.idxOf c := by
  induction L with
  | nil => rfl
  | cons x l ih =>
    rw [List.idxOf_cons]
    change Bool.rec (motive := fun _ => Nat) (Nat.succ (idxN l c)) 0 (Nat.beq x c) = _
    rw [ih]
    by_cases h : x = c
    · rw [h, Nat.beq_refl]
      simp
    · have hb : Nat.beq x c = false := by
        rw [Bool.eq_false_iff]
        exact fun h' => h (Nat.eq_of_beq_eq_true h')
      rw [hb]
      simp [h]

theorem ptMapT_get {f : Nat → Nat} (hf : ∀ v, ∃ w, f (codeOf v) = codeOf w) {y : Nat}
    (hy : y < 693) : (ptMapT f)[y]! = ptK CFSG.KD.Misc.Unitary.UL normC f y := by
  have e1 : uPts[y]! = CFSG.KD.Misc.Unitary.UL.getD y 0 := by
    rw [CFSG.KD.Misc.Unitary.hU, CFSG.KD.Misc.Unitary.getE]
  have hlt : normC (f uPts[y]!) < 4096 := by
    obtain ⟨w, hw⟩ := hf (uVec y)
    rw [uPts_get ⟨y, hy⟩, hw, normC_codeOf]
    exact codeOf_lt _
  unfold ptMapT
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hy, uPos_get hlt, e1, ptK, idxN_eq,
    CFSG.KD.Misc.Unitary.hU, List.toList_toArray]

theorem permD_val (y : Fin 693) : (permD y).val = ptK CFSG.KD.Misc.Unitary.UL normC dltC y.val := by
  rw [← isTab_D y, ptMapT_get (fun v => ⟨_, dltC_codeOf v⟩) y.2]

theorem permF_val (y : Fin 693) : (permF y).val = ptK CFSG.KD.Misc.Unitary.UL normC frobC y.val := by
  rw [← isTab_F y, ptMapT_get (fun v => ⟨_, frobC_codeOf v⟩) y.2]

theorem liftK_sound {L : List Nat} {nm dl fr : Nat → Nat} {P SG RT : List Nat}
    (h : liftK L nm dl fr P SG RT = true) :
    RT.length = 4 ∧ ∀ k < 21, liftAt L nm dl fr P SG RT k = true := by
  unfold liftK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  refine ⟨h.1, ?_⟩
  have key : ∀ n, Nat.rec (motive := fun _ => Bool) true
      (fun k acc => acc && liftAt L nm dl fr P SG RT k) n = true →
      ∀ k < n, liftAt L nm dl fr P SG RT k = true := by
    intro n
    induction n with
    | zero => intro _ k hk; omega
    | succ n ih =>
      intro hn k hk
      change ((Nat.rec (motive := fun _ => Bool) true
        (fun k acc => acc && liftAt L nm dl fr P SG RT k) n) &&
          liftAt L nm dl fr P SG RT n) = true at hn
      rw [Bool.and_eq_true] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ih hn.1 k hk
      · exact hn.2
  exact key 21 h.2

local notation "W0 " k:max => (uaPts[0]!)[k]!

theorem stabAp_W0 {g : Nat} (hg : g < 34) {k : Nat} (hk : k < 21) :
    stabAp tvTabs stabWords[g]! (W0 k) = W0 ((po.SG.getD g []).getD k 0) := by
  obtain ⟨-, hlt, -⟩ := uaPlane_parts (i := 0) (by omega)
  have hs := sgK_sound c21262sg_0 g (by rw [← c21262sw, List.length_map]; simpa using sw_lt.1 ▸ hg)
  have hsk : (po.SG.getD g []).getD k 0 < 21 := hs.2.1 _ (getD_mem (by rw [hs.1]; exact hk))
  have e1 := hs.2.2 k hk
  rw [sw_get hg, pl0_get hk, pl0_get hsk] at e1
  rw [(stabAp_TP (sw_mem hg) (hlt k hk)).1, ← e1]

theorem lift_W0 {j : Nat} (hj : j < 4) {k : Nat} (hk : k < 21) :
    at' 5 (pt.RT.getD j 0) k < 21 ∧
      (liftTab tvTabs (j + 1))[W0 k]! = W0 (at' 5 (pt.RT.getD j 0) k) := by
  obtain ⟨-, hlt, -⟩ := uaPlane_parts (i := 0) (by omega)
  have h := (liftK_sound c21275lift_0).2 k hk
  unfold liftAt at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, hs⟩, hF⟩, hDF⟩, hDDF⟩ := h
  have hx : (po.PL.getD 0 []).getD k 0 = W0 k := pl0_get hk
  have hxl : (W0 k) < 693 := hlt k hk
  rw [hx] at hF hDF hDDF
  interval_cases j
  · refine ⟨r0, ?_⟩
    change (stabTab tvTabs 0)[W0 k]! = _
    unfold stabTab
    rw [CFSG.SmithL6.Kernel.ofFn_get! _ hxl]
    change stabAp tvTabs stabWords[0]! (W0 k) = _
    rw [stabAp_W0 (by omega) hk, hs]
  · refine ⟨r1, ?_⟩
    rw [← pl0_get r1, ← hF]
    exact ptMapT_get (fun v => ⟨_, frobC_codeOf v⟩) hxl
  · refine ⟨r2, ?_⟩
    rw [← pl0_get r2, ← hDF, isTab_liftP (by omega) ⟨_, hxl⟩]
    change (permD (permF (permD⁻¹ ⟨_, hxl⟩))).val = _
    rw [permD_inv, Equiv.Perm.mul_apply, permD_val, permF_val, permD_val, permD_val]
  · refine ⟨r3, ?_⟩
    rw [← pl0_get r3, ← hDDF, isTab_liftP (by omega) ⟨_, hxl⟩]
    change (permD (permD (permF ((permD * permD)⁻¹ ⟨_, hxl⟩)))).val = _
    rw [← permD_inv, inv_inv, permD_val, permD_val, permF_val, permD_val]

theorem flag_W0 {m : Nat} (hm : m < 21) : ((uaFlags uaPts)[0]!)[W0 m]! = true := by
  obtain ⟨-, hlt, -⟩ := uaPlane_parts (i := 0) (by omega)
  unfold uaFlags
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ (by omega : 0 < 891),
    CFSG.SmithL6.Kernel.ofFn_get! _ (hlt m hm)]
  exact anyIn_eq_true.2 ⟨m, hm, beq_self_eq_true _⟩

theorem liftFacts : ∀ j < 5,
    invPairOK (liftTab tvTabs j) (invTab (liftTab tvTabs j)) = true ∧
      normOK tvTabs (liftTab tvTabs j) = true ∧
      ∀ k < 21, ((uaFlags uaPts)[0]!)[(liftTab tvTabs j)[W0 k]!]! = true := by
  intro j hj
  have ht := isTab_liftP hj
  refine ⟨invPairOK_of ht (isTab_invTab ht), normOK_of ht (isPolarAut_liftP hj), fun k hk => ?_⟩
  rcases j with _ | j
  · obtain ⟨-, hlt, -⟩ := uaPlane_parts (i := 0) (by omega)
    rw [ht ⟨_, hlt k hk⟩]
    exact flag_W0 hk
  · obtain ⟨hr, he⟩ := lift_W0 (by omega : j < 4) hk
    rw [he]
    exact flag_W0 hr

theorem sArrT_lift {j : Nat} (hj : j < 4) :
    sArrT uaPts[0]! (liftTab tvTabs (j + 1)) = ivUnpack (pt.RT.getD j 0) := by
  refine array_ext_getElem! (n := 21) (by unfold sArrT; exact Array.size_ofFn)
    (by unfold ivUnpack; exact Array.size_ofFn) fun k hk => ?_
  obtain ⟨hr, he⟩ := lift_W0 hj hk
  unfold sArrT
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hk, ivUnpack_get hk]
  change uaPos uaPts[0]! (liftTab tvTabs (j + 1))[W0 k]! = _
  rw [he, ← wPt_val (by omega) hr, uaPos_wPt (by omega) hr]

theorem reachL : CFSG.SmithL6.K.Reach 675 34
    (fun v => ((List.range 4).map fun j => sArrT uaPts[0]! (liftTab tvTabs (j + 1))).any
      fun r => r == collI[v]!)
    (fun g u v => collComp (collComp (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! collI[u]!)
      (stabWords.map fun w => stabSig tvTabs uaPts[0]! (w.2, w.1))[g]! == collI[v]!) := by
  refine CFSG.SmithL6.K.Reach.roots reachI fun v hv h => ?_
  unfold ivRootK at h
  obtain ⟨r, hr, he⟩ := List.any_eq_true.1 h
  rw [Nat.beq_eq] at he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hj4 : j < 4 := (liftK_sound c21275lift_0).1 ▸ hj
  refine List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj4, rfl⟩, ?_⟩
  rw [beq_iff_eq, sArrT_lift hj4, collI_get hv, ← he, List.getD_eq_getElem _ _ hj]

end CertificateChecks.KernelSmithEK
