module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ClassData
public import Certificates.Kernel.G24Cls.Chk27203
public import Certificates.Kernel.G24Cls.Inv27203
public import Certificates.Kernel.G24Tri.C27206
public import CFSG.Certificates.Kernel.G24KeySound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutList
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBasic
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelG24.Cls27203

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G24Key CFSG.KC.G24Tri
  CFSG.KC.DigitScan CertificateChecks.KernelG24.Tri27206
  CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co1Block

theorem ap_eq_pg (P p : ℕ) : ap P p = pg 11 (mask 11) P p := by
  rw [CFSG.KC.Pack.mask_eq]
  rfl

theorem ptRep_inv {P Q : ℕ} {g : Pm} (hP : PtRep P g) (hQ : ∀ i < 1365, ap Q (ap P i) = i) :
    PtRep Q g⁻¹ := fun x => by
  have h := hQ _ (g⁻¹ x).2
  have e : ap P (g⁻¹ x) = x := by rw [hP]; simp
  rw [e] at h
  exact h

theorem rep_of_invEqK {P Q : ℕ} (h : invEqK 1365 11 (mask 11) (1365 * 11) P Q = true) :
    Rep 1365 (unpack 1365 11 P) (permOfArr 1365 (unpack 1365 11 P)) ∧
      PtRep P (permOfArr 1365 (unpack 1365 11 P)) ∧
      PtRep Q (permOfArr 1365 (unpack 1365 11 P))⁻¹ := by
  have h1 := invEqK_sound h
  have hr := rep_permOfArr h1.2
  exact ⟨hr.1, ptRep_of_rep hr.1, ptRep_of_rep hr.2⟩

section Letters


theorem ya_eq : ya = unpack 1365 11 (LC.S 1) := by
  have h : ya = twoBStrong[1]! := rfl
  rw [h, CertificateChecks.KernelCo1B.Tri2045.strong_facts.2 1 (by norm_num),
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR 1 (by norm_num))]

@[expose] noncomputable def gxy (l : ℕ) : Pm := gGen 1 (Nat.land l 1)

theorem land1_lt (l : ℕ) : Nat.land l 1 < 2 := by
  change l &&& 1 < 2
  rw [Nat.and_one_is_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem ptLC {j : ℕ} (hj : j < 2) : PtRep (LC.S j) (gGen 1 j) := by
  interval_cases j
  · have h := rep_xa
    rw [xa_eq] at h
    have e : gGen 1 0 = xBar := by simp [gGen]
    rw [e]
    exact ptRep_of_rep h
  · have h := rep_ya
    rw [ya_eq] at h
    have e : gGen 1 1 = yBar := by simp [gGen]
    rw [e]
    exact ptRep_of_rep h

theorem ptS (l : ℕ) : PtRep (xyS l) (gxy l) := ptLC (land1_lt l)

theorem ptSI (l : ℕ) : PtRep (xySI l) (gxy l)⁻¹ := by
  refine ptRep_inv (ptS l) fun i hi => ?_
  have h := CFSG.KC.EnumSound.permOK_sound (n := 1365) (w := 11)
    (CFSG.KC.Pack.allN_spec kP (Nat.land l 1) (by have := land1_lt l; omega))
  rw [ap_eq_pg, ap_eq_pg]
  exact (h.2.2 i hi).2

theorem gxy_mem (l : ℕ) : gxy l ∈ twoBD := by
  have := land1_lt l
  unfold gxy
  rcases (by omega : Nat.land l 1 = 0 ∨ Nat.land l 1 = 1) with h | h
  · have e : gGen 1 0 = xBar := by simp [gGen]
    rw [h, e]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have e : gGen 1 1 = yBar := by simp [gGen]
    rw [h, e]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end Letters

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c =
    (if c = true then t else e) := by
  cases c <;> rfl

theorem cls_eq : clsNums = (CFSG.KC.Co1BPair.numsOf CT.chars).toArray := by
  have h : clsNums = parseNums clsText := rfl
  rw [h, CT.eq]
  exact nums_eq _ (scanK_sound kTextC).1

theorem cls_len : (CFSG.KC.Co1BPair.numsOf CT.chars).length = 72575 := (scanK_sound kTextC).2.1

theorem cls_get {i : ℕ} (hi : i < 72575) :
    fCls i (clsNums[i]!) = true := by
  have h := (scanK_sound kTextC).2.2 i hi
  rw [cls_eq]
  have hi' : i < (CFSG.KC.Co1BPair.numsOf CT.chars).length := by rw [cls_len]; exact hi
  simpa [getElem!_def, List.getD_eq_getElem?_getD, hi'] using h

theorem cls_size : clsNums.size = 72575 := by
  rw [cls_eq, List.size_toArray, cls_len]

theorem extract_get (a : Array ℕ) {s e x : ℕ} (hx : s + x < e) (he : e ≤ a.size) :
    (a.extract s e)[x]! = a[s + x]! := by
  have h1 : x < (a.extract s e).size := by rw [Array.size_extract]; omega
  rw [getElem!_pos (a.extract s e) x h1, getElem!_pos a (s + x) (by omega), Array.getElem_extract]

theorem fCls_spec {i v : ℕ} (h : fCls i v = true) :
    (8192 ≤ i → i < 19112 → v = ap (RG ((i - 8192) / 1365)) ((i - 8192) % 1365)) ∧
      (19112 ≤ i → i < 23207 → v ≤ i - 19112) ∧ (23207 ≤ i → i < 27302 → v < 8) := by
  unfold fCls at h
  simp only [bIf_eq, strictB_eq, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [if_neg (by omega), if_pos h2] at h
    exact Nat.eq_of_beq_eq_true h
  · rw [if_neg (by omega), if_neg (by omega), if_pos h2] at h
    exact Nat.le_of_ble_eq_true h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2] at h
    exact Nat.le_of_ble_eq_true h

theorem rdGens_get {j : ℕ} (hj : j < 8) :
    rdGens[j]! = clsNums.extract (8192 + 1365 * j) (8192 + 1365 * (j + 1)) := by
  unfold rdGens
  simp [getElem!_def, hj]

theorem rdGens_size : rdGens.size = 8 := by
  unfold rdGens
  simp

theorem rdGens_pt {j : ℕ} (hj : j < 8) {x : ℕ} (hx : x < 1365) :
    (rdGens[j]!)[x]! = ap (RG j) x := by
  rw [rdGens_get hj, extract_get _ (by omega) (by rw [cls_size]; omega)]
  have h := (fCls_spec (cls_get (i := 8192 + 1365 * j + x) (by omega))).1 (by omega) (by omega)
  rw [h]
  congr 2
  · omega
  · omega

theorem rdPar_get {k : ℕ} (hk : k < 4095) : rdPar[k]! ≤ k := by
  have h1 : rdPar[k]! = clsNums[19112 + k]! :=
    extract_get _ (by omega) (by rw [cls_size]; omega)
  rw [h1]
  have := (fCls_spec (cls_get (i := 19112 + k) (by omega))).2.1 (by omega) (by omega)
  omega

theorem rdPg_get {k : ℕ} (hk : k < 4095) : rdPg[k]! < 8 := by
  have h1 : rdPg[k]! = clsNums[23207 + k]! :=
    extract_get _ (by omega) (by rw [cls_size]; omega)
  rw [h1]
  exact (fCls_spec (cls_get (i := 23207 + k) (by omega))).2.2 (by omega) (by omega)

theorem rdPar_size : rdPar.size = 4095 := by
  unfold rdPar
  simp [cls_size]

@[expose] noncomputable def gR (j : ℕ) : Pm := permOfArr 1365 (unpack 1365 11 (RG j))

theorem ptRG {j : ℕ} (hj : j < 8) : PtRep (RG j) (gR j) :=
  (rep_of_invEqK (CFSG.KC.Pack.allN_spec kInv j hj)).2.1

theorem land7_lt (l : ℕ) : Nat.land l 7 < 8 := by
  change l &&& (2 ^ 3 - 1) < 8
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

@[expose] noncomputable def gRl (l : ℕ) : Pm := gR (Nat.land l 7)

theorem ptT (l : ℕ) : PtRep (gT l) (gRl l) := ptRG (land7_lt l)

theorem rep_of_pt {t : Array ℕ} {P : ℕ} {g : Pm} (ht : ∀ x < 1365, t[x]! = ap P x)
    (hP : PtRep P g) : Rep 1365 t g := fun x => by rw [ht x x.2, hP]

theorem isInvA_of_rep {t r : Array ℕ} {g : Pm} (ht : Rep 1365 t g) (hr : Rep 1365 r g⁻¹) :
    isInvA 1365 t r = true := by
  rw [isInvA, allLt_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem rep_rdGens {j : ℕ} (hj : j < 8) : Rep 1365 rdGens[j]! (gR j) :=
  rep_of_pt (fun _ hx => rdGens_pt hj hx) (ptRG hj)

theorem perm_rdGens {j : ℕ} (hj : j < 8) : permOfArr 1365 rdGens[j]! = gR j := by
  have hinv := (rep_of_invEqK (CFSG.KC.Pack.allN_spec kInv j hj)).2.2
  have hr : Rep 1365 (unpack 1365 11 (RGI j)) (gR j)⁻¹ := fun x => by
    rw [← ap_eq_unpack _ x.2]
    exact hinv x
  exact Rep.unique (rep_permOfArr (isInvA_of_rep (rep_rdGens hj) hr)).1 (rep_rdGens hj)

theorem la_len : (CFSG.KC.Co1BPair.numsOf LT.chars).length = 19108 := (scanK_sound kTextL).2.1

theorem la_size : laNums.size = 19108 := by
  rw [la_eq, List.size_toArray, la_len]

theorem la_get {i : ℕ} (hi : i < 19108) : fLa i (laNums[i]!) = true := by
  have h := (scanK_sound kTextL).2.2 i hi
  rw [la_eq]
  have hi' : i < (CFSG.KC.Co1BPair.numsOf LT.chars).length := by rw [la_len]; exact hi
  simpa [getElem!_def, List.getD_eq_getElem?_getD, hi'] using h

theorem fLa_spec {i v : ℕ} (h : fLa i v = true) :
    (1365 ≤ i → i < 5459 → v ≤ i - 1365 ∧ v = t12 PLa (i - 1365)) ∧
      (5459 ≤ i → i < 9553 → v < 2 ∧ v = t12 GLa (i - 5459)) := by
  unfold fLa at h
  simp only [bIf_eq, strictB_eq, Nat.blt_eq] at h
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [if_neg (by omega), if_pos h2] at h
    split_ifs at h with hh
    exact ⟨Nat.le_of_ble_eq_true hh, Nat.eq_of_beq_eq_true h⟩
  · rw [if_neg (by omega), if_neg (by omega), if_pos h2] at h
    split_ifs at h with hh
    exact ⟨hh, Nat.eq_of_beq_eq_true h⟩

theorem laPar_get {k : ℕ} (hk : k < 4094) : laPar[k]! ≤ k ∧ laPar[k]! = t12 PLa k := by
  have h1 : laPar[k]! = laNums[1365 + k]! :=
    extract_get _ (by omega) (by rw [la_size]; omega)
  rw [h1]
  have := (fLa_spec (la_get (i := 1365 + k) (by omega))).1 (by omega) (by omega)
  rw [show 1365 + k - 1365 = k by omega] at this
  exact this

theorem laPg_get {k : ℕ} (hk : k < 4094) : laPg[k]! < 2 ∧ laPg[k]! = t12 GLa k := by
  have h1 : laPg[k]! = laNums[1365 + 4094 + k]! :=
    extract_get _ (by omega) (by rw [la_size]; omega)
  rw [h1]
  have := (fLa_spec (la_get (i := 1365 + 4094 + k) (by omega))).2 (by omega) (by omega)
  rw [show 1365 + 4094 + k - 5459 = k by omega] at this
  exact this

theorem laPar_size : laPar.size = 4094 := by
  unfold laPar
  simp [la_size]

theorem laList_size : laList.size = 4095 := by
  change (buildList tAa laPar (conjOp laPg)).size = 4095
  rw [buildList_size, laPar_size]

theorem walkK_succ (PAR : ℕ → ℕ) (f m : ℕ) :
    walkK PAR (f + 1) (m + 1) = walkK PAR f (t12 PAR m) := by
  change strictN (t12 PAR (Nat.sub (m + 1) 1)) (walkK PAR f) = _
  rw [CFSG.KC.Pack.strictN_eq]
  rfl

section Main


theorem gxy_gGen {g : ℕ} (hg : g < 2) : gxy g = gGen 1 g := by
  unfold gxy
  congr 1
  change g &&& 1 = g
  rw [Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt hg

theorem la_rep {tA : Pm} (htA : Rep 1365 tAa tA) :
    ∀ f node, node < 4095 → walkK PLa f node = 0 →
      Rep 1365 laList[node]! (treeE gxy PLa GLa f node * tA * (treeE gxy PLa GLa f node)⁻¹)
  | 0, node, _, hw => by
    have h0 : node = 0 := hw
    subst h0
    change Rep 1365 (buildList tAa laPar (conjOp laPg))[0]! _
    rw [buildList_zero, treeE_zero]
    simpa using htA
  | f + 1, 0, _, _ => by
    change Rep 1365 (buildList tAa laPar (conjOp laPg))[0]! _
    rw [buildList_zero, treeE_zero]
    simpa using htA
  | f + 1, m + 1, hn, hw => by
    rw [walkK_succ] at hw
    obtain ⟨hpk, hpe⟩ := laPar_get (k := m) (by omega)
    obtain ⟨hgk, hge⟩ := laPg_get (k := m) (by omega)
    have ih := la_rep htA f (t12 PLa m) (by omega) hw
    change Rep 1365 (buildList tAa laPar (conjOp laPg))[m + 1]! _
    rw [buildList_succ tAa laPar (conjOp laPg) (by rw [laPar_size]; omega) hpk]
    change Rep 1365 (conjA gA[laPg[m]!]! gAi[laPg[m]!]! laList[laPar[m]!]!) _
    have hg := hg2 xa_inv ya_inv 1 _ hgk
    rw [hpe] at ⊢
    have h := rep_conjA hg.1 hg.2 ih
    have e : treeE gxy PLa GLa (f + 1) (m + 1) = gGen 1 laPg[m]! * treeE gxy PLa GLa f (t12 PLa m) := by
      change gxy (t12 GLa m) * _ = _
      rw [← hge, gxy_gGen hgk]
    rw [e]
    have e2 : gGen 1 laPg[m]! * treeE gxy PLa GLa f (t12 PLa m) * tA *
        (gGen 1 laPg[m]! * treeE gxy PLa GLa f (t12 PLa m))⁻¹ =
        gGen 1 laPg[m]! * (treeE gxy PLa GLa f (t12 PLa m) * tA *
          (treeE gxy PLa GLa f (t12 PLa m))⁻¹) * (gGen 1 laPg[m]!)⁻¹ := by group
    rw [e2]
    exact h

theorem keyE_eq_of_pts {g h : Pm} (hp : ∀ x : Fin 1365, (x : ℕ) < 3 → g x = h x) :
    keyE g = keyE h := by
  unfold keyE
  rw [hp 0 (by decide), hp 1 (by decide), hp 2 (by decide)]

theorem comm_of_commB {a b : ℕ} {A B : Pm} (hA : PtRep a A) (hB : PtRep b B) (hAD : A ∈ twoBD)
    (hBD : B ∈ twoBD) (h : commB a b = true) : A * B = B * A := by
  refine twoBD_eq_of_keyE (mul_mem hAD hBD) (mul_mem hBD hAD) (keyE_eq_of_pts fun x hx => ?_)
  have h1 := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec h x hx)
  rw [hB x, hA (B x), hA x, hB (A x)] at h1
  exact Fin.ext h1

theorem wordE_mem {a b : Pm} (ha : a ∈ twoBD) (hb : b ∈ twoBD) (W : ℕ) :
    ∀ L, wordE a b W L ∈ twoBD
  | 0 => one_mem _
  | L + 1 => by
    refine mul_mem ?_ (wordE_mem ha hb W L)
    split_ifs
    · exact ha
    · exact hb

theorem mem_of_sift {P : ℕ} {g : Pm} (hP : Rep 1365 (unpack 1365 11 P) g)
    (hc : canonK 1365 11 (mask 11) (1365 * 11) P = true)
    (hs : siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0 P = true) :
    g ∈ twoBD := by
  refine mem_of_inD hP ?_
  unfold inD twoBLevels
  exact siftK_sound hb kP LC.hl rfl (range_of_canonK hc) hs

theorem fact2 : (251596800 : ℕ).factorization 2 = 12 := by
  have h : (251596800 : ℕ) = 2 ^ 12 * 61425 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 61425)]
  simp

theorem main_facts :
    ∃ tA : Pm, Rep 1365 tAa tA ∧ tA ∈ twoBD ∧ tA * tA = 1 ∧ tA ≠ 1 ∧
      (∀ i < laList.size, ∃ d ∈ twoBD, Rep 1365 laList[i]! (d * tA * d⁻¹)) ∧
      (∀ z, (∃ d ∈ twoBD, z = d * tA * d⁻¹) → ∃ i < laList.size, Rep 1365 laList[i]! z) ∧
      laList.size = 4095 ∧
      4096 ≤ {z | ∃ d ∈ twoBD, z = d * xBar * d⁻¹}.ncard ∧
      (∀ z ∈ twoBD, z * z = 1 → z ≠ 1 →
        (∃ d ∈ twoBD, d * z * d⁻¹ = tA) ∨ ∃ d ∈ twoBD, d * z * d⁻¹ = xBar) ∧
      rdGens.size = 8 ∧ (∀ j < 8, Rep 1365 rdGens[j]! (permOfArr 1365 rdGens[j]!)) ∧
      Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}) ≤ twoBD ∧
      Nat.card (Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8})) = 4096 ∧
      ∀ i < rdList.size, ∃ w ∈ Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}),
        Rep 1365 rdList[i]! w := by
  classical
  have hid := CertificateChecks.KernelCo1B.Tri2045.idA_eq
  have kCan' := kCan
  have kSift' := kSift
  have kOrd' := kOrd
  have kCent' := kCent
  have kInvS' := kInvS
  simp only [Bool.and_eq_true] at kCan' kSift' kOrd' kCent' kInvS'
  have ptX : PtRep (LC.S 0) xBar := by
    have := ptLC (j := 0) (by norm_num)
    simpa [gGen] using this
  have ptYi : PtRep (LC.SI 1) yBar⁻¹ := by
    have h1 := ptLC (j := 1) (by norm_num)
    have e : gGen 1 1 = yBar := by simp [gGen]
    rw [e] at h1
    refine ptRep_inv h1 fun i hi => ?_
    have h := CFSG.KC.EnumSound.permOK_sound (n := 1365) (w := 11)
      (CFSG.KC.Pack.allN_spec kP 1 (by norm_num))
    rw [ap_eq_pg, ap_eq_pg]
    exact (h.2.2 i hi).2
  have hxD : xBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyD : yBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨repT, ptTA, -⟩ := rep_of_invEqK kInvS'.1.1
  set tA := permOfArr 1365 (unpack 1365 11 (PK 6)) with htAdef
  have htA : Rep 1365 tAa tA := by
    rw [tA_eq]
    exact repT
  have htAD : tA ∈ twoBD := mem_of_sift repT
    (CFSG.KC.Pack.allN_spec Tri27206.kCan 6 (by norm_num)) kSift'.2
  have hord2 : orderOf tA = 2 :=
    ((ordIs_iff repT 2).1 (ordIs_of hid (CFSG.KC.Pack.allN_spec Tri27206.kCan 6 (by norm_num))
      (by norm_num) kOrd'.2)).2
  have htAsq : tA * tA = 1 := by
    rw [← pow_two, ← hord2, pow_orderOf_eq_one]
  have htA1 : tA ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord2
    omega
  have hγD : ∀ j < 8, gR j ∈ twoBD := fun j hj =>
    mem_of_sift (rep_of_invEqK (CFSG.KC.Pack.allN_spec kInv j hj)).1
      (CFSG.KC.Pack.allN_spec kCan'.1 j hj) (CFSG.KC.Pack.allN_spec kSift'.1.1 j hj)
  have hTeq : Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}) =
      Subgroup.closure (gR '' Set.Iio 8) := by
    have hset : (fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8} = gR '' Set.Iio 8 :=
      Set.image_congr fun j hj => perm_rdGens hj
    rw [hset]
  set T := Subgroup.closure (gR '' Set.Iio 8) with hTdef
  have hTD : T ≤ twoBD := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hγD j hj
  have hgRl : ∀ l, gRl l ∈ T := fun l =>
    Subgroup.subset_closure ⟨_, land7_lt l, rfl⟩
  let e : ℕ → Pm := treeE gRl TP TG 8
  have heT : ∀ k, e k ∈ T := fun k => treeE_mem hgRl TP TG 8 k
  have hkey : ∀ k < 4096, keyT k = keyE (e k) := treeK_spec ptT kTree
  have hTtree := closure_eq_of_tree (γ := gR) (J := 8) (n := 4096) (e := e)
    (fun k _ => heT k) (by norm_num) (treeE_zero _ _ _ _)
    (fun i hi j hj => by
      obtain ⟨hc, hK⟩ := closK_spec kClos i hi j hj
      refine ⟨_, hc, twoBD_eq_of_keyE (hTD (heT _)) (mul_mem (hγD j hj) (hTD (heT i))) ?_⟩
      rw [← hkey _ hc, hK, hkey i hi, kmap_keyE (ptT j)]
      have : gRl j = gR j := by
        unfold gRl
        congr 1
        change j &&& (2 ^ 3 - 1) = j
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_eq_of_lt hj
      rw [this])
    (fun i hi j hj h => sortedK_injOn kInc i hi j hj (by rw [hkey i hi, hkey j hj, h]))
  have hTcard : Nat.card T = 4096 := hTtree.2
  let K := twoBD ⊓ Subgroup.centralizer {tA}
  have hKmem : ∀ g : Pm, g ∈ twoBD → g * tA = tA * g → g ∈ K := fun g hg hc =>
    ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hc.symm⟩
  have hTK : T ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hKmem _ (hγD j hj) (comm_of_commB (ptRG hj) ptTA (hγD j hj) htAD
      (CFSG.KC.Pack.allN_spec kCent'.1 j hj))
  have hc35 : ∀ i < 2, ∀ Q : ℕ, invEqK 1365 11 (mask 11) (1365 * 11) (C35 i) Q = true →
      ∀ v, 0 < v → ordAuxK (C35 i) (v - 1) (C35 i) = true → ∃ c : Pm, c ∈ K ∧ orderOf c = v := by
    intro i hi Q hinv v hv hord
    obtain ⟨repC, ptC, -⟩ := rep_of_invEqK hinv
    have hcan := CFSG.KC.Pack.allN_spec kCan'.2 i hi
    have hCD := mem_of_sift repC hcan (CFSG.KC.Pack.allN_spec kSift'.1.2 i hi)
    exact ⟨_, hKmem _ hCD (comm_of_commB ptC ptTA hCD htAD
      (CFSG.KC.Pack.allN_spec kCent'.2 i hi)), ((ordIs_iff repC v).1 (ordIs_of hid hcan hv hord)).2⟩
  obtain ⟨c3, hc3K, hc3⟩ := hc35 0 (by norm_num) _ kInvS'.1.2 3 (by norm_num) kOrd'.1.1
  obtain ⟨c5, hc5K, hc5⟩ := hc35 1 (by norm_num) _ kInvS'.2 5 (by norm_num) kOrd'.1.2
  have hdvd : 61440 ∣ Nat.card K := by
    have h1 : 4096 ∣ Nat.card K := hTcard ▸ Subgroup.card_dvd_of_le hTK
    have h2 : 3 ∣ Nat.card K := (show orderOf c3 = 3 from hc3) ▸ Subgroup.orderOf_dvd_natCard K hc3K
    have h3 : 5 ∣ Nat.card K := (show orderOf c5 = 5 from hc5) ▸ Subgroup.orderOf_dvd_natCard K hc5K
    have h12 : 4096 * 3 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (4096 * 3) 5) h12 h3
    simpa using this
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hK61440 : 61440 ≤ Nat.card K := Nat.le_of_dvd hKpos hdvd
  have hcls := ncard_conj_mul_le twoBD htAD (K := K) inf_le_left fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hk.2 tA rfl).symm
  rw [card_twoBD] at hcls
  have hcls4095 : {z : Pm | ∃ d ∈ twoBD, z = d * tA * d⁻¹}.ncard ≤ 4095 := by
    have h1 := Nat.mul_le_mul_left {z : Pm | ∃ d ∈ twoBD, z = d * tA * d⁻¹}.ncard hK61440
    have h2 := le_trans h1 hcls
    omega
  let cL : ℕ → Pm := treeE gxy PLa GLa 24
  have hcLD : ∀ k, cL k ∈ twoBD := fun k => treeE_mem gxy_mem PLa GLa 24 k
  have hroot : ∀ k < 4095, walkK PLa 24 k = 0 := fun k hk =>
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kRoot k hk)
  have hlaRep : ∀ k < 4095, Rep 1365 laList[k]! (cL k * tA * (cL k)⁻¹) := fun k hk =>
    la_rep htA 24 k hk (hroot k hk)
  have hlaKey : ∀ k, keyLa k = keyE (cL k * tA * (cL k)⁻¹) := fun k =>
    keyK_eq ptS ptSI ptTA PLa GLa 24 k
  have hclass := eq_image_of_ncard_le (Set.toFinite _) hcls4095
    (f := fun k => cL k * tA * (cL k)⁻¹) (fun k _ => ⟨cL k, hcLD k, rfl⟩)
    (fun i hi j hj h => sortedK_injOn kLa i hi j hj (by
      rw [hlaKey i, hlaKey j]
      exact congrArg keyE h))
  let cB : ℕ → Pm := treeE gxy PLb GLb 19
  have hlb : 4096 ≤ {z : Pm | ∃ d ∈ twoBD, z = d * xBar * d⁻¹}.ncard :=
    le_ncard_of_inj (Set.toFinite _) (f := fun k => cB k * xBar * (cB k)⁻¹)
      (fun k _ => ⟨cB k, treeE_mem gxy_mem PLb GLb 19 k, rfl⟩)
      (fun i hi j hj h => sortedK_injOn kLb i hi j hj (by
        change keyK xyS xySI PLb GLb 19 (LC.S 0) i = keyK xyS xySI PLb GLb 19 (LC.S 0) j
        rw [keyK_eq ptS ptSI ptX, keyK_eq ptS ptSI ptX]
        exact congrArg keyE h))
  have hfusT : ∀ z ∈ T, z * z = 1 → z ≠ 1 →
      (∃ d ∈ twoBD, d * z * d⁻¹ = tA) ∨ ∃ d ∈ twoBD, d * z * d⁻¹ = xBar := by
    intro z hz hzsq hz1
    have hz' : z ∈ (T : Set Pm) := hz
    rw [hTtree.1] at hz'
    obtain ⟨k, hk, rfl⟩ := hz'
    have hk' : k < 4096 := hk
    have hzD : e k ∈ twoBD := hTD (heT k)
    have hrec := recK_spec (CFSG.KC.Pack.allN_spec kRec k hk')
    rw [hkey k hk'] at hrec
    rcases hrec with ⟨-, hb, hcase⟩ | ⟨-, -, hall⟩
    · exfalso
      rcases hcase with h0 | hne
      · exact hz1 (by rw [h0]; exact treeE_zero _ _ _ _)
      · apply hne
        rw [kpt_keyE _ hb, downK_eq ptT]
        rw [← Equiv.Perm.mul_apply, hzsq]
        rfl
    · set W := Nat.shiftRight (REC k) 10
      set L := Nat.land (Nat.shiftRight (REC k) 2) 255
      let w := wordE xBar yBar⁻¹ W L
      have hwD : w ∈ twoBD := wordE_mem hxD (inv_mem hyD) W L
      have hpts : ∀ R : ℕ, ∀ r : Pm, PtRep R r → r ∈ twoBD →
          (∀ b < 3, CFSG.KC.G24Key.wpt (LC.S 0) (LC.SI 1) W L (kpt (keyE (e k)) b) =
            ap R (CFSG.KC.G24Key.wpt (LC.S 0) (LC.SI 1) W L b)) → w * e k * w⁻¹ = r := by
        intro R r hR hrD hb
        have heq : w * e k = r * w := twoBD_eq_of_keyE (mul_mem hwD hzD) (mul_mem hrD hwD)
          (keyE_eq_of_pts fun x hx => by
            have h := hb x hx
            rw [kpt_keyE _ hx, wpt_eq ptX ptYi] at h
            have e1 : (⟨(x : ℕ), by omega⟩ : Fin 1365) = x := rfl
            rw [e1, wpt_eq ptX ptYi, hR] at h
            exact Fin.ext h)
        rw [heq, mul_inv_cancel_right]
      by_cases hR : Nat.land (Nat.shiftRight (REC k) 1) 1 = 0
      · left
        refine ⟨w, hwD, hpts (PK 6) tA ptTA htAD fun b hb => ?_⟩
        have := (hall b hb).2
        rw [if_pos hR] at this
        exact this
      · right
        refine ⟨w, hwD, hpts (LC.S 0) xBar ptX hxD fun b hb => ?_⟩
        have := (hall b hb).2
        rw [if_neg hR] at this
        exact this
  have hfus := fusion_of_sylow hTD (by rw [hTcard, card_twoBD, fact2]; norm_num) hfusT
  have hrdgen := rmulList_gen (γ := gR) (gs := rdGens)
    (fun j hj => by rw [rdGens_size] at hj; exact rep_rdGens hj)
    (par := rdPar) (pg := rdPg) (fun k hk => rdPar_get (by rw [rdPar_size] at hk; exact hk))
    (fun k hk => by rw [rdGens_size]; exact rdPg_get (by rw [rdPar_size] at hk; exact hk))
  refine ⟨tA, htA, htAD, htAsq, htA1, fun i hi => ?_, fun z hz => ?_, laList_size, hlb, hfus,
    rdGens_size, fun j hj => by rw [perm_rdGens hj]; exact rep_rdGens hj, ?_, ?_, fun i hi => ?_⟩
  · rw [laList_size] at hi
    exact ⟨cL i, hcLD i, hlaRep i hi⟩
  · obtain ⟨i, hi, e'⟩ := hclass z hz
    refine ⟨i, by rw [laList_size]; exact hi, ?_⟩
    rw [← e']
    exact hlaRep i hi
  · rw [hTeq]
    exact hTD
  · rw [hTeq]
    exact hTcard
  · rw [hTeq]
    obtain ⟨w, hw, hrep⟩ := hrdgen i hi
    refine ⟨w, ?_, hrep⟩
    have hs : gR '' {j | j < rdGens.size} = gR '' Set.Iio 8 := by
      rw [rdGens_size]
      rfl
    rw [hs] at hw
    exact hw

theorem classes_ok : ∃ tA : Equiv.Perm (Fin 1365), Rep 1365 tAa tA ∧
    tA ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧ tA * tA = 1 ∧ tA ≠ 1 ∧
    (∀ i < laList.size, ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
      Rep 1365 laList[i]! (d * tA * d⁻¹)) ∧
    (∀ z, (∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, z = d * tA * d⁻¹) →
      ∃ i < laList.size, Rep 1365 laList[i]! z) ∧
    laList.size = 4095 ∧
    4096 ≤ {z | ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
      z = d * permOfArr 1365 xa * d⁻¹}.ncard ∧
    (∀ z ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, z * z = 1 → z ≠ 1 →
      (∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, d * z * d⁻¹ = tA) ∨
        ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
          d * z * d⁻¹ = permOfArr 1365 xa) ∧
    rdGens.size = 8 ∧ (∀ j < 8, Rep 1365 rdGens[j]! (permOfArr 1365 rdGens[j]!)) ∧
    Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}) ≤
      Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
    Nat.card (Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8})) = 4096 ∧
    ∀ i < rdList.size, ∃ w ∈ Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}),
      Rep 1365 rdList[i]! w := by
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY]
  exact main_facts

end Main

end CertificateChecks.KernelG24.Cls27203

end
