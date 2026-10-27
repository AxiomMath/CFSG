
module

public import Certificates.Kernel.SporSch.HN.ArrStrong
public import Certificates.Kernel.SporSch.HN.Intr2098K
public import CFSG.Sporadic.HNSchreier.IntrinsicCheckInputs
public import CFSG.Certificates.Kernel.SporSch.HNF5RankSound
public import CFSG.Certificates.Kernel.SporSch.HNNat
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.HNF5KronSound
import CFSG.Certificates.Kernel.PackSetSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNIntr

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.He CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CFSG.KS.TW CFSG.KS Matrix

theorem entK {K : ℕ} (hK : K < 137) : Canon5 (sc K) ∧
    (HNC.OP K = 0 → Canon5 (sc (HNC.L K)) → Canon5 (sc (HNC.R K)) →
      ∀ i < 133, vm5 (sc (HNC.R K)) (sc (HNC.L K) i) = sc K i) ∧
    (HNC.OP K = 1 → ∀ i < 133, sc (HNC.L K) i = sc K i) := by
  rcases (by omega : K < 36 ∨ (36 ≤ K ∧ K < 46) ∨ (46 ≤ K ∧ K < 56) ∨ (56 ≤ K ∧ K < 66) ∨
      (66 ≤ K ∧ K < 76) ∨ (76 ≤ K ∧ K < 86) ∨ (86 ≤ K ∧ K < 96) ∨ (96 ≤ K ∧ K < 106) ∨
      (106 ≤ K ∧ K < 116) ∨ (116 ≤ K ∧ K < 126) ∨ 126 ≤ K) with
    h | h | h | h | h | h | h | h | h | h | h
  · exact F5Kron.krBlk_sound blk0 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk1 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk2 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk3 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk4 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk5 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk6 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk7 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk8 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk9 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk10 (by omega) (by omega)

theorem canon (k : ℕ) (hk : k < 137) : Canon5 (sc k) := (entK hk).1

theorem mulC {K l r : ℕ} (hK : K < 137) (ho : HNC.OP K = 0) (hl : HNC.L K = l)
    (hr : HNC.R K = r) : ∀ i < 133, vm5 (sc r) (sc l i) = sc K i := by
  subst hl hr
  have hs := CFSG.KC.Pack.allN_spec specLt K hK
  rw [CFSG.KC.Pack.band_iff, Nat.blt_eq, Nat.blt_eq] at hs
  exact (entK hK).2.1 ho (canon _ hs.1) (canon _ hs.2)

theorem copyC {K l : ℕ} (hK : K < 137) (ho : HNC.OP K = 1) (hl : HNC.L K = l) :
    ∀ i < 133, sc l i = sc K i := by
  subst hl
  exact (entK hK).2.2 ho

theorem rows_eq {X T : ℕ → ℕ} (h : allN 133 (fun i => Nat.beq (X i) (T i)) = true) :
    rows5 X = rows5 T :=
  rows5_congr fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem mul_eq {K l r : ℕ} (hl1 : l < 137) (hr1 : r < 137) (hK : K < 137) (ho : HNC.OP K = 0)
    (hl : HNC.L K = l) (hr : HNC.R K = r) :
    mulM 5 133 (rows5 (sc l)) (rows5 (sc r)) = rows5 (sc K) :=
  mulM5_sound (canon l hl1) (canon r hr1) (mulC hK ho hl hr)

theorem sc_strong {j : ℕ} (hj : j < 34) : rows5 (sc j) = rows5 (HNStrong.ss (13 + j)) :=
  rows5_congr fun i hi => by
    have := allN_spec (allN_spec eqS j hj) i hi
    rw [Nat.add_eq] at this
    exact Nat.eq_of_beq_eq_true this

theorem mletter_sc {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 17) :
    mletter HNStrong.SA HNStrong.SIA l = rows5 (sc (letE l)) := by
  unfold mletter letE
  split_ifs with hp
  · rw [SA_get (by omega), HNStrong.F, sc_strong (by omega)]
  · rw [SIA_get (by omega), HNStrong.FI, sc_strong (by omega),
      show 13 + (16 + (-l).toNat) = 30 + ((-l).toNat - 1) by omega]

theorem seed_sc {l : ℕ} (hl : l = 1 ∨ l = 2) :
    seedSel rowsA rowsB l = rows5 (sc (seedE l)) := by
  rcases hl with rfl | rfl
  · rw [seedSel, ite_eq_left rfl, HNStrong.rowsA_eq, seedE, ite_eq_left rfl, rows_eq eqA]
  · rw [seedSel, ite_eq_right (by decide), ite_eq_left rfl, HNStrong.rowsB_eq, seedE,
      ite_eq_right (by decide), rows_eq eqB]

@[expose] noncomputable def seedChainOK (w : List ℕ) (o : ℕ) : Bool :=
  decide (1 ≤ w.length) && HNC.OP o == 1 && HNC.L o == seedE (w.headD 0) &&
    (List.range (w.length - 1)).all fun t => HNC.OP (o + t + 1) == 0 && HNC.L (o + t + 1) == o + t &&
      HNC.R (o + t + 1) == seedE (w.getD (t + 1) 0)

theorem chS_ok : chainOK HNC.OP HNC.L HNC.R letE 137 FAData.sWords[0]! chS = true := by quickRfl
theorem chH0_ok : chainOK HNC.OP HNC.L HNC.R letE 137 IntrinsicData.wHWord[0]! (chH 0) = true := by
  quickRfl
theorem chH1_ok : chainOK HNC.OP HNC.L HNC.R letE 137 IntrinsicData.wHWord[1]! (chH 1) = true := by
  quickRfl
theorem chU0_ok : seedChainOK IntrinsicData.wRoot[0]! (chU 0) = true := by quickRfl
theorem chU1_ok : seedChainOK IntrinsicData.wRoot[1]! (chU 1) = true := by quickRfl

theorem letters_S : ∀ l ∈ FAData.sWords[0]!, l ≠ 0 ∧ l.natAbs ≤ 17 := by decide
theorem letters_H : ∀ c < 2, ∀ l ∈ IntrinsicData.wHWord[c]!, l ≠ 0 ∧ l.natAbs ≤ 17 := by decide
theorem letters_U : ∀ c < 2, ∀ l ∈ IntrinsicData.wRoot[c]!, l = 1 ∨ l = 2 := by decide

theorem lens : FAData.sWords[0]!.length = 10 ∧ IntrinsicData.wHWord[0]!.length = 13 ∧
    IntrinsicData.wHWord[1]!.length = 12 ∧ IntrinsicData.wRoot[0]!.length = 41 ∧
    IntrinsicData.wRoot[1]!.length = 21 := by decide

theorem strong_chain {w : List ℤ} {o : ℕ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17)
    (h : chainOK HNC.OP HNC.L HNC.R letE 137 w o = true) :
    mword HNStrong.SA HNStrong.SIA w = rows5 (sc (o + w.length - 1)) := by
  simp only [CFSG.KS.SporSch.chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, hlen⟩, hl⟩, ho⟩, hL⟩, hs⟩ := h
  have hlt : ∀ t < w.length, mletter HNStrong.SA HNStrong.SIA (w.getD t 0) =
      rows5 (sc (letE (w.getD t 0))) ∧ letE (w.getD t 0) < 137 := fun t ht => by
    have hm : w.getD t 0 ∈ w := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    exact ⟨mletter_sc (hw _ hm), hl _ hm⟩
  have key : ∀ t, t < w.length →
      mword HNStrong.SA HNStrong.SIA (w.drop (w.length - 1 - t)) = rows5 (sc (o + t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have e : w.drop (w.length - 1 - 0) = [w.getD (w.length - 1) 0] := by
        rw [Nat.sub_zero, List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
          List.getD_eq_getElem _ _ (by omega)]
      rw [e, mword_one, (hlt _ (by omega)).1, mulM5_idR (canon _ (hlt _ (by omega)).2),
        Nat.add_zero]
      exact rows5_congr fun i hi => copyC (by omega) ho hL i hi
    | succ t ih =>
      intro ht
      obtain ⟨⟨a, b⟩, c⟩ := hs t (by omega)
      have e : w.drop (w.length - 1 - (t + 1)) =
          w.getD (w.length - 2 - t) 0 :: w.drop (w.length - 1 - t) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
        congr 2 <;> omega
      rw [e, mword, ih (by omega), (hlt _ (by omega)).1,
        mulM5_sound (canon _ (hlt _ (by omega)).2) (canon _ (by omega)) (mulC (by omega) a b c)]
      rfl
  have := key (w.length - 1) (by omega)
  rwa [show w.length - 1 - (w.length - 1) = 0 by omega, List.drop_zero,
    show o + (w.length - 1) = o + w.length - 1 by omega] at this

theorem seed_chain {w : List ℕ} {o : ℕ} (hw : ∀ l ∈ w, l = 1 ∨ l = 2) (hlt : o + w.length ≤ 137)
    (h : seedChainOK w o = true) :
    wordM (seedSel rowsA rowsB) w = rows5 (sc (o + w.length - 1)) := by
  simp only [seedChainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨h1, ho⟩, hl⟩, hs⟩ := h
  have hcan : ∀ l ∈ w, seedE l < 137 := fun l hl' => by
    rcases hw l hl' with rfl | rfl <;> decide
  refine wordM5_chain (LT := fun l => sc (seedE l)) (Q := fun t => sc (o + t - 1)) h1
    (fun l hl' => seed_sc (hw l hl')) (fun l hl' => canon _ (hcan l hl'))
    (fun t ht1 ht => canon _ (by omega)) (fun i hi => ?_) (fun t ht1 ht i hi => ?_)
  · rw [show o + 1 - 1 = o by omega]
    exact (copyC (by omega) ho hl i hi).symm
  · obtain ⟨⟨a, b⟩, c⟩ := hs (t - 1) (by omega)
    rw [show o + (t - 1) + 1 = o + t by omega] at a b c
    rw [show t - 1 + 1 = t by omega] at c
    rw [show o + (t + 1) - 1 = o + t by omega, show o + t - 1 = o + (t - 1) by omega]
    exact mulC (by omega) a b c i hi

noncomputable abbrev s1J : JH := wJ sL FAData.sWords[0]!

noncomputable abbrev hcJ (c : ℕ) : JH := wJ sL IntrinsicData.wHWord[c]!

noncomputable abbrev ucJ (c : ℕ) : JH := seedJ IntrinsicData.wRoot[c]!

theorem mat_strongWord {w : List ℤ}
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) :
    matJ (wJ sL w) = toMat 5 133 (mword HNStrong.SA HNStrong.SIA w) := by
  refine (mword_mat (m := 17) (fun j hj => ?_) w hw).symm
  rw [SA_get hj, SIA_get hj]
  exact ⟨(mat_sL j hj).1.symm, (mat_sL j hj).2.symm⟩

theorem conj_mat {c : ℕ} (hc : c < 2) :
    matJ (s1J * ucJ c) = matJ (ucJ c * hcJ c) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lens
  obtain ⟨p0, p1, p2, p3, p4, -⟩ := pos_eq
  obtain ⟨a0, a1, a2, b0, b1, b2, c0, c1, c2, d0, d1, d2⟩ := prod_spec
  rw [matJ_mul, matJ_mul, mat_strongWord letters_S, mat_strongWord (letters_H c hc),
    seedJ_mat _ (letters_U c hc), strong_chain letters_S chS_ok, ← toMat_mulM, ← toMat_mulM, l1, p0]
  interval_cases c
  · rw [strong_chain (letters_H 0 (by omega)) chH0_ok,
      seed_chain (letters_U 0 (by omega)) (by rw [l4, p3]; decide) chU0_ok, l2, l4, p1, p3]
    change toMat 5 133 (mulM 5 133 (rows5 (sc 45)) (rows5 (sc 111))) =
      toMat 5 133 (mulM 5 133 (rows5 (sc 111)) (rows5 (sc 58)))
    rw [mul_eq (by decide) (by decide) (by decide) a0 a1 a2,
      mul_eq (by decide) (by decide) (by decide) b0 b1 b2, rows_eq eqXY0]
  · rw [strong_chain (letters_H 1 (by omega)) chH1_ok,
      seed_chain (letters_U 1 (by omega)) (by rw [l5, p4]; decide) chU1_ok, l3, l5, p2, p4]
    change toMat 5 133 (mulM 5 133 (rows5 (sc 45)) (rows5 (sc 132))) =
      toMat 5 133 (mulM 5 133 (rows5 (sc 132)) (rows5 (sc 70)))
    rw [mul_eq (by decide) (by decide) (by decide) c0 c1 c2,
      mul_eq (by decide) (by decide) (by decide) d0 d1 d2, rows_eq eqXY1]

theorem conj_J {c : ℕ} (hc : c < 2) :
    (ucJ c)⁻¹ * s1J * ucJ c = hcJ c := by
  rw [mul_assoc, matJ_injective (conj_mat hc), ← mul_assoc, inv_mul_cancel, one_mul]

theorem seedWordInvIdx_gi :
    ∀ (w : List ℕ) {y : ℕ}, y < nPts →
      seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) w y = gi (seedJ w)⁻¹ y
  | [], _, hy => by rw [seedJ, inv_one]; exact (gi_one hy).symm
  | l :: w, y, hy => by
    have e1 : seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) (l :: w) y =
        seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) w ((if l = 1 then arrJ aJ⁻¹ else arrJ bJ⁻¹)[y]!) :=
      rfl
    have h1 : (if l = 1 then arrJ aJ⁻¹ else arrJ bJ⁻¹)[y]! = gi (if l = 1 then aJ else bJ)⁻¹ y := by
      split_ifs <;> exact arrJ_get _ hy
    have hl : gi (if l = 1 then aJ else bJ)⁻¹ y < nPts := gi_lt _ hy
    rw [e1, h1, seedWordInvIdx_gi w hl, seedJ, _root_.mul_inv_rev, gi_mul _ _ hy]

theorem base_lt : ∀ b ∈ Data.baseList, b < nPts := base_facts.2.2

theorem base_ok {c : ℕ} (hc : c < 2) :
    (Data.baseList.all fun b => seedWordInvIdx (arrJ aJ⁻¹) (arrJ bJ⁻¹) IntrinsicData.wRoot[c]!
      ((arrJ s1J)[seedWordIdx (arrJ aJ) (arrJ bJ) IntrinsicData.wRoot[c]! b]!) ==
        (arrJ (hcJ c))[b]!) = true := by
  rw [List.all_eq_true]
  intro b hb
  have hbl := base_lt b hb
  rw [seedWordIdx_gi _ hbl, arrJ_get _ (gi_lt _ hbl), seedWordInvIdx_gi _ (gi_lt _ (gi_lt _ hbl)),
    arrJ_get _ hbl, ← gi_mul _ _ hbl, ← gi_mul _ _ hbl, ← mul_assoc, conj_J hc]
  exact beq_self_eq_true _

theorem pinvs2 :
    pinvs nPts #[arrJ aJ, arrJ bJ] = #[arrJ aJ⁻¹, arrJ bJ⁻¹] := by
  simp [pinvs, pinvCand_arrJ]

@[expose] def trip (k y : ℕ) : ℕ := if y < 3 * k then (if y % 3 = 2 then y - 2 else y + 1) else y

theorem nat_facts : ∀ c < 2, (natArr IntrinsicData.rho[c]!).size = 12 ∧
    (∀ x < 12, IntrinsicData.wHWord[c]!.foldr (GZ HNNat.natF HNNat.natFI) x =
      (natArr IntrinsicData.wNat[c]!)[x]!) ∧
    (∀ x < 12, (natArr IntrinsicData.rho[c]!)[x]! < 12 ∧
      IntrinsicData.rho[c]!.idxOf ((natArr IntrinsicData.rho[c]!)[x]!) = x) ∧
    (∀ x < 12, IntrinsicData.rho[c]!.idxOf x < 12 ∧
      trip IntrinsicData.wCycles[c]! (IntrinsicData.rho[c]!.idxOf x) < 12 ∧
      (natArr IntrinsicData.rho[c]!)[trip IntrinsicData.wCycles[c]! (IntrinsicData.rho[c]!.idxOf x)]! =
        (natArr IntrinsicData.wNat[c]!)[x]!) := by
  decide +kernel

theorem pinv_rho {c : ℕ} (hc : c < 2) {y : ℕ} (hy : y < 12) :
    (pinvCand 12 (natArr IntrinsicData.rho[c]!))[y]! = IntrinsicData.rho[c]!.idxOf y := by
  obtain ⟨hs, -, hr, -⟩ := nat_facts c hc
  have e : natArr IntrinsicData.rho[c]! = Array.ofFn (n := 12) fun i =>
      (natArr IntrinsicData.rho[c]!)[i.val]! := CFSG.KS.PW.arr_ext hs fun _ _ => rfl
  rw [e]
  exact CFSG.KS.CB.pinvCand_get (T := fun x => (natArr IntrinsicData.rho[c]!)[x]!)
    (U := fun y => IntrinsicData.rho[c]!.idxOf y)
    (fun x hx => (hr x hx).1) (fun x hx => (hr x hx).2) hy

theorem nat_w {c : ℕ} (hc : c < 2) :
    peq 12 (pword 12 HNNat.natS (pinvs 12 HNNat.natS) IntrinsicData.wHWord[c]!)
      (natArr IntrinsicData.wNat[c]!) = true :=
  HNNat.peq_maps fun x hx => by
    rw [HNNat.natWord_pt (letters_H c hc) hx, (nat_facts c hc).2.1 x hx]

theorem nat_inv {c : ℕ} (hc : c < 2) :
    pisInv 12 (natArr IntrinsicData.rho[c]!) (pinvCand 12 (natArr IntrinsicData.rho[c]!)) = true := by
  refine CFSG.ONSchreier.allBelowN_iff.2 fun x hx => ?_
  obtain ⟨-, -, hr, -⟩ := nat_facts c hc
  rw [pinv_rho hc (hr x hx).1, (hr x hx).2]
  simp [(hr x hx).1]

theorem tripleArr_get {k y : ℕ} (hy : y < 12) : (tripleArr k)[y]! = trip k y := by
  rw [tripleArr, getElem!_pos _ y (by simpa using hy), Array.getElem_ofFn]
  rfl

theorem nat_conj {c : ℕ} (hc : c < 2) :
    peq 12 (pcomp 12 (pcomp 12 (natArr IntrinsicData.rho[c]!) (tripleArr IntrinsicData.wCycles[c]!))
      (pinvCand 12 (natArr IntrinsicData.rho[c]!))) (natArr IntrinsicData.wNat[c]!) = true :=
  HNNat.peq_maps fun x hx => by
    obtain ⟨-, -, -, ht⟩ := nat_facts c hc
    obtain ⟨h1, h2, h3⟩ := ht x hx
    rw [CFSG.KS.PW.pcomp_get' hx, pinv_rho hc hx, CFSG.KS.PW.pcomp_get' h1, tripleArr_get h1, h3]

theorem small_ok : IntrinsicData.wRoot.size = 2 ∧ IntrinsicData.wHWord.size = 2 ∧
    IntrinsicData.wNat.size = 2 ∧ IntrinsicData.rho.size = 2 ∧ IntrinsicData.wCycles = #[2, 4] ∧
    ∀ c < 2, (IntrinsicData.wRoot[c]!.all fun l => l == 1 || l == 2) = true ∧
      plettersOK 17 IntrinsicData.wHWord[c]! = true := by decide +kernel

private theorem arr2_get0 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := by
  rw [getElem!_pos _ 0 (by simp)]
  rfl

private theorem arr2_get1 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := by
  rw [getElem!_pos _ 1 (by simp)]
  rfl

theorem intrinsicChecks_arr :
    intrinsicChecks (hnsData.orbit ()) = true := by
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := small_ok
  unfold intrinsicChecks
  try dsimp only
  rw [hns_n, natTab_alpha, natTab_beta, regs_get (k := 1) (by omega), regs_get (k := 2) (by omega),
    hS_eq, pinvs2, pword_arrJ SJ_arrs _ fun l hl => letters_S l hl]
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq]
  refine ⟨by simp, by rw [arr2_get0]; exact pisInv_arrJ _, by rw [arr2_get1]; exact pisInv_arrJ _,
    z1, z2, z3, z4, z5, ?_⟩
  refine CFSG.ONSchreier.allBelowN_iff.2 fun c hc => ?_
  have hp := z6 c hc
  rw [pword_arrJ SJ_arrs _ fun l hl => letters_H c hc l hl]
  simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
  rw [base_ok hc, hp.1, hp.2, nat_w hc, nat_inv hc, nat_conj hc]
  rfl

end CertificateChecks.KernelSporSch.HNIntr

end
