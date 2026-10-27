module

public import Certificates.Data.J4M2.QStruct
public import Certificates.Kernel.J4Q.QT2AC
public import Certificates.Kernel.J4Q.MaskU
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q

theorem mulT_frTable (X Y : Array V2) : mulT X (frTable Y) = mulRows X Y := rfl

theorem getD_map_frTable (a : Array (Array V2)) (i : Nat) :
    (a.map frTable)[i]?.getD idT = frTable (a[i]?.getD (idRows ())) := by
  rw [Array.getElem?_map]
  cases a[i]? <;> rfl

theorem get!_range_map {α : Type} [Inhabited α] (f : Nat → α) {m n : Nat} (hn : n < m) :
    (((List.range m).map f).toArray)[n]! = f n := by
  rw [getElem!_pos _ n (by simp [hn])]
  simp

theorem get!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {n : Nat}
    (hn : n < a.size) : (a.map f)[n]! = f a[n]! := by
  rw [getElem!_pos _ n (by simpa using hn), getElem!_pos _ n hn]
  simp

theorem foldl_congr_mem {α β : Type} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ b ∈ l, ∀ x, f x b = g x b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h b List.mem_cons_self a]
    exact foldl_congr_mem l _ fun b' hb x => h b' (List.mem_cons_of_mem _ hb) x

theorem wordT_eq (w : List Int) : CFSG.Quasithin.J4M2.wordT w = wR w := by
  unfold CFSG.Quasithin.J4M2.wordT wR wordRows
  refine foldl_congr_mem w _ fun l _ acc => ?_
  by_cases h : 0 < l
  · rw [if_pos h, if_pos h, letT, getD_map_frTable, mulT_frTable, letM]
  · rw [if_neg h, if_neg h, letInvT, getD_map_frTable, mulT_frTable, letInv]

theorem wR_append (a b : List Int) : wR (a ++ b) = mulRows (wR a) (wR b) :=
  wordRows_append g5_wf g5i_wf a b

theorem powRows_comm {M : Array V2} (hM : WfA M) :
    ∀ e, mulRows M (powRows M e) = mulRows (powRows M e) M
  | 0 => by
    rw [powRows, mulRows_idRows (rows_wf_of hM), idRows_mulRows hM]
  | e + 1 => by
    rw [powRows, ← mulRows_assoc hM (wf_powRows hM e) hM, powRows_comm hM e]

theorem wR_powWord (w : List Int) : ∀ e, wR (powWord w e) = powRows (wR w) e
  | 0 => rfl
  | e + 1 => by
    rw [powWord, wR_append, wR_powWord w e, powRows_comm (wR_enc w).1]
    rfl

@[expose] noncomputable def kwK (i : Nat) : Nat := wordJ c rm one G5 G5i (mkKW.getD i [])

@[expose] noncomputable def gmK (n : Nat) : Nat :=
  if n < 12 then getN one QAs n
  else if n = 12 then YA
  else if n = 13 then YB
  else if n = 14 then YP5
  else if n = 15 then YP7
  else if n = 16 then YP11
  else if n < 28 then getN one Us (n - 17)
  else kwK (n - 28)

theorem uG5_chk : allR 11 (fun j =>
    Nat.beq (getN one Us j) (wordJ c rm one G5 G5i (uWordK j))) = true := by
  quickRfl

theorem gmats_get {n : Nat} (hn : n < 32) : gmats[n]! = CFSG.Quasithin.J4M2.wordT (genWord n) :=
  get!_range_map (fun n => CFSG.Quasithin.J4M2.wordT (genWord n)) hn

theorem gmats_size : gmats.size = 32 := by simp [gmats]

theorem gm_enc {n : Nat} (hn : n < 32) : WfA gmats[n]! ∧ encR gmats[n]! = gmK n := by
  rw [gmats_get hn, wordT_eq]
  unfold genWord gmK
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact qR_enc h1
  · exact ya_enc
  · exact yb_enc
  · rw [wR_powWord]
    exact y5_enc
  · rw [wR_powWord]
    exact y7_enc
  · rw [wR_powWord]
    exact y11_enc
  · refine ⟨(wR_enc _).1, ?_⟩
    rw [(wR_enc _).2, uWord_eq]
    exact (Nat.eq_of_beq_eq_true (allR_spec uG5_chk (n - 17) (by omega))).symm
  · refine ⟨(wR_enc _).1, ?_⟩
    rw [(wR_enc _).2, kWords_eq]
    rfl

theorem gtabs_get {n : Nat} (hn : n < 32) : gtabs[n]! = frTable gmats[n]! :=
  get!_map frTable gmats (by rw [gmats_size]; exact hn)

@[expose] def uRowsT : Array (Array V2) := ((List.range 11).map fun j => CFSG.Quasithin.J4M2.wordT (uWord j)).toArray

theorem uRowsT_enc : ∀ j < Us.length,
    WfA (uRowsT[j]?.getD (idRows ())) ∧ encR (uRowsT[j]?.getD (idRows ())) = getN one Us j := by
  intro j hj
  have hj' : j < 11 := hj
  have e : uRowsT[j]?.getD (idRows ()) = wR (uWord j) := by
    simp [uRowsT, hj', wordT_eq]
  rw [e]
  refine ⟨(wR_enc _).1, ?_⟩
  rw [(wR_enc _).2, uWord_eq]
  exact (Nat.eq_of_beq_eq_true (allR_spec uG5_chk j hj')).symm

theorem uTabs_get {j : Nat} (hj : j < 11) : uTabs[j]! = frTable (CFSG.Quasithin.J4M2.wordT (uWord j)) :=
  get!_range_map (fun j => frTable (CFSG.Quasithin.J4M2.wordT (uWord j))) hj

theorem etaM_eq (m : Nat) : etaM m = etaRows uRowsT 11 m := by
  unfold etaM etaRows
  refine foldl_congr_mem _ _ fun j hj acc => ?_
  have hj' : j < 11 := List.mem_range.1 hj
  have e : uRowsT[j]?.getD (idRows ()) = CFSG.Quasithin.J4M2.wordT (uWord j) := by simp [uRowsT, hj']
  rw [uTabs_get hj', e]
  rfl

theorem etaM_enc (m : Nat) : WfA (etaM m) ∧ encR (etaM m) = etaK c rm one Us m := by
  rw [etaM_eq]
  exact enc_etaRows hK uRowsT_enc m

theorem zM_enc : WfA zM ∧ encR zM = ZM :=
  ⟨(etaM_enc 1131).1, (etaM_enc 1131).2.trans (Nat.eq_of_beq_eq_true z_chk).symm⟩

theorem zT_eq : zT = frTable zM := rfl

theorem qM_get {k : Nat} (hk : k < 12) : qM[k]! = gmats[k]! :=
  get!_range_map (fun k => gmats[k]!) hk

theorem qM_size : qM.size = 12 := by simp [qM]

theorem qM_enc {k : Nat} (hk : k < 12) : WfA qM[k]! ∧ encR qM[k]! = getN one QAs k := by
  rw [qM_get hk]
  have h := gm_enc (n := k) (by omega)
  simp only [gmK, hk, ↓reduceIte] at h
  exact h

theorem qT_get {k : Nat} (hk : k < 12) : qT[k]! = frTable qM[k]! :=
  get!_map frTable qM (by rw [qM_size]; exact hk)

theorem qI_get {k : Nat} (hk : k < 12) : qI[k]! = invRows qM[k]! :=
  get!_map invRows qM (by rw [qM_size]; exact hk)

theorem qIT_get {k : Nat} (hk : k < 12) : qIT[k]! = frTable qI[k]! :=
  get!_map frTable qI (by simp [qI, qM_size]; exact hk)

theorem qinv_chk : allR 12 (fun k => andB (canonJ pad (getN one QIs k))
    (Nat.beq (mulJ c rm (getN one QAs k) (getN one QIs k)) one)) = true := by
  quickRfl

theorem qI_enc {k : Nat} (hk : k < 12) : WfA qI[k]! ∧ encR qI[k]! = getN one QIs k := by
  have h := allR_spec qinv_chk k hk
  rw [andB_eq, Bool.and_eq_true] at h
  rw [qI_get hk]
  exact invRows_enc hK (qM_enc hk).1 h.1 (by rw [(qM_enc hk).2]; exact h.2)

@[expose] noncomputable def qProdK (e : Nat) (δ : Bool) : Nat :=
  let m := (List.range 12).foldl (fun acc j => if e.testBit j then mulJ c rm acc (getN one QAs j)
    else acc) one
  if δ then mulJ c rm m ZM else m

theorem qProd_enc (e : Nat) (δ : Bool) : WfA (qProd e δ) ∧ encR (qProd e δ) = qProdK e δ := by
  have key : ∀ (l : List Nat), (∀ j ∈ l, j < 12) → ∀ (acc : Array V2) (a : Nat),
      WfA acc ∧ encR acc = a →
      WfA (l.foldl (fun acc j => if e.testBit j then mulT acc qT[j]! else acc) acc) ∧
        encR (l.foldl (fun acc j => if e.testBit j then mulT acc qT[j]! else acc) acc) =
          l.foldl (fun acc j => if e.testBit j then mulJ c rm acc (getN one QAs j) else acc) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons j l ih =>
      intro hl acc a h
      have hj := hl j List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      by_cases hb : e.testBit j
      · simp only [hb, ↓reduceIte]
        rw [qT_get hj]
        exact mul_enc hK h (qM_enc hj)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact h
  have hm := key (List.range 12) (fun j hj => List.mem_range.1 hj) (idRows ()) one (id_enc hK)
  unfold qProd qProdK
  cases δ
  · exact hm
  · exact mul_enc hK hm zM_enc

@[expose] noncomputable def oW : List (List Int) :=
  [aK, bK, powWord y5K y5e, powWord y7K y7e, powWord y11K y11e]

@[expose] noncomputable def oiK (i : Nat) : Nat := wordJ c rm one G5 G5i (negRev (oW.getD i []))

theorem oinv_chk : allR 5 (fun i => andB (canonJ pad (oiK i))
    (Nat.beq (mulJ c rm (gmK (12 + i)) (oiK i)) one)) = true := by
  quickRfl

theorem oInv_enc {i : Nat} (hi : i < 5) :
    WfA (invRows gmats[12 + i]!) ∧ encR (invRows gmats[12 + i]!) = oiK i := by
  have h := allR_spec oinv_chk i hi
  rw [andB_eq, Bool.and_eq_true] at h
  have hg := gm_enc (n := 12 + i) (by omega)
  exact invRows_enc hK hg.1 h.1 (by rw [hg.2]; exact h.2)

theorem oI_get {i : Nat} (hi : i < 5) : oI[i]! = invRows gmats[12 + i]! :=
  get!_range_map (fun i => invRows gmats[12 + i]!) hi

theorem oIT_get {i : Nat} (hi : i < 5) : oIT[i]! = frTable oI[i]! :=
  get!_map frTable oI (by simp [oI]; exact hi)

@[expose] noncomputable def cmK : Nat := mulJ c rm (mulJ c rm (mulJ c rm YA YB) (oiK 0)) (oiK 1)

theorem cMat_enc : WfA cMat ∧ encR cMat = cmK := by
  have ha := gm_enc (n := 12) (by omega)
  have hb := gm_enc (n := 13) (by omega)
  simp only [gmK] at ha hb
  have hai := oInv_enc (i := 0) (by omega)
  have hbi := oInv_enc (i := 1) (by omega)
  unfold cMat
  rw [gtabs_get (by omega)]
  exact mul_enc hK (mul_enc hK (mul_enc hK ha hb) hai) hbi

end CertificateChecks.KernelJ4M2

end
