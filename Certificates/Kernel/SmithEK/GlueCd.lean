module

public import Certificates.Kernel.SmithEK.ChecksCd
public import Certificates.Kernel.SmithEK.GlueOU
public import CFSG.Certificates.Kernel.SmithEK.CdSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

theorem ptsL_nodup : pts.L.Nodup := by
  have H := CFSG.KC.Misc.Lines.Pts.of CFSG.KD.Misc.T46.pts CFSG.KD.Misc.Lines.pos
  exact ptsL_eq ▸ H.nodup

theorem ptsL_lt : ∀ c ∈ pts.L, c < 4096 := by
  have H := CFSG.KC.Misc.Lines.Pts.of CFSG.KD.Misc.T46.pts CFSG.KD.Misc.Lines.pos
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < 693 := pts_length ▸ hi
  have h := H.lt i hi'
  rw [← ptsL_eq, List.getD_eq_getElem _ _ hi] at h
  exact h

theorem mapF_ok : cdMapK frobC pts.L pd.FT = true := by
  have h : cdMapK cdFrob pts.L pd.FT = true := c21276map_0
  have e : cdFrob = frobC := funext cdFrob_eq
  rw [e] at h
  exact h

theorem mapD_ok : cdMapK dltC pts.L pd.DT = true := by
  have h : cdMapK cdDlt pts.L pd.DT = true := c21276map_1
  have e : cdDlt = dltC := funext cdDlt_eq
  rw [e] at h
  exact h

theorem frobT_get {p : Nat} (hp : p < 693) :
    (ptMapT frobC)[p]! = at' 10 pd.FT p ∧ at' 10 pd.FT p < 693 :=
  ⟨ptMapT_get uPts_eq ptsL_nodup pts_length ptsL_lt mapF_ok hp, (cdMapK_sound mapF_ok p hp).1⟩

theorem dltT_get {p : Nat} (hp : p < 693) :
    (ptMapT dltC)[p]! = at' 10 pd.DT p ∧ at' 10 pd.DT p < 693 :=
  ⟨ptMapT_get uPts_eq ptsL_nodup pts_length ptsL_lt mapD_ok hp, (cdMapK_sound mapD_ok p hp).1⟩

theorem dlt2T_get {p : Nat} (hp : p < 693) :
    (compTab (ptMapT dltC) (ptMapT dltC))[p]! = at' 10 pd.DT (at' 10 pd.DT p) ∧
      at' 10 pd.DT (at' 10 pd.DT p) < 693 := by
  rw [compTab_get _ _ hp, (dltT_get hp).1, (dltT_get (dltT_get hp).2).1]
  exact ⟨rfl, (dltT_get (dltT_get hp).2).2⟩

theorem invD_get {y : Nat} (hy : y < 693) :
    (invTab (ptMapT dltC))[y]! = at' 10 pd.DI y ∧ at' 10 pd.DI y < 693 := by
  have h := c21276inv_0
  have e0 : Nat.beq (nat_lit 0) (nat_lit 0) = true := rfl
  rw [e0, cond_true] at h
  have hB := cdInvK_sound h
  have hB' : ∀ y < 693, at' 10 pd.DI y < 693 ∧ (ptMapT dltC)[at' 10 pd.DI y]! = y := by
    intro y hy
    have e := (hB y hy).2
    simp only [List.foldr_cons, List.foldr_nil] at e
    rw [(dltT_get (hB y hy).1).1]
    exact ⟨(hB y hy).1, e⟩
  exact ⟨invTab_get (fun x hx => (dltT_get hx).1 ▸ (dltT_get hx).2) hB' hy, (hB y hy).1⟩

theorem invE_get {y : Nat} (hy : y < 693) :
    (invTab (compTab (ptMapT dltC) (ptMapT dltC)))[y]! = at' 10 pd.EI y ∧ at' 10 pd.EI y < 693 := by
  have h := c21276inv_1
  have e1 : Nat.beq (nat_lit 1) (nat_lit 0) = false := rfl
  rw [e1, cond_false] at h
  have hB := cdInvK_sound h
  have hB' : ∀ y < 693, at' 10 pd.EI y < 693 ∧
      (compTab (ptMapT dltC) (ptMapT dltC))[at' 10 pd.EI y]! = y := by
    intro y hy
    have e := (hB y hy).2
    simp only [List.foldr_cons, List.foldr_nil] at e
    rw [(dlt2T_get (hB y hy).1).1]
    exact ⟨(hB y hy).1, e⟩
  exact ⟨invTab_get (fun x hx => (dlt2T_get hx).1 ▸ (dlt2T_get hx).2) hB' hy, (hB y hy).1⟩

theorem lift0_get {x : Nat} (hx : x < 693) :
    (liftTab tvTabs 0)[x]! = at' 10 (pd.LT.getD 0 0) x ∧ at' 10 (pd.LT.getD 0 0) x < 693 := by
  have h : cdCompK (pd.LT.getD 0 0) [] = true := c21276lt_0
  have e := cdCompK_sound h x hx
  rw [List.foldr_nil] at e
  have e2 : liftTab tvTabs 0 = idTab := rfl
  rw [e2, idTab_get hx, e]
  exact ⟨rfl, hx⟩

theorem lift1_get {x : Nat} (hx : x < 693) :
    (liftTab tvTabs 1)[x]! = at' 10 (pd.LT.getD 1 0) x ∧ at' 10 (pd.LT.getD 1 0) x < 693 := by
  have h : cdCompK (pd.LT.getD 1 0) [CFSG.KD.Misc.Xi.TP (po.SW.getD 0 0 % 1024),
      CFSG.KD.Misc.Xi.TP (po.SW.getD 0 0 / 1024)] = true := c21276lt_1
  have e := cdCompK_sound h x hx
  simp only [List.foldr_cons, List.foldr_nil] at e
  have e2 : liftTab tvTabs 1 = stabTab tvTabs 0 := rfl
  have hS := stabAp_TP (sw_mem (g := 0) (by omega)) hx
  rw [← sw_get (by omega)] at hS
  rw [e2, stabTab_get _ _ hx, e]
  exact ⟨hS.1, hS.1 ▸ hS.2⟩

theorem lift2_get {x : Nat} (hx : x < 693) :
    (liftTab tvTabs 2)[x]! = at' 10 (pd.LT.getD 2 0) x ∧ at' 10 (pd.LT.getD 2 0) x < 693 := by
  have h : cdCompK (pd.LT.getD 2 0) [pd.FT] = true := c21276lt_2
  have e := cdCompK_sound h x hx
  simp only [List.foldr_cons, List.foldr_nil] at e
  have e2 : liftTab tvTabs 2 = ptMapT frobC := rfl
  rw [e2, e]
  exact frobT_get hx

theorem lift3_get {x : Nat} (hx : x < 693) :
    (liftTab tvTabs 3)[x]! = at' 10 (pd.LT.getD 3 0) x ∧ at' 10 (pd.LT.getD 3 0) x < 693 := by
  have h : cdCompK (pd.LT.getD 3 0) [pd.DT, pd.FT, pd.DI] = true := c21276lt_3
  have e := cdCompK_sound h x hx
  simp only [List.foldr_cons, List.foldr_nil] at e
  have e2 : liftTab tvTabs 3 =
      compTab (compTab (ptMapT dltC) (ptMapT frobC)) (invTab (ptMapT dltC)) := rfl
  obtain ⟨hI, hI'⟩ := invD_get hx
  obtain ⟨hF, hF'⟩ := frobT_get hI'
  obtain ⟨hD, hD'⟩ := dltT_get hF'
  rw [e2, e, compTab_get _ _ hx, hI, compTab_get _ _ hI', hF, hD]
  exact ⟨rfl, hD'⟩

theorem lift4_get {x : Nat} (hx : x < 693) :
    (liftTab tvTabs 4)[x]! = at' 10 (pd.LT.getD 4 0) x ∧ at' 10 (pd.LT.getD 4 0) x < 693 := by
  have h : cdCompK (pd.LT.getD 4 0) [pd.DT, pd.DT, pd.FT, pd.EI] = true := c21276lt_4
  have e := cdCompK_sound h x hx
  simp only [List.foldr_cons, List.foldr_nil] at e
  have e2 : liftTab tvTabs 4 = compTab (compTab (compTab (ptMapT dltC) (ptMapT dltC))
      (ptMapT frobC)) (invTab (compTab (ptMapT dltC) (ptMapT dltC))) := rfl
  obtain ⟨hI, hI'⟩ := invE_get hx
  obtain ⟨hF, hF'⟩ := frobT_get hI'
  obtain ⟨hD, hD'⟩ := dlt2T_get hF'
  rw [e2, e, compTab_get _ _ hx, hI, compTab_get _ _ hI', hF, hD]
  exact ⟨rfl, hD'⟩

theorem liftTab_get {j : Nat} (hj : j < 5) {x : Nat} (hx : x < 693) :
    (liftTab tvTabs j)[x]! = at' 10 (pd.LT.getD j 0) x ∧ at' 10 (pd.LT.getD j 0) x < 693 := by
  match j, hj with
  | 0, _ => exact lift0_get hx
  | 1, _ => exact lift1_get hx
  | 2, _ => exact lift2_get hx
  | 3, _ => exact lift3_get hx
  | 4, _ => exact lift4_get hx

theorem pl0_len : (po.PL.getD 0 []).length = 21 :=
  (plK_sound c21262pl_0 0 (by rw [pb_len]; omega)).1

theorem pl0_all_lt : ∀ w ∈ po.PL.getD 0 [], w < 693 :=
  (plK_sound c21262pl_0 0 (by rw [pb_len]; omega)).2.1

theorem arr_eq_of_get {A : Array Nat} {L : List Nat} {n : Nat} (hA : A.size = n)
    (hL : L.length = n) (h : ∀ k < n, L.getD k 0 = A[k]!) : A = L.toArray := by
  refine Array.ext (by rw [hA, List.size_toArray, hL]) fun k h1 h2 => ?_
  have hk : k < n := hA ▸ h1
  have e := h k hk
  rw [getElem!_pos _ k h1, List.getD_eq_getElem _ _ (hL ▸ hk)] at e
  rw [List.getElem_toArray]
  exact e.symm

theorem pl0_arr : uaPts[0]! = (po.PL.getD 0 []).toArray :=
  arr_eq_of_get (CFSG.LargeExtraspecial.SMod20.uaPlane_parts (i := 0) (by omega)).1 pl0_len
    fun _ hk => pl0_get hk

theorem pl0_nodup : (po.PL.getD 0 []).Nodup := by
  obtain ⟨-, -, hd, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts (i := 0) (by omega)
  rw [List.nodup_iff_injective_get]
  rintro ⟨k, hk⟩ ⟨l, hl⟩ he
  simp only [List.get_eq_getElem] at he
  have hk' : k < 21 := pl0_len ▸ hk
  have hl' : l < 21 := pl0_len ▸ hl
  by_contra hne
  refine hd k hk' l hl' (fun e => hne (Fin.ext e)) ?_
  rw [← pl0_get hk', ← pl0_get hl', List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl]
  exact he

theorem sa_ok {j : Nat} (hj : j < 5) :
    cdSaK (po.PL.getD 0 []) (pd.LT.getD j 0) (pd.SA.getD j []) = true := by
  match j, hj with
  | 0, _ => exact c21276sa_0
  | 1, _ => exact c21276sa_1
  | 2, _ => exact c21276sa_2
  | 3, _ => exact c21276sa_3
  | 4, _ => exact c21276sa_4

theorem cdSArrT_lift {j : Nat} (hj : j < 5) {k : Nat} (hk : k < 21) :
    (sArrT uaPts[0]! (liftTab tvTabs j))[k]! = (pd.SA.getD j []).getD k 0 :=
  sArrT_get pl0_arr pl0_nodup pl0_len pl0_all_lt (fun _ hx => (liftTab_get hj hx).1) (sa_ok hj) hk

theorem collAmat_lift {j : Nat} (hj : j < 5) (u : Nat) :
    collAmat (sArrT uaPts[0]! (liftTab tvTabs j)) u = amK po.CO (pd.SA.getD j []) u :=
  collAmat_amK co_get (fun _ hk => cdSArrT_lift hj (by omega)) u

theorem candT_lift {j : Nat} (hj : j < 5) (a : Nat) {x : Nat} (hx : x < 693) :
    (candT tvTabs uaPts[0]! (liftTab tvTabs j) a)[x]! =
      cdImg CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) a x :=
  candT_cdImg (fun _ hn => (pl0_get (by omega)).symm)
    (fun _ hn _ hy => ap_tvTabs_TP (pl0_lt (by omega)) hy) (fun _ hx => liftTab_get hj hx) a hx

theorem cdImg_lt_rec {TP : Nat → Nat} {W : List Nat}
    (hT : ∀ n < 9, ∀ y < 693, at' 10 (TP (W.getD n 0)) y < 693) (a : Nat) : ∀ n ≤ 9, ∀ y < 693,
    Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
      (fun n ih y => ih (bif bitK a n then at' 10 (TP (W.getD n 0)) y else y)) n y < 693
  | 0, _, _, hy => hy
  | n + 1, hn, y, hy => by
    change Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
      (fun n ih y => ih (bif bitK a n then at' 10 (TP (W.getD n 0)) y else y)) n
        (bif bitK a n then at' 10 (TP (W.getD n 0)) y else y) < 693
    refine cdImg_lt_rec hT a n (by omega) _ ?_
    cases bitK a n
    · exact hy
    · exact hT n (by omega) y hy

theorem cdImg_lt {j : Nat} (hj : j < 5) (a : Nat) {x : Nat} (hx : x < 693) :
    cdImg CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) a x < 693 :=
  cdImg_lt_rec (fun _ hn _ hy => (ap_tvTabs_TP (pl0_lt (by omega)) hy).2) a 9 le_rfl _
    (liftTab_get hj hx).2

theorem plane_img {j : Nat} (hj : j < 5) {a i i' : Nat}
    (h : cdPlK CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) a po.PL pb.P i i' = true)
    {k : Nat} (hk : k < 21) :
    uaMem uaPts[i']! ((candT tvTabs uaPts[0]! (liftTab tvTabs j) a)[(uaPts[i]!)[k]!]!) = true := by
  obtain ⟨hi, hi', hm⟩ := cdPlK_sound h
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts hi
  have hx := hlt k hk
  rw [candT_lift hj a hx, uaMem_pb hi' (cdImg_lt hj a hx)]
  exact hm _ (uaPts_mem_pl hi hk)

theorem plane_fix {j : Nat} (hj : j < 5) {a e : Nat} (he : e < 891)
    (h : ∀ x ∈ po.PL.getD e [],
      cdImg CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) a x = x)
    {k : Nat} (hk : k < 21) :
    (candT tvTabs uaPts[0]! (liftTab tvTabs j) a)[(uaPts[e]!)[k]!]! = (uaPts[e]!)[k]! := by
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts he
  rw [candT_lift hj a (hlt k hk)]
  exact h _ (uaPts_mem_pl he hk)

end CertificateChecks.KernelSmithEK
