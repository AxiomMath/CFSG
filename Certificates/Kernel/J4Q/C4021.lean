module

public import CFSG.Sporadic.J4.QTOutCommNative
public import Certificates.Kernel.J4Q.CommBase
public import Certificates.Kernel.J4Q.C4023
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def cmQK (u0 u1 i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) u1 (Nat.beq i 111))
    (vecJ rm u0 (getN one WLS i)) (Nat.blt i 111)

theorem qRows_enc {u0 u1 : V2} (h0 : u0.wf = true) (h1 : u1.wf = true) :
    WfA (qRows u0 u1) ∧ encR (qRows u0 u1) = rowsJ (cmQK (v2N u0) (v2N u1)) := by
  have hlen : (((List.range 111).map fun l => frApply (wTabs[l]!) u0) ++ [u1]).length = 112 := by simp
  have hwf : ∀ v ∈ ((List.range 111).map fun l => frApply (wTabs[l]!) u0) ++ [u1], v.wf = true := by
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
      rw [wTabs_get (List.mem_range.1 hl)]
      exact wf_frApply (wmat_enc (List.mem_range.1 hl)).1 _
    · rw [List.mem_singleton.1 h]
      exact h1
  obtain ⟨e1, e2⟩ := enc_toArray _ hlen hwf
  refine ⟨e1, e2.trans (rowsJ_congr fun i hi => ?_)⟩
  unfold cmQK
  by_cases h : i < 111
  · have hb : Nat.blt i 111 = true := by
      rw [Nat.blt_eq]
      exact h
    rw [hb, List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
      List.getElem_map, List.getElem_range, wTabs_get h, v2N_frApply hK (wmat_enc h).1 h0,
      (wmat_enc h).2]
  · have hi' : i = 111 := by omega
    subst hi'
    rfl

@[expose] noncomputable def selK (b : Bool) (x : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (nat_lit 0) x b

theorem v2N_zero : v2N V2.zero = 0 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem zero_wf : V2.zero.wf = true := by decide

theorem orB_eq' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem selV_enc (b : Bool) {x : V2} (hx : x.wf = true) :
    (selV b x).wf = true ∧ v2N (selV b x) = selK b (v2N x) := by
  cases b
  · exact ⟨zero_wf, v2N_zero⟩
  · exact ⟨hx, rfl⟩

theorem u1s_chk : allR 4 (fun i => Nat.blt (v2N (u1s[i]!)) (Nat.shiftLeft 1 112)) = true := by quickRfl

theorem u1s_wf {i : Nat} (hi : i < 4) : (u1s[i]!).wf = true :=
  wf_of_lt (lt_of_blt (allR_spec u1s_chk i hi))

@[expose] noncomputable def cmKapK (b0 b1 b2 b3 : Bool) : Nat :=
  Nat.xor (Nat.xor (selK b0 (rowJ rm BK 0)) (selK b1 (rowJ rm BK 1)))
    (Nat.xor (selK b2 (rowJ rm BK 2)) (selK b3 (rowJ rm BK 3)))

@[expose] noncomputable def cmU1K (b0 b1 b2 b3 d0 d1 : Bool) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (selK b0 (v2N (u1s[0]!))) (selK b1 (v2N (u1s[1]!))))
      (Nat.xor (selK b2 (v2N (u1s[2]!))) (selK b3 (v2N (u1s[3]!)))))
    (Nat.xor (selK d0 (rowJ rm BF 0)) (selK d1 (rowJ rm BF 1)))

theorem bk_row (i : Nat) : (bkRows[i]!).wf = true ∧ v2N (bkRows[i]!) = rowJ rm BK i :=
  ⟨wf_getElem! bk_enc.1 i, by rw [v2N_getElem! hK bk_enc.1, bk_enc.2]⟩

theorem bf_row (i : Nat) : (bfRows[i]!).wf = true ∧ v2N (bfRows[i]!) = rowJ rm BF i :=
  ⟨wf_getElem! bf_enc.1 i, by rw [v2N_getElem! hK bf_enc.1, bf_enc.2]⟩

theorem xor_enc {a b : V2} {x y : Nat} (ha : a.wf = true ∧ v2N a = x) (hb : b.wf = true ∧ v2N b = y) :
    (a.xor b).wf = true ∧ v2N (a.xor b) = Nat.xor x y :=
  ⟨wf_xor ha.1 hb.1, by rw [v2N_xor, ha.2, hb.2]⟩

theorem sel_enc (b : Bool) {x : V2} {n : Nat} (h : x.wf = true ∧ v2N x = n) :
    (selV b x).wf = true ∧ v2N (selV b x) = selK b n := by
  rw [← h.2]
  exact selV_enc b h.1

theorem kap_enc (b0 b1 b2 b3 : Bool) :
    (kappaComb b0 b1 b2 b3).wf = true ∧ v2N (kappaComb b0 b1 b2 b3) = cmKapK b0 b1 b2 b3 :=
  xor_enc (xor_enc (sel_enc b0 (bk_row 0)) (sel_enc b1 (bk_row 1)))
    (xor_enc (sel_enc b2 (bk_row 2)) (sel_enc b3 (bk_row 3)))

theorem u1_enc (b0 b1 b2 b3 d0 d1 : Bool) :
    ((uComb b0 b1 b2 b3).xor (fixComb d0 d1)).wf = true ∧
      v2N ((uComb b0 b1 b2 b3).xor (fixComb d0 d1)) = cmU1K b0 b1 b2 b3 d0 d1 :=
  xor_enc (xor_enc (xor_enc (sel_enc b0 ⟨u1s_wf (by decide), rfl⟩) (sel_enc b1 ⟨u1s_wf (by decide), rfl⟩))
      (xor_enc (sel_enc b2 ⟨u1s_wf (by decide), rfl⟩) (sel_enc b3 ⟨u1s_wf (by decide), rfl⟩)))
    (xor_enc (sel_enc d0 (bf_row 0)) (sel_enc d1 (bf_row 1)))

theorem tcomb_enc (b0 b1 b2 b3 d0 d1 : Bool) : WfA (tcomb b0 b1 b2 b3 d0 d1) ∧
    encR (tcomb b0 b1 b2 b3 d0 d1) =
      mulJ c rm PRI (rowsJ (cmQK (cmKapK b0 b1 b2 b3) (cmU1K b0 b1 b2 b3 d0 d1))) := by
  obtain ⟨k1, k2⟩ := kap_enc b0 b1 b2 b3
  obtain ⟨u1, u2⟩ := u1_enc b0 b1 b2 b3 d0 d1
  have hq := qRows_enc k1 u1
  rw [k2, u2] at hq
  exact mul_enc hK pInv_enc hq

@[expose] noncomputable def cmJgK (g : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) Bi B (Nat.beq g 1)) A (Nat.beq g 0)

theorem jgen_enc (g : Nat) : WfA (jgen g) ∧ encR (jgen g) = cmJgK g := by
  unfold jgen cmJgK
  by_cases h0 : g = 0
  · subst h0
    exact rowsA_enc
  · rw [nbeq_false h0]
    simp only [h0, ↓reduceIte]
    by_cases h1 : g = 1
    · subst h1
      exact rowsB_enc
    · rw [nbeq_false h1]
      simp only [h1, ↓reduceIte]
      exact base_invs 1

@[expose] noncomputable def cmJwK (w : List Nat) : Nat := List.foldl (fun acc g => mulJ c rm acc (cmJgK g)) one w

theorem foldl_jgen_enc : ∀ (w : List Nat) (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
    WfA (w.foldl (fun acc g => mulRows acc (jgen g)) acc) ∧
      encR (w.foldl (fun acc g => mulRows acc (jgen g)) acc) = w.foldl (fun a g => mulJ c rm a (cmJgK g)) a
  | [], _, _, h => h
  | g :: w, acc, a, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_jgen_enc w _ _ (mul_enc hK h (jgen_enc g))

theorem jword_enc (w : List Nat) : WfA (jword w) ∧ encR (jword w) = cmJwK w :=
  foldl_jgen_enc w _ _ (id_enc hK)

@[expose] noncomputable def cbK (t : Nat) : Bool :=
  strictB (mulJ c rm PRI (rowsJ (cmQK (cmKapK (bitB t 0) (bitB t 1) (bitB t 2) (bitB t 3))
      (cmU1K (bitB t 0) (bitB t 1) (bitB t 2) (bitB t 3) (bitB t 4) (bitB t 5))))) fun T =>
    orB (Nat.beq T one) (notB (Nat.beq (powFuelK c rm one 128
      (mulJ c rm (cmJwK (witWords.getD t [])) T) 86775571046077562880) one))

#j4q_all CFSG.KD.J4Q.CB CertificateChecks.KernelJ4Q.cbK 64

theorem comb_bits : ∀ b0 b1 b2 b3 d0 d1 : Bool, combIdx b0 b1 b2 b3 d0 d1 < 64 ∧
    bitB (combIdx b0 b1 b2 b3 d0 d1) 0 = b0 ∧ bitB (combIdx b0 b1 b2 b3 d0 d1) 1 = b1 ∧
    bitB (combIdx b0 b1 b2 b3 d0 d1) 2 = b2 ∧ bitB (combIdx b0 b1 b2 b3 d0 d1) 3 = b3 ∧
    bitB (combIdx b0 b1 b2 b3 d0 d1) 4 = d0 ∧ bitB (combIdx b0 b1 b2 b3 d0 d1) 5 = d1 := by
  decide

theorem comb_ok (b0 b1 b2 b3 d0 d1 : Bool) :
    eqRows (tcomb b0 b1 b2 b3 d0 d1) idRows = true ∨
      (wfRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
        (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) = true ∧
      eqRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
        (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) idRows = false) := by
  obtain ⟨hlt, e0, e1, e2, e3, e4, e5⟩ := comb_bits b0 b1 b2 b3 d0 d1
  have h := CB.all _ hlt
  rw [cbK, e0, e1, e2, e3, e4, e5, strictB_eq] at h
  have hT := tcomb_enc b0 b1 b2 b3 d0 d1
  have hX := mul_enc hK (jword_enc (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) [])) hT
  have hP := enc_powFuel hK 128 _ _ 86775571046077562880 hX
  rw [orB_eq', Bool.or_eq_true] at h
  rcases h with h | h
  · left
    rw [eqRows_of hT (id_enc hK)]
    exact h
  · right
    refine ⟨wf_bool hP.1, ?_⟩
    rw [powBin, eqRows_of hP (id_enc hK)]
    rw [notB_eq, Bool.not_eq_true'] at h
    exact h

theorem wro_enc (w : List Int) :
    WfA (wordRowsOf w) ∧ encR (wordRowsOf w) = wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] w :=
  enc_wordRows hK loc_gens loc_invs w

theorem edges_chk : allR 6 (fun e => Nat.beq (vecJ rm (v2N v0Vec) (getN one EMS e)) 0) = true := by quickRfl

theorem rg_chk : allR 2 (fun g => Nat.beq (vecJ rm (v2N v0Vec) (getN one RGS g))
    (Nat.xor (vecJ rm (v2N v1Vec) (cmMGK g)) (v2N v1Vec))) = true := by quickRfl

theorem u1_chk : allR 4 (fun i => allR 2 fun g => Nat.beq (vecJ rm (v2N (u1s[i]!)) (Nat.xor (cmMGK g) one))
    (vecJ rm (rowJ rm BK i) (getN one RGS g))) = true := by quickRfl

theorem kcols_ok : (∀ c ∈ kCols, c.1 < 6 ∧ c.2 < 112) ∧ (∀ c ∈ fCols, c.1 < 2 ∧ c.2 < 112) := by
  decide

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem c4021 : (kEdges.length = 6)
    ∧ ((∀ c ∈ kCols, c.1 < 6 ∧ c.2 < 112) ∧ (∀ c ∈ fCols, c.1 < 2 ∧ c.2 < 112))
    ∧ (∀ e ∈ kEdges, e.1 < 111)
    ∧ (eqRows (mulRows pInv pRows) idRows = true ∧
          eqRows (mulRows pRows pInv) idRows = true)
    ∧ (eqRows (mulRows bkRows (phiOf edgeMats kCols)) (psiRows 4) = true ∧
          eqRows (mulRows (invRows bkRows) bkRows) idRows = true)
    ∧ (eqRows (mulRows bfRows (phiOf mgps fCols)) (psiRows 2) = true ∧
          eqRows (mulRows (invRows bfRows) bfRows) idRows = true)
    ∧ (∀ e < 6, (frApply (frTable (edgeMat e)) v0Vec).beq V2.zero = true)
    ∧ (∀ g < 2, (frApply (frTable (rg g)) v0Vec).beq
          ((frApply (frTable (mg g)) v1Vec).xor v1Vec) = true)
    ∧ (∀ i < 4, ∀ g < 2,
          (frApply (frTable (mgp g)) (u1s[i]!)).beq (frApply (frTable (rg g)) (bkRows[i]!)) = true)
    ∧ (∀ b0 b1 b2 b3 d0 d1 : Bool,
          eqRows (tcomb b0 b1 b2 b3 d0 d1) idRows = true ∨
            (wfRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
              (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) = true ∧
            eqRows (powBin (mulRows (jword (witWords.getD (combIdx b0 b1 b2 b3 d0 d1) []))
              (tcomb b0 b1 b2 b3 d0 d1)) 86775571046077562880) idRows = false))
    ∧ (eqRows (mulRows (mulRows yRows (wordRowsOf mWord0)) yRows)
            (mulRows (etaR mConjC0) (wordRowsOf mConjW0)) = true ∧
          eqRows (mulRows (mulRows yRows (wordRowsOf mWord1)) yRows)
            (mulRows (etaR mConjC1) (wordRowsOf mConjW1)) = true)
    ∧ ((∀ ℓ ∈ mWord0, ℓ ∈ letters) ∧ (∀ ℓ ∈ mWord1, ℓ ∈ letters) ∧
          (∀ ℓ ∈ mConjW0, ℓ ∈ letters) ∧ (∀ ℓ ∈ mConjW1, ℓ ∈ letters) ∧ mConjC0 < 2 ^ 11 ∧
          mConjC1 < 2 ^ 11)
    ∧ (((List.range 2048).any fun c => actT (wordT wObs) c != c) = true) := by
  have hk := kcols_ok
  have hphiK := phiOf_enc (mats := edgeMats) (Ms := EMS) (n := 6)
    (fun e he => by rw [edgeMats_get he]; exact edgeMat_enc he) hk.1
  have hphiF := phiOf_enc (mats := mgps) (Ms := [Nat.xor (cmMGK 0) one, Nat.xor (cmMGK 1) one]) (n := 2)
    (fun g hg => by
      rw [mgps_get hg]
      rcases g with _ | _ | g
      · exact mgp_enc 0
      · exact mgp_enc 1
      · omega) hk.2
  refine ⟨rfl, hk, by decide, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, comb_ok, ⟨?_, ?_⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩, by quickRfl⟩
  · rw [eqRows_of (mul_enc hK pInv_enc pRows_enc) (id_enc hK)]
    quickRfl
  · rw [eqRows_of (mul_enc hK pRows_enc pInv_enc) (id_enc hK)]
    quickRfl
  · rw [eqRows_of (mul_enc hK bk_enc hphiK) (psiRows_enc 4)]
    quickRfl
  · rw [eqRows_of (mul_enc hK bkInv_enc bk_enc) (id_enc hK)]
    quickRfl
  · rw [eqRows_of (mul_enc hK bf_enc hphiF) (psiRows_enc 2)]
    quickRfl
  · rw [eqRows_of (mul_enc hK bfInv_enc bf_enc) (id_enc hK)]
    quickRfl
  · intro e he
    rw [beq_v2N, v2N_frApply hK (edgeMat_enc he).1 v0_wf, (edgeMat_enc he).2]
    exact allR_spec edges_chk e he
  · intro g hg
    rw [beq_v2N, v2N_frApply hK (rg_enc hg).1 v0_wf, (rg_enc hg).2, v2N_xor,
      v2N_frApply hK (mg_enc g).1 v1_wf, (mg_enc g).2]
    exact allR_spec rg_chk g hg
  · intro i hi g hg
    rw [beq_v2N, v2N_frApply hK (mgp_enc g).1 (u1s_wf hi), (mgp_enc g).2,
      v2N_frApply hK (rg_enc hg).1 (bk_row i).1, (rg_enc hg).2, (bk_row i).2]
    exact allR_spec (allR_spec u1_chk i hi) g hg
  · rw [eqRows_of (mul_enc hK (mul_enc hK y_enc (wro_enc mWord0)) y_enc)
      (mul_enc hK (etaR_enc mConjC0) (wro_enc mConjW0))]
    quickRfl
  · rw [eqRows_of (mul_enc hK (mul_enc hK y_enc (wro_enc mWord1)) y_enc)
      (mul_enc hK (etaR_enc mConjC1) (wro_enc mConjW1))]
    quickRfl

end CertificateChecks.KernelJ4Q

end
