module

public import Certificates.Kernel.HN1408.CayleyDefs
public import Certificates.Kernel.HN1408.EnumH
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleyCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Sl25Strict

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

structure CodeM (T : Type) [Mul T] where
  enc : T → Nat
  mulC : Nat → Nat → Nat
  inj : Function.Injective enc
  hom : ∀ x y, enc (x * y) = mulC (enc x) (enc y)

section Loop

variable {T : Type}

def pushes (g : Array T → Nat → T) (n : Nat) (a : Array T) : Array T :=
  (List.range' 1 n).foldl (fun fv k => fv.push (g fv k)) a

theorem pushes_succ (g : Array T → Nat → T) (n : Nat) (a : Array T) :
    pushes g (n + 1) a = (pushes g n a).push (g (pushes g n a) (n + 1)) := by
  unfold pushes
  rw [List.range'_concat, List.foldl_append]
  simp [Nat.add_comm]

theorem pushes_size (g : Array T → Nat → T) (a : Array T) :
    ∀ n, (pushes g n a).size = a.size + n
  | 0 => rfl
  | n + 1 => by rw [pushes_succ, Array.size_push, pushes_size g a n]; omega

theorem getD_push_lt {a : Array T} {x : T} {j : Nat} (d : T) (h : j < a.size) :
    (a.push x).getD j d = a.getD j d := by
  unfold Array.getD
  rw [dif_pos (by rw [Array.size_push]; omega), dif_pos h]
  exact Array.getElem_push_lt h

theorem getD_push_eq (a : Array T) (x d : T) : (a.push x).getD a.size d = x := by
  unfold Array.getD
  rw [dif_pos (by rw [Array.size_push]; omega)]
  exact Array.getElem_push_eq

theorem pushes_stable (g : Array T → Nat → T) (a : Array T) (d : T) {n : Nat} {j : Nat}
    (hj : j < a.size + n) : ∀ N, n ≤ N → (pushes g N a).getD j d = (pushes g n a).getD j d := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [pushes_succ, getD_push_lt _ (by rw [pushes_size]; omega), ih]

end Loop

theorem cayleyImages_eq {T : Type} [Group T] (ts : Array T) (par lab : Array Nat) :
    cayleyImages ts par lab =
      pushes (fun fv k => fv.getD (par.getD k 0) 1 * ts.getD (lab.getD k 0) 1) (par.size - 1)
        #[1] := by
  unfold cayleyImages pushes
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem cayleyImages_spec {T : Type} [Group T] (ts : Array T) (par lab : Array Nat)
    (hp : 0 < par.size) :
    (cayleyImages ts par lab).size = par.size ∧ (cayleyImages ts par lab).getD 0 1 = 1 ∧
      ∀ k, 1 ≤ k → k < par.size → par.getD k 0 < k →
        (cayleyImages ts par lab).getD k 1 =
          (cayleyImages ts par lab).getD (par.getD k 0) 1 * ts.getD (lab.getD k 0) 1 := by
  rw [cayleyImages_eq]
  set g : Array T → Nat → T := fun fv k => fv.getD (par.getD k 0) 1 * ts.getD (lab.getD k 0) 1
  have h1 : (#[1] : Array T).size = 1 := rfl
  refine ⟨by rw [pushes_size, h1]; omega, ?_, ?_⟩
  · rw [pushes_stable g #[1] 1 (n := 0) (by rw [h1]; omega) _ (Nat.zero_le _)]
    rfl
  · intro k hk1 hk hpk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hs : (pushes g k' #[1]).size = k' + 1 := by rw [pushes_size, h1]; omega
    rw [pushes_stable g #[1] 1 (n := k' + 1) (by rw [h1]; omega) _ (by omega), pushes_succ,
      ← hs, getD_push_eq, hs]
    change (pushes g k' #[1]).getD (par.getD (k' + 1) 0) 1 * ts.getD (lab.getD (k' + 1) 0) 1 = _
    rw [pushes_stable g #[1] 1 (n := k') (by rw [h1]; omega) (par.size - 1) (by omega)]

theorem cyBA {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := (bAnd_iff _ _).1 h

theorem ofFn_getD {α : Type} {n k : Nat} (f : Nat → α) (d : α) (hk : k < n) :
    (Array.ofFn (n := n) fun i => f i.val).getD k d = f k := by
  unfold Array.getD
  rw [dif_pos (by rw [Array.size_ofFn]; exact hk)]
  exact Array.getElem_ofFn ..

theorem ofFn_getElem! {α : Type} [Inhabited α] {n k : Nat} (f : Nat → α) (hk : k < n) :
    (Array.ofFn (n := n) fun i => f i.val)[k]! = f k := by
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem cayleyOK_of {T : Type} [Group T] [DecidableEq T] (M : CodeM T) {cap m cnt c1 : Nat}
    {ws : List (List Nat)} {ts : List T} {tc C : List Nat}
    {G GI GJ TT PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (hd : cyHd ws m cap G GI GJ TT PL cnt = true)
    (hr : cyRec ws.length G GI GJ TT PL POS SRT SRI HS HSI CL cnt = true)
    (hlen : ws.length = ts.length) (h1 : M.enc 1 = c1) (htc : ts.map M.enc = tc)
    (hc : cayK M.mulC c1 tc ws.length cnt PL CL C = true) :
    cayleyOK cap m ws ts = true := by
  set K := ws.length with hK
  unfold cyHd at hd
  obtain ⟨hd1, hd2⟩ := cyBA hd
  obtain ⟨hd3, hd4⟩ := cyBA hd2
  have hm : cnt = m := Nat.eq_of_beq_eq_true hd3
  have hcnt : 0 < cnt := Nat.blt_eq.mp (cyBA hd4).1
  have hg : ∀ j < K, GI j = WK (ws.getD j []) ∧ G j = idK ∧
      canonK 1408 11 (mask 11) (1408 * 11) (GJ j) = true ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j) = true := by
    intro j hj
    obtain ⟨a, h8⟩ := cyBA (allN_spec hd1 j hj)
    obtain ⟨b, h9⟩ := cyBA h8
    obtain ⟨c, d⟩ := cyBA h9
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c, d⟩
  unfold cyRec at hr
  obtain ⟨hp, hr2⟩ := cyBA hr
  obtain ⟨hs, hcl⟩ := cyBA hr2
  have hp' : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI K cnt TT PL POS SRT SRI i =
      true := fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi
  have hs' : ∀ i < cnt, hsortPtK 1408 11 (mask 11) cnt TT HS HSI i = true :=
    fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi
  have hcl' : ∀ c < cnt * (K + K),
      findPtK cnt TT (prodQK 1408 11 (mask 11) (K + K) TT (bothK K GI GJ)) CL c = true :=
    fun c hc' => slK_spec hcl c (Nat.zero_le _) (by change c < 0 + cnt * (K + K); omega)
      (by change c < cnt * (K + K); omega)
  obtain ⟨eW, -⟩ := enumW_of hl (fun j hj => (hg j hj).2.1) (fun j hj => (hg j hj).1)
    (fun j hj => ⟨(hg j hj).2.2.2, (hg j hj).2.2.1⟩) hd4 hp' hs' hcl' hm
  have hTabs := tabsW_tabs hl (fun j hj => (hg j hj).1)
  obtain ⟨e, htree, -⟩ := mulH_sound hn (fun j hj => (hg j hj).2.1) hTabs hd4 hp' hs'
  have hT : ∀ i < cnt, Cn (TT i) := fun i hi => penumPt_canon (hp' i hi)
  have hgs : (tabsW ws).toArray.size = K := hTabs.1
  have hsz : (hRec 1408 11 cnt TT PL).1.size = cnt := hRec_size 1408 11 cnt TT PL
  have hpsz : (hRec 1408 11 cnt TT PL).2.1.size = cnt := Array.size_ofFn
  have hparD : ∀ k < cnt, (hRec 1408 11 cnt TT PL).2.1.getD k 0 = parOf PL k :=
    fun k hk => ofFn_getD (parOf PL) 0 hk
  have hlabD : ∀ k < cnt, (hRec 1408 11 cnt TT PL).2.2.getD k 0 = labOf PL k :=
    fun k hk => ofFn_getD (labOf PL) 0 hk
  unfold mulTreeOK at htree
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htree
  obtain ⟨⟨-, h0⟩, hall⟩ := htree
  have htr : ∀ k, 1 ≤ k → k < cnt → parOf PL k < k ∧ labOf PL k < K := by
    intro k hk1 hk
    have := allIn_eq_true.1 hall k hk1 (by rw [hsz]; exact hk)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have ep : (hRec 1408 11 cnt TT PL).2.1[k]! = parOf PL k := ofFn_getElem! (parOf PL) hk
    have el : (hRec 1408 11 cnt TT PL).2.2[k]! = labOf PL k := ofFn_getElem! (labOf PL) hk
    rw [ep, el, hgs] at this
    exact ⟨this.1.1, this.1.2⟩
  simp only [cayK, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1', c2⟩, c3⟩, c4⟩, c5⟩ := hc
  have hClen : C.length = cnt := Nat.eq_of_beq_eq_true c1'
  have hts : ∀ i < ts.length, M.enc (ts.toArray.getD i 1) = tc.getD i 0 := by
    intro i hi
    rw [← htc, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
    unfold Array.getD
    rw [dif_pos (by simpa using hi)]
    rfl
  set fv := cayleyImages ts.toArray (hRec 1408 11 cnt TT PL).2.1 (hRec 1408 11 cnt TT PL).2.2
    with hfv
  obtain ⟨fsz, f0, fk⟩ := cayleyImages_spec ts.toArray (hRec 1408 11 cnt TT PL).2.1
    (hRec 1408 11 cnt TT PL).2.2 (by rw [hpsz]; exact hcnt)
  rw [← hfv] at fsz f0 fk
  have hcode : ∀ k < cnt, M.enc (fv.getD k 1) = C.getD k 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [f0, h1]
        exact (Nat.eq_of_beq_eq_true c2).symm
      · obtain ⟨hpk, hlk⟩ := htr k hk0 hk
        rw [fk k hk0 (by rw [hpsz]; exact hk) (by rw [hparD k hk]; exact hpk), M.hom,
          hparD k hk, hlabD k hk, ih _ hpk (by omega), hts _ (by omega)]
        exact (Nat.eq_of_beq_eq_true (List.all_eq_true.1 c3 k
          (List.mem_range'_1.2 ⟨hk0, by omega⟩))).symm
  unfold cayleyOK
  simp only [e]
  rw [← hfv]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨eW, hlen⟩, by rw [hsz]; exact hcnt⟩, h0⟩, by rw [fsz, hpsz, hsz]⟩, f0⟩, ?_⟩, ?_⟩
  · unfold cayleyStepOK
    rw [allIn_eq_true]
    intro k _ hk
    rw [allIn_eq_true]
    intro i _ hi
    rw [hsz] at hk
    rw [hgs] at hi
    have hc' : k * (K + K) + i < cnt * (K + K) := by
      have := Nat.mul_le_mul_right (K + K) (Nat.succ_le_of_lt hk)
      rw [Nat.succ_mul] at this
      omega
    obtain ⟨hq, he⟩ := findPt_spec (hcl' _ hc')
    unfold prodQK at he
    obtain ⟨e1, e2⟩ := div_mod_pair (i := k) (K := K + K) (by omega : i < K + K)
    rw [show Nat.div (k * (K + K) + i) (K + K) = k from e1,
      show Nat.mod (k * (K + K) + i) (K + K) = i from e2] at he
    have hb : bothK K GI GJ i = GI i := by
      unfold bothK
      rw [Nat.blt_eq.mpr hi]
    rw [hb] at he
    obtain ⟨hgi, hci⟩ := hTabs.2 i hi
    rw [List.any_eq_true]
    refine ⟨r32 CL (k * (K + K) + i), List.mem_range.2 (by rw [hsz]; exact hq), ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rw [hRec_get hk, hgi, compT_unpack (hT k hk) hci, ← he, hRec_get hq]
      exact tblEq_self (hT _ hq)
    · apply M.inj
      rw [M.hom, hcode _ hq, hcode k hk, hts i (by omega)]
      exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 (List.all_eq_true.1 c4 k
        (List.mem_range.2 hk)) i (List.mem_range.2 hi))
  · unfold distinctOK
    rw [allIn_eq_true]
    intro a _ ha
    rw [allIn_eq_true]
    intro b hab hb
    rw [fsz, hpsz] at ha hb
    apply decide_eq_true
    intro heq
    have := congrArg M.enc heq
    rw [hcode a ha, hcode b hb, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)] at this
    have := (List.Nodup.getElem_inj_iff (of_decide_eq_true c5)).1 this
    omega

@[expose] def sl25Enc (A : SL25S) : Nat :=
  (A.val.1 0 0).val + 5 * (A.val.1 0 1).val + 25 * (A.val.1 1 0).val + 125 * (A.val.1 1 1).val

theorem sl25Enc_digits (A : SL25S) :
    sl25Enc A % 5 = (A.val.1 0 0).val ∧ sl25Enc A / 5 % 5 = (A.val.1 0 1).val ∧
      sl25Enc A / 25 % 5 = (A.val.1 1 0).val ∧ sl25Enc A / 125 % 5 = (A.val.1 1 1).val := by
  have h0 := ZMod.val_lt (A.val.1 0 0)
  have h1 := ZMod.val_lt (A.val.1 0 1)
  have h2 := ZMod.val_lt (A.val.1 1 0)
  have h3 := ZMod.val_lt (A.val.1 1 1)
  unfold sl25Enc
  omega

theorem sl25Enc_inj : Function.Injective sl25Enc := by
  intro A B h
  obtain ⟨a0, a1, a2, a3⟩ := sl25Enc_digits A
  obtain ⟨b0, b1, b2, b3⟩ := sl25Enc_digits B
  rw [h] at a0 a1 a2 a3
  apply SL25S.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective 5 (a0.symm.trans b0)
  · exact ZMod.val_injective 5 (a1.symm.trans b1)
  · exact ZMod.val_injective 5 (a2.symm.trans b2)
  · exact ZMod.val_injective 5 (a3.symm.trans b3)

theorem sl25Enc_mul (A B : SL25S) : sl25Enc (A * B) = sl25Mul (sl25Enc A) (sl25Enc B) := by
  have e : ∀ i j, ((A * B).val.1 i j).val = ((A.val.1 i 0).val * (B.val.1 0 j).val +
      (A.val.1 i 1).val * (B.val.1 1 j).val) % 5 := by
    intro i j
    rw [SL25S.val_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      ZMod.val_add, ZMod.val_mul, ZMod.val_mul, ← Nat.add_mod]
  obtain ⟨a0, a1, a2, a3⟩ := sl25Enc_digits A
  obtain ⟨b0, b1, b2, b3⟩ := sl25Enc_digits B
  unfold sl25Mul
  simp only [a0, a1, a2, a3, b0, b1, b2, b3]
  unfold sl25Enc
  rw [e 0 0, e 0 1, e 1 0, e 1 1]

@[expose] def sl25Code : CodeM SL25S := ⟨sl25Enc, sl25Mul, sl25Enc_inj, sl25Enc_mul⟩

end CFSG.KD.HN1408

end
