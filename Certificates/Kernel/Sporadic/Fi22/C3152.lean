
module

public import Certificates.Kernel.Sporadic.Fi22.F3152Lines
public import Certificates.Kernel.Sporadic.Fi22.F3152PullA
public import Certificates.Kernel.Sporadic.Fi22.F3152PullB
public import Certificates.Kernel.Sporadic.Fi22.F3152Small
public import Certificates.Kernel.Sporadic.Fi22.F3152Sep
public import CFSG.Certificates.Kernel.F3152.FormSound
public import CFSG.Certificates.Kernel.F3152.SortSound
public import Certificates.Kernel.Fi22Core.Matrix
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3152

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.F3152 CFSG.Monster.B.Fischer CFSG.Monster.B.Fischer.Native
open CFSG.KS.Raw CFSG.KC.Enum CFSG.Monster.B.Co2.Native CertificateChecks.KernelFi22C

theorem parLt_true {n chunks : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    parLt n chunks p = true := by
  unfold parLt
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  change allLt (n / chunks + 1) (fun k => !(decide (c * (n / chunks + 1) + k < n)) ||
    p (c * (n / chunks + 1) + k)) = true
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun k _ => ?_
  by_cases hk : c * (n / chunks + 1) + k < n
  · simp [h _ hk]
  · simp [hk]

theorem any_of {n : Nat} {f : (i : Nat) → i < n → Bool} {i : Nat} (hi : i < n) (h : f i hi = true) :
    Nat.any n f = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

theorem wfM_of_rowsWF {X : Array V} (h : RowsWF X) : wfM X = true := by
  unfold wfM
  rw [Array.all_eq_true]
  intro i hi
  have := h i
  rwa [getElem!_pos X i hi] at this

@[expose] noncomputable def NL (r : Nat) : Nat := (T.CH.getD r (0, 0)).1

theorem ch_line {r : Nat} (hr : r < 3510) :
    ∃ N, T.CH[r]? = some (N, 752) ∧ lineOK (SL r) N = true := by
  have hc : r / 54 < 65 := by omega
  have h : linesK SL 54 (dropK (54 * (r / 54)) T.CH) (54 * (r / 54)) = true := Lines.all (r / 54) hc
  obtain ⟨N, h1, h2⟩ := linesK_spec h (r % 54) (Nat.mod_lt _ (by norm_num))
  rw [dropK_eq, List.getElem?_drop] at h1
  rw [Nat.div_add_mod] at h1 h2
  exact ⟨N, h1, h2⟩

theorem ch_get {r : Nat} (hr : r < 3510) :
    T.CH[r]? = some ((T.CH.getD r (0, 0)).1, 752) ∧ lineOK (SL r) (T.CH.getD r (0, 0)).1 = true := by
  obtain ⟨N, h1, h2⟩ := ch_line hr
  have e : (T.CH.getD r (0, 0)).1 = N := by
    rw [List.getD_eq_getElem?_getD, h1]
    rfl
  rw [e]
  exact ⟨h1, h2⟩

theorem ch_len : T.CH.length = 3510 := by
  have h := tail_ok
  rw [nilK_iff, dropK_eq, List.drop_eq_nil_iff] at h
  have h' : T.CH.length ≤ 3510 := h
  obtain ⟨N, h1, -⟩ := ch_line (r := 3509) (by norm_num)
  have := (List.getElem?_eq_some_iff.1 h1).1
  omega

theorem forms_get {r m : Nat} (hr : r < 3510) (hm : m < 752) :
    (fi22FormsBytes.get! (752 * r + m)).toNat = (NL r >>> (8 * m)) % 256 := by
  unfold fi22FormsBytes
  rw [T.eq]
  exact text_get ch_len (fun r hr => ch_get hr) hr hm

theorem polar_eq {r : Nat} (hr : r < 3510) : polarRows fi22FormsBytes (752 * r) = unlane 77 (SL r) :=
  polar_of_line (ch_get hr).2 (fun _ hm => forms_get hr hm)

theorem ti_get : TI.CH.length = 1 ∧ (∀ r < 1, TI.CH[r]? = some ((TI.CH.getD r (0, 0)).1, 752) ∧
    lineOK ((fun _ => SL 3510) r) (TI.CH.getD r (0, 0)).1 = true) := by
  have h := inv_line
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [nilK_iff, dropK_eq, List.drop_eq_nil_iff] at h2
  have h2' : TI.CH.length ≤ 1 := h2
  obtain ⟨N, e1, e2⟩ := linesK_spec h1 0 (by norm_num)
  have hl := (List.getElem?_eq_some_iff.1 e1).1
  refine ⟨by omega, fun r hr => ?_⟩
  have e0 : r = 0 := by omega
  subst e0
  have e : (TI.CH.getD 0 (0, 0)).1 = N := by
    rw [List.getD_eq_getElem?_getD, e1]
    rfl
  rw [e]
  exact ⟨e1, e2⟩

theorem polar_inv : polarRows fi22InvFormBytes 0 = unlane 77 (SL 3510) := by
  have hl := (ti_get.2 0 (by norm_num)).2
  refine polar_of_line hl (fun m hm => ?_)
  have := text_get (S := fun _ => SL 3510) ti_get.1 ti_get.2 (r := 0) (by norm_num) hm
  rw [Nat.mul_zero] at this
  unfold fi22InvFormBytes
  rw [TI.eq]
  exact this

theorem GL_eq {k : Nat} (hk : k < 2) : CertificateChecks.KernelSpor.F3152.GL k = Fi22CGT.F k := by
  interval_cases k
  · exact Nat.eq_of_beq_eq_true (by quickRfl)
  · exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem gen_get {k r : Nat} (hk : k < 2) (hr : r < 3510) :
    (fi22ChainGen k)[r]! = (CertificateChecks.KernelSpor.F3152.GL k >>> (12 * r)) &&& 4095 := by
  rw [Fi22G.gen_eq hk, GL_eq hk]
  unfold unpack
  rw [getElem!_pos _ r (by rw [Array.size_ofFn]; exact hr), Array.getElem_ofFn]
  rfl

theorem pullA_at {r : Nat} (hr : r < 3510) :
    (CertificateChecks.KernelSpor.F3152.GL 0 >>> (12 * r)) &&& 4095 < 3510 ∧
    mulK (SL 3512) (mulK (SL ((CertificateChecks.KernelSpor.F3152.GL 0 >>> (12 * r)) &&& 4095)) LA) =
      SL r := by
  have hc : r / 54 < 65 := by omega
  have h : pullK (SL 3512) LA (CertificateChecks.KernelSpor.F3152.GL 0) SL 54 (54 * (r / 54)) = true :=
    PullA.all (r / 54) hc
  have := pullK_spec h (r % 54) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at this
  exact this

theorem pullB_at {r : Nat} (hr : r < 3510) :
    (CertificateChecks.KernelSpor.F3152.GL 1 >>> (12 * r)) &&& 4095 < 3510 ∧
    mulK (SL 3513) (mulK (SL ((CertificateChecks.KernelSpor.F3152.GL 1 >>> (12 * r)) &&& 4095)) LB) =
      SL r := by
  have hc : r / 54 < 65 := by omega
  have h : pullK (SL 3513) LB (CertificateChecks.KernelSpor.F3152.GL 1) SL 54 (54 * (r / 54)) = true :=
    PullB.all (r / 54) hc
  have := pullK_spec h (r % 54) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at this
  exact this

theorem tr_eqs : trLane 77 LA = SL 3512 ∧ trLane 77 LB = SL 3513 := by
  have h := tr_ok
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨eqV_iff.1 h.1, eqV_iff.1 h.2⟩

theorem action_of {k : Nat} (hk : k < 2) {A : Array V} {LAx LAt : V} (hA : A = unlane 77 LAx)
    (hw : LAx.wf = true) (htr : trLane 77 LAx = LAt)
    (hpull : ∀ r < 3510, (CertificateChecks.KernelSpor.F3152.GL k >>> (12 * r)) &&& 4095 < 3510 ∧
      mulK LAt (mulK (SL ((CertificateChecks.KernelSpor.F3152.GL k >>> (12 * r)) &&& 4095)) LAx) =
        SL r) :
    actionOK fi22FormsBytes (fi22ChainGen k) A 4 = true := by
  unfold actionOK
  dsimp only
  apply parLt_true
  intro r hr
  obtain ⟨h1, h2⟩ := hpull r hr
  rw [gen_get hk hr, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, pullback_of_lanes hA hw htr (polar_eq h1) (polar_eq hr) h2⟩

theorem action_ok :
    actionOK fi22FormsBytes (fi22ChainGen 0) CFSG.Sporadic.Fi22.Native.matA 4 = true ∧
    actionOK fi22FormsBytes (fi22ChainGen 1) CFSG.Sporadic.Fi22.Native.matB 4 = true :=
  ⟨action_of (by norm_num) matA_eq canons.1.wf tr_eqs.1 fun _ hr => pullA_at hr,
    action_of (by norm_num) matB_eq canons.2.1.wf tr_eqs.2 fun _ hr => pullB_at hr⟩

theorem inv_ok :
    pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matA
      (transpose 77 CFSG.Sporadic.Fi22.Native.matA) = true ∧
    pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matB
      (transpose 77 CFSG.Sporadic.Fi22.Native.matB) = true := by
  have h := inv_pull
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨pullback_of_lanes matA_eq canons.1.wf tr_eqs.1 polar_inv polar_inv (eqV_iff.1 h.1),
    pullback_of_lanes matB_eq canons.2.1.wf tr_eqs.2 polar_inv polar_inv (eqV_iff.1 h.2)⟩

theorem lane_eq_of_trits {r r' : Nat} (hr : r < 3510) (hr' : r' < 3510)
    (h : ∀ i < 77, ∀ j < 77, i ≤ j →
      trit fi22FormsBytes (752 * r) (pairIdx i j) = trit fi22FormsBytes (752 * r') (pairIdx i j)) :
    SL r = SL r' := by
  have l1 := (ch_get hr).2
  have l2 := (ch_get hr').2
  have hF : toMat 77 (formRows fi22FormsBytes (752 * r)) = toMat 77 (formRows fi22FormsBytes (752 * r')) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [toMat_apply, toMat_apply, formRows_val _ _ hi hj, formRows_val _ _ hi hj]
    by_cases hij : i ≤ j
    · rw [ite_eq_left hij, ite_eq_left hij, h i hi j hj hij]
    · rw [ite_eq_right hij, ite_eq_right hij]
  have hM : toMat 77 (unlane 77 (SL r)) = toMat 77 (unlane 77 (SL r')) := by
    rw [← polar_eq hr, ← polar_eq hr', toMat_polarRows, toMat_polarRows, hF]
  have hU := eq_of_canonM (canonM_unlane 77 (lineOK_wf l1)) (canonM_unlane 77 (lineOK_wf l2)) hM
  have e : (77 * 77 : Nat) = 5929 := rfl
  have b1 := lineOK_lt l1
  have b2 := lineOK_lt l2
  rw [← e] at b1 b2
  exact unlane_inj b1.1 b1.2 b2.1 b2.2 hU

theorem any2_of {f g : Nat → Nat}
    (h : (∀ i < 77, ∀ j < 77, i ≤ j → f (pairIdx i j) = g (pairIdx i j)) → False) :
    (Nat.any 77 fun i _ => Nat.any 77 fun j _ =>
      decide (i ≤ j) && f (pairIdx i j) != g (pairIdx i j)) = true := by
  by_contra hne
  apply h
  intro i hi j hj hij
  by_contra hd
  apply hne
  apply any_of hi
  apply any_of hj
  rw [decide_eq_true hij, Bool.true_and, bne_iff_ne]
  exact hd

theorem distinct_ok : distinctOK fi22FormsBytes 4 = true := by
  unfold distinctOK
  apply parLt_true
  intro r hr
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro r' hr'
  refine any2_of (f := trit fi22FormsBytes (752 * r)) (g := trit fi22FormsBytes (752 * r'))
    fun hall => ?_
  · have hS := lane_eq_of_trits hr (by omega) hall
    have l2 := (ch_get (r := r') (by omega)).2
    rw [← hS] at l2
    have hN := lineOK_inj (ch_get hr).2 l2
    have hnd := nodup_of_sortedK sorted_ok
    obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.1 (ch_get hr).1
    obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.1 (ch_get (r := r') (by omega)).1
    have hne : r ≠ r' := by omega
    apply hne
    refine (List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact h1)
      (hj := by rw [List.length_map]; exact h2)).1 ?_
    rw [List.getElem_map, List.getElem_map, e1, e2]
    exact hN

theorem rowsK_spec {L : V} : ∀ (l : List V) (i n : Nat), rowsK L l i n = true →
    ∀ t (ht : t < l.length), l[t] = blk 77 L (i + t)
  | [], _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | x :: l, i, n, h, t, ht => by
    change Bool.rec (motive := fun _ => Bool) false (rowsK L l (Nat.succ i) (Nat.pred n))
      (eqV x (blk 77 L i)) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases t with _ | t
    · rw [List.getElem_cons_zero, eqV_iff.1 h.1, Nat.add_zero]
    · rw [List.getElem_cons_succ, rowsK_spec l _ _ h.2 t (by simpa using ht)]
      congr 1
      omega

theorem bi_size : fi22Bi.size = 77 := rfl

theorem bi_eq : fi22Bi = unlane 77 (SL 3511) := by
  apply Array.ext (by rw [bi_size, unlane_size])
  intro t h1 h2
  have ht : t < 77 := by rwa [bi_size] at h1
  rw [← getElem!_pos (unlane 77 (SL 3511)) t h2, unlane_get _ ht, ← Array.getElem_toList]
  rw [rowsK_spec _ 0 77 bi_rows t (by rw [Array.length_toList]; exact h1), Nat.zero_add]

theorem bi_wf : wfM fi22Bi = true := by
  rw [CFSG.KS.F3R.wfM_eq]
  decide +kernel

theorem bi_inv : eqM 77 (mul 77 (polarRows fi22InvFormBytes 0) fi22Bi) (idM 77) = true := by
  have h := bi_id
  rw [bAnd_eq, Bool.and_eq_true] at h
  have e : mulLane 77 (spreadE 77 77) (SL 3510) (SL 3511) = LI := (eqV_iff.1 h.1).trans (eqV_iff.1 h.2)
  rw [polar_inv, bi_eq, mul_unlane (by norm_num), idM_eq, e]
  exact eqM_self (unlane_size _ _)

theorem sep_mats : fi22SepMats = (SepL.map (unlane 77)).toArray := by
  have e1 : fi22CentralizerIdx = [0, 1, 2, 3, 4, 10] := rfl
  have e2 : SepL = [0, 1, 2, 3, 4, 10].map (fun r => mulK (SL 3511) (SL r)) := rfl
  unfold fi22SepMats
  rw [e1, e2, List.map_toArray, List.map_map]
  apply congrArg List.toArray
  apply List.map_congr_left
  intro r hr
  have hr' : r < 3510 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  rw [Function.comp_apply, bi_eq, polar_eq hr', mul_unlane (by norm_num)]
  rfl

theorem sep_ok : sepOK 77 fi22SepMats fi22SepTerms fi22SepVec fi22SepK fi22SepP fi22SepTinv
    fi22SepTree = true := by
  have hd : 0 < 77 := by norm_num
  have hwf := sep_wf
  rw [Bool.and_eq_true, List.all_eq_true] at hwf
  obtain ⟨hW, hLs⟩ := hwf
  have hlen : SepL.length = 6 := rfl
  have hv : fi22SepVec.p < 2 ^ 77 ∧ fi22SepVec.m < 2 ^ 77 := by decide
  have hsz : (SepL.map (unlane 77)).toArray.size = 6 := by
    rw [List.size_toArray, List.length_map, hlen]
  have hmw : (SepL.map (unlane 77)).toArray.all wfM = true := by
    rw [Array.all_eq_true]
    intro i hi
    rw [List.getElem_toArray, List.getElem_map]
    exact wfM_of_rowsWF (rowsWF_unlane (hLs _ (List.getElem_mem _)))
  rw [sep_mats]
  unfold sepOK
  rw [combM_unlane hd idM_eq SepL fi22SepTerms (by rw [hlen]; decide),
    spinVecs_lane hd hLs hv.1 hv.2 fi22SepTree (by rw [hlen]; decide)]
  dsimp only
  have eW : combL 77 (spreadE 77 77) LI SepL fi22SepTerms = SepW := rfl
  have eS : spinL 77 (List.map (trLane 77) SepL) fi22SepVec fi22SepTree = SepS := rfl
  rw [eW, eS, mulVec_unlane hd hW hv.1 hv.2, hmw, hsz, CFSG.KS.F3R.mul_eq, CFSG.KS.F3R.mul_eq,
    CFSG.KS.F3R.eqM_eq, CFSG.KS.F3R.eqM_eq, CFSG.KS.F3R.wfM_eq, CFSG.KS.F3R.wfM_eq]
  have s := sep_small
  simp only [Bool.and_eq_true] at s
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩ := s
  have sp := sep_spin
  rw [Bool.and_eq_true] at sp
  rw [s1, s2, s3, s4, s5, s6, s7, s8, sep_zero, sep_proj, s9, s10, sp.1, sp.2]
  rfl

end CertificateChecks.KernelSpor.F3152

namespace CertificateChecks.KernelSpor.F3152

open CFSG.F3.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Fischer.Native

theorem facts3152 :
    distinctOK fi22FormsBytes 4 = true ∧
    actionOK fi22FormsBytes (fi22ChainGen 0) CFSG.Sporadic.Fi22.Native.matA 4 = true ∧
    actionOK fi22FormsBytes (fi22ChainGen 1) CFSG.Sporadic.Fi22.Native.matB 4 = true ∧
    pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matA
      (transpose 77 CFSG.Sporadic.Fi22.Native.matA) = true ∧
    pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matB
      (transpose 77 CFSG.Sporadic.Fi22.Native.matB) = true ∧
    wfM fi22Bi = true ∧ fi22Bi.size = 77 ∧
    eqM 77 (mul 77 (polarRows fi22InvFormBytes 0) fi22Bi) (idM 77) = true ∧
    sepOK 77 fi22SepMats fi22SepTerms fi22SepVec fi22SepK fi22SepP fi22SepTinv
      fi22SepTree = true :=
  ⟨distinct_ok, action_ok.1, action_ok.2, inv_ok.1, inv_ok.2, bi_wf, bi_size, bi_inv, sep_ok⟩

end CertificateChecks.KernelSpor.F3152

end
