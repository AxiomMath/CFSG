module

public import Certificates.Kernel.Fi22Cent.Checks
public import Certificates.Kernel.Fi22Core.Conj
public import Certificates.Kernel.T46K.Letters
public import Certificates.Data.CFSGNative.Fi22.Centralizer
public import Certificates.Kernel.Fi22.Letters
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 42200

namespace CertificateChecks.KernelFi22Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22Cent CFSG.KS.Fi22L CFSG.KS.TW CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelFi22C

theorem ea_facts : (∀ i < 693, 0 < EAK i ∧ EAK i < 3510 ∧ gA (EAK i) = EAK i ∧ EPK (EAK i) = i) ∧
    ∀ i < 692, EAK i < EAK (i + 1) := by
  have h := ea_ok
  unfold eaK at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := Raw.Orb.allN_iff.1 h.1 i hi
    simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    exact h1
  · have h2 := Raw.Orb.allN_iff.1 h.2 i hi
    simpa [Nat.blt_eq] using h2

theorem ep_facts {x : Nat} (hx : x < 3510) :
    (EPK x < 693 ∧ EAK (EPK x) = x) ∨ (EPK x = 693 ∧ (x = 0 ∨ gA x ≠ x)) := by
  have h := Raw.Orb.allN_iff.1 ep_ok x hx
  rw [Raw.Orb.strictB_eq, Raw.Orb.bIf_eq] at h
  by_cases hm : EPK x < 693
  · rw [ite_eq_left (Eq.mpr Nat.blt_eq hm)] at h
    exact Or.inl ⟨hm, Nat.eq_of_beq_eq_true h⟩
  · rw [ite_eq_right (show ¬(Nat.blt (EPK x) 693 = true) from fun hb => hm (Nat.blt_eq.mp hb)),
      Raw.Orb.bAnd_eq, Bool.and_eq_true,
      Raw.Orb.bIf_eq] at h
    refine Or.inr ⟨Nat.eq_of_beq_eq_true h.1, ?_⟩
    by_cases h0 : x = 0
    · exact Or.inl h0
    · rw [ite_eq_right (fun hb => h0 (Nat.eq_of_beq_eq_true hb))] at h
      right
      intro e
      rw [e, Nat.beq_refl] at h
      exact absurd h.2 (by decide)

theorem EAK_mono {i j : Nat} (hij : i < j) (hj : j < 693) : EAK i < EAK j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans (ea_facts.2 j (by omega))
    · exact ea_facts.2 i (by omega)

theorem gA_eq {k : Nat} (hk : k < 3510) : ap orbL.alpha k = gA k := (alpha_get hk).1

theorem gA_lt {k : Nat} (hk : k < 3510) : gA k < 3510 := (alpha_get hk).2

@[expose] noncomputable def EAL : List Nat := (List.range 693).map EAK

theorem EAL_pairwise : EAL.Pairwise (· < ·) := by
  unfold EAL
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro i j hi hj hij
  exact EAK_mono hij (List.mem_range.1 hj)

theorem e_toList : (eaPts orbL).toList = EAL := by
  unfold eaPts
  rw [List.toList_toArray]
  refine List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _) EAL_pairwise fun x => ?_
  rw [List.mem_filter, List.mem_range]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨hx, hx0, hxa⟩
    rw [gA_eq hx] at hxa
    rcases ep_facts hx with ⟨hm, he⟩ | ⟨-, h0 | h0⟩
    · exact List.mem_map.2 ⟨EPK x, List.mem_range.2 hm, he⟩
    · exact absurd h0 hx0
    · exact absurd hxa h0
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2, h3, -⟩ := ea_facts.1 i (List.mem_range.1 hi)
    exact ⟨h2, by omega, by rw [gA_eq h2]; exact h3⟩

theorem e_size : (eaPts orbL).size = 693 := by
  rw [← Array.length_toList, e_toList, EAL, List.length_map, List.length_range]

theorem e_get {i : Nat} (hi : i < 693) : (eaPts orbL)[i]! = EAK i := by
  rw [getElem!_pos _ i (by rw [e_size]; exact hi), ← Array.getElem_toList]
  simp only [e_toList, EAL, List.getElem_map, List.getElem_range]

theorem p_get {x : Nat} (hx : x < 3510) : (ePos (eaPts orbL))[x]! = EPK x := by
  unfold ePos
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, e_toList]
  simp only
  have hnd : EAL.Nodup := EAL_pairwise.imp ne_of_lt
  rcases ep_facts hx with ⟨hm, he⟩ | ⟨hm, h0⟩
  · have hl : EPK x < EAL.length := by simp [EAL, hm]
    have e1 : EAL[EPK x] = x := by simp [EAL, he]
    have := List.get_idxOf hnd ⟨EPK x, hl⟩
    simp only [List.get_eq_getElem, e1] at this
    exact this
  · rw [hm]
    have hn : x ∉ EAL := by
      intro hmem
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hmem
      have := (ea_facts.1 i (List.mem_range.1 hi)).2.2.2
      rw [hm] at this
      have := List.mem_range.1 hi
      omega
    rw [List.idxOf_eq_length hn]
    simp [EAL]

theorem EAK_lt {i : Nat} (hi : i < 693) : EAK i < 3510 := (ea_facts.1 i hi).2.1

theorem EPK_EAK {i : Nat} (hi : i < 693) : EPK (EAK i) = i := (ea_facts.1 i hi).2.2.2

theorem phi_facts {i : Nat} (hi : i < 693) : PHK i < 693 ∧ PIK i < 693 ∧ PIK (PHK i) = i ∧
    PHK (PIK i) = i := by
  have h := Raw.Orb.allN_iff.1 phi_ok i hi
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem phiData_length : phiData.toList.length = 693 := by
  rw [Array.length_toList]
  rfl

theorem phi_get {i : Nat} (hi : i < 693) : phiData[i]! = PHK i := by
  have := CertificateChecks.KernelT46.eqLF_spec _ 0 phd_ok i (by rw [phiData_length]; exact hi)
  rw [Nat.zero_add] at this
  rw [CFSG.KS.PC.getElem!_eq_getD, this]

theorem phiPos_get {u : Nat} (hu : u < 693) : (phiPos ())[u]! = PIK u := by
  unfold phiPos
  rw [getElem!_pos _ u (by simpa using hu), Array.getElem_ofFn]
  simp only
  have hget : ∀ i (hi : i < phiData.toList.length), phiData.toList[i] = PHK i := by
    intro i hi
    have := phi_get (by rw [phiData_length] at hi; exact hi)
    rw [getElem!_pos phiData i (by rw [← Array.length_toList]; exact hi)] at this
    rw [Array.getElem_toList]
    exact this
  have hnd : phiData.toList.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b e
    simp only [List.get_eq_getElem, hget] at e
    have ha : a.val < 693 := lt_of_lt_of_eq a.isLt phiData_length
    have hb : b.val < 693 := lt_of_lt_of_eq b.isLt phiData_length
    apply Fin.ext
    rw [← (phi_facts ha).2.2.1, ← (phi_facts hb).2.2.1, e]
  have hp := phi_facts hu
  have hl : PIK u < phiData.toList.length := by rw [phiData_length]; exact hp.2.1
  have e1 : phiData.toList[PIK u] = u := by rw [hget _ hl, hp.2.2.2]
  have := List.get_idxOf hnd ⟨PIK u, hl⟩
  simp only [List.get_eq_getElem, e1] at this
  exact this

theorem ap_compT {n : Nat} (P Q : Table) {x : Nat} (hx : x < n) :
    ap (compT n P Q) x = ap P (ap Q x) := by
  unfold compT
  rw [CFSG.Sporadic.Th.ap_ofFn _ hx]
  rfl

theorem bi_get {x : Nat} (hx : x < 3510) : ap (genTables orbL (-2)) x = gBi x ∧ gBi x < 3510 := by
  have e : genTables orbL (-2) = invT 3510 orbL.beta := by
    unfold genTables
    simp
  rw [e]
  exact ((tr_binv CertificateChecks.KernelFi22.Letters.gen_ok).2 x hx)

theorem uF_succ (f k y : Nat) : uF (f + 1) k y =
    if k = 0 then y else (if labK k = 1 then gA else gB) (uF f (parK k) y) := by
  change nIf(Nat.beq k 0, y, strictN (uF f (parK k) y) fun z =>
    nIf(Nat.beq (labK k) 1, gA z, gB z)) = _
  rw [TW.strictN_eq']
  by_cases h0 : k = 0
  · subst h0
    rfl
  · rw [ite_eq_right h0]
    have e : Nat.beq k 0 = false :=
      Bool.eq_false_iff.2 fun hb => h0 (Nat.eq_of_beq_eq_true hb)
    rw [e]
    by_cases hl : labK k = 1
    · rw [ite_eq_left hl, hl]
      rfl
    · rw [ite_eq_right hl]
      have e2 : Nat.beq (labK k) 1 = false :=
        Bool.eq_false_iff.2 fun hb => hl (Nat.eq_of_beq_eq_true hb)
      rw [e2]

theorem uInvF_succ (f k x : Nat) : uInvF (f + 1) k x =
    if k = 0 then x else uInvF f (parK k) (if labK k = 1 then gA x else gBi x) := by
  change nIf(Nat.beq k 0, x, uInvF f (parK k) (nIf(Nat.beq (labK k) 1, gA x, gBi x))) = _
  by_cases h0 : k = 0
  · subst h0
    rfl
  · rw [ite_eq_right h0]
    have e : Nat.beq k 0 = false :=
      Bool.eq_false_iff.2 fun hb => h0 (Nat.eq_of_beq_eq_true hb)
    rw [e]
    by_cases hl : labK k = 1
    · rw [ite_eq_left hl, hl]
      rfl
    · rw [ite_eq_right hl]
      have e2 : Nat.beq (labK k) 1 = false :=
        Bool.eq_false_iff.2 fun hb => hl (Nat.eq_of_beq_eq_true hb)
      rw [e2]

theorem lk_big {T y : Nat} (hT : T < 2 ^ 42120) (hy : 3510 ≤ y) : lk T y = 0 := by
  unfold lk
  have h : Nat.shiftRight T (Nat.mul 12 y) = 0 := by
    change T >>> (12 * y) = 0
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [h]
  rfl

theorem tM_lt (x : Nat) : Nat.land x tM < 2 ^ 42120 := by
  change x &&& wM 42120 < 2 ^ 42120
  rw [wM_eq]
  exact Nat.and_lt_two_pow x (by omega)

theorem ap_big {t : Table} {y : Nat} (ht : t.size = 3510) (hy : 3510 ≤ y) : ap t y = 0 := by
  unfold ap
  rw [getElem!_neg t y (by omega)]
  rfl

theorem ap_alpha (y : Nat) : ap orbL.alpha y = gA y := by
  by_cases hy : y < 3510
  · exact gA_eq hy
  · have e : orbL.alpha = orbTab 0 := rfl
    rw [e, ap_big (orbTab_size 0) (by omega)]
    exact (lk_big (tM_lt _) (by omega)).symm

theorem ap_beta (y : Nat) : ap orbL.beta y = gB y := by
  by_cases hy : y < 3510
  · exact (beta_get hy).1
  · have e : orbL.beta = orbTab 1 := rfl
    rw [e, ap_big (orbTab_size 1) (by omega)]
    exact (lk_big (tM_lt _) (by omega)).symm

theorem ap_bi (y : Nat) : ap (genTables orbL (-2)) y = gBi y := by
  by_cases hy : y < 3510
  · exact (bi_get hy).1
  · have hs : (genTables orbL (-2)).size = 3510 := by
      have e : genTables orbL (-2) = invT 3510 orbL.beta := by
        unfold genTables
        simp
      rw [e]
      exact (tr_binv CertificateChecks.KernelFi22.Letters.gen_ok).1
    rw [ap_big hs (by omega)]
    exact (lk_big (tM_lt _) (by omega)).symm

theorem cTab_fuel : ∀ f k, k < f → k < 3510 → ∀ x < 3510,
    ap (cTab orbL (genTables orbL (-2)) k) x = uF f k (gA (uInvF f k x)) := by
  intro f
  induction f with
  | zero => intro k hk; omega
  | succ f ih =>
    intro k hkf hk x hx
    rw [cTab.eq_def, uF_succ, uInvF_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [lt_irrefl, false_and, dite_false, ↓reduceIte]
      exact gA_eq hx
    · obtain ⟨-, -, -, ht⟩ := tree_facts hk
      obtain ⟨hpar, hlab⟩ := ht hk0
      have hpa : ap orbL.par k = parK k := ap_tab 2 hk
      have hlb : ap orbL.lab k = labK k := ap_tab 3 hk
      have hk0' : k ≠ 0 := by omega
      rw [dite_eq_left ⟨hk0, by rw [hpa]; exact hpar⟩, ite_eq_right hk0', ite_eq_right hk0', hpa, hlb]
      have hpk : parK k < k := hpar
      have hpf : parK k < f := by omega
      have hp3 : parK k < 3510 := by omega
      rcases hlab with ⟨hl, -⟩ | ⟨hl, -⟩
      · change labK k = 1 at hl
        rw [hl]
        simp only [beq_self_eq_true, ite_true]
        rw [ap_compT _ _ hx, ap_compT _ _ (by rw [ap_alpha]; exact gA_lt hx), ap_alpha, ap_alpha,
          ih _ hpf hp3 _ (gA_lt hx)]
      · change labK k = 2 at hl
        rw [hl]
        simp only [show ((2 : Nat) == 1) = false from rfl, show ¬((2 : Nat) = 1) from by decide,
          ite_false, Bool.false_eq_true]
        rw [ap_compT _ _ hx, ap_compT _ _ (by rw [ap_bi]; exact (bi_get hx).2), ap_beta, ap_bi,
          ih _ hpf hp3 _ (bi_get hx).2]

theorem cTab_eq {k x : Nat} (hk : k < 3510) (hx : x < 3510) :
    ap (cTab orbL (genTables orbL (-2)) k) x = cK k x := by
  rw [cTab_fuel 3510 k hk hk x hx]
  unfold cK
  rw [TW.strictN_eq']

end CertificateChecks.KernelFi22Cent

end
