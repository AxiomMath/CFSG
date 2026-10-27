module

public import Certificates.Kernel.J4NP7850.Sound
public import Certificates.Kernel.J4NP7850.ChecksQ
public import Certificates.Kernel.J4NP7850.ChecksNE
public import Certificates.Kernel.J4Q.Orb
public import CFSG.Sporadic.J4.QT2LocFixMain
public import CFSG.Certificates.Kernel.J4Q.VOrbTree

public section

namespace CertificateChecks.KernelJ4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4M4F CFSG.KD.J4NP7850 CFSG.KS.J4NP7850

theorem vecJ_comb {B : List Nat} {M : Nat} (hB : ∀ t < 6, vecJ rm (B.getD t 0) M = B.getD t 0) :
    ∀ n ≤ 6, ∀ s, vecJ rm (combK B n s) M = combK B n s
  | 0, _, _ => vecJ_zero M
  | n + 1, hn, s => by
    rw [combK_succ]
    split
    · rw [vecJ_xor, vecJ_comb hB n (by omega) s, hB n (by omega)]
    · exact vecJ_comb hB n (by omega) s

theorem comb_bit {B P : List Nat} (hB : ∀ t < 6, ∀ s < 6, (B.getD t 0).testBit (P.getD s 0) = decide (s = t))
    {s : Nat} (hs : s < 6) (σ : Nat) :
    ∀ n ≤ 6, (combK B n σ).testBit (P.getD s 0) = (decide (s < n) && σ.testBit s)
  | 0, _ => by
    have e : combK B 0 σ = 0 := rfl
    rw [e]
    simp
  | n + 1, hn => by
    rw [combK_succ]
    have ih := comb_bit hB hs σ n (by omega)
    split
    · rename_i hσ
      rw [Nat.testBit_xor, ih, hB n (by omega) s hs]
      rcases Nat.lt_trichotomy s n with h | rfl | h
      · simp [h, Nat.ne_of_lt h, Nat.lt_succ_of_lt h]
      · simp [hσ]
      · have h1 : ¬ s < n := by omega
        have h2 : ¬ s < n + 1 := by omega
        simp [h1, h2, Nat.ne_of_gt h]
    · rename_i hσ
      rw [ih]
      rcases Nat.lt_trichotomy s n with h | rfl | h
      · simp [h, Nat.lt_succ_of_lt h]
      · simp [hσ]
      · have h1 : ¬ s < n := by omega
        have h2 : ¬ s < n + 1 := by omega
        simp [h1, h2]

@[expose] noncomputable def idxP (P : List Nat) (z : Nat) : Nat :=
  xsum (fun s => if z.testBit (P.getD s 0) then 2 ^ s else 0) 6

theorem idxP_bit (P : List Nat) (z : Nat) :
    ∀ n i, (xsum (fun s => if z.testBit (P.getD s 0) then 2 ^ s else 0) n).testBit i =
      (decide (i < n) && z.testBit (P.getD i 0))
  | 0, i => by simp [xsum]
  | n + 1, i => by
    rw [xsum_succ, Nat.testBit_xor, idxP_bit P z n i]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · split <;> simp [h, Nat.lt_succ_of_lt h, Nat.testBit_two_pow, Nat.ne_of_gt h]
    · split <;> simp_all [Nat.testBit_two_pow]
    · have h1 : ¬ i < n := by omega
      have h2 : ¬ i < n + 1 := by omega
      split <;> simp [h1, h2, Nat.testBit_two_pow, Nat.ne_of_lt h]

theorem idxP_lt (P : List Nat) (z : Nat) : idxP P z < 2 ^ 6 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  unfold idxP
  rw [idxP_bit]
  have : ¬ i < 6 := by omega
  simp [this]

theorem fix_comb {z : Nat} (hz : z < 2 ^ 112) (hfix : ∀ j < 10, vecJ rm z (FM7850.getD j one) = z) :
    ∃ σ < 2 ^ 6, z = combK b 6 σ := by
  obtain ⟨hP, hB⟩ := basisK_spec c7850_basis
  have hB1 : ∀ t < 6, ∀ s < 6, (b.getD t 0).testBit (P.getD s 0) = decide (s = t) :=
    fun t ht => (hB t ht).2.2
  refine ⟨idxP P z, idxP_lt P z, ?_⟩
  have hc0 : ∀ n ≤ 6, ∀ s, combK b n s < 2 ^ 112 := by
    intro n
    induction n with
    | zero => intro _ s; exact Nat.two_pow_pos 112
    | succ n ih =>
      intro hn s
      rw [combK_succ]
      split
      · exact Nat.xor_lt_two_pow (ih (by omega) s) (hB n (by omega)).1
      · exact ih (by omega) s
  have hc : ∀ s, combK b 6 s < 2 ^ 112 := hc0 6 le_rfl
  have key : z ^^^ combK b 6 (idxP P z) = 0 := by
    refine rankK_spec c7850_rank c7850_q (Nat.xor_lt_two_pow hz (hc _)) (fun j hj => ?_) ?_
    · rw [vecJ_xor, hfix j hj,
        vecJ_comb (fun t ht => (hB t ht).2.1 j hj) 6 le_rfl]
    · intro p hp
      obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hp
      have hs6 : s < 6 := by
        have := Nat.eq_of_beq_eq_true c7850_Plen
        omega
      rw [← List.getD_eq_getElem _ 0 hs, Nat.testBit_xor, comb_bit hB1 hs6 _ 6 le_rfl]
      unfold idxP
      rw [idxP_bit]
      simp [hs6]
  have := congrArg (· ^^^ combK b 6 (idxP P z)) key
  simpa [Nat.xor_assoc] using this

section Fix

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Quasithin.KGC31.J4M4 CertificateChecks.KernelJ4Q Matrix

theorem FM_eq : FM7850 = CertificateChecks.KernelJ4M4F.FMs := rfl

theorem U4_eq : getN one Us 4 = U4 := rfl

theorem eta16_eq : eta uJ 11 16 = uJ 4 := by
  have e : (16 : Nat) = 2 ^ 4 := rfl
  rw [e]
  exact eta_two_pow (by norm_num)

theorem Mx_gJ (hM : MatFacts) :
    Mx gJ = rowsMatrix (wordRows baseMats baseInvs CFSG.Quasithin.KGC31.J4M4.gWord) :=
  Mx_wordProd_baseJ hM CFSG.Quasithin.KGC31.J4M4.gWord

theorem duad_eq (hM : MatFacts) :
    gJ * eta fJn 10 420 * gJ⁻¹ = eta uJ 11 16 := by
  have hd := duadK_spec c7850_duad
  have hg := G7850_enc
  have hf := CFSG.KS.J4M4F.fRows_enc hK CertificateChecks.KernelJ4M4F.fTab_enc 420
  have hu := uTab_enc 4 (by rw [Us_length]; norm_num)
  have e1 : mulRows (wordRows baseMats baseInvs CFSG.Quasithin.KGC31.J4M4.gWord)
      (fRows (fTab ()) 420) =
      mulRows ((uTab (locMats ()) (locInvs ()))[4]?.getD (idRows ()))
        (wordRows baseMats baseInvs CFSG.Quasithin.KGC31.J4M4.gWord) := by
    apply eqRows_iff.mp
    rw [eqRows_eq (wf_mulRows hg.1 hf.1) (wf_mulRows hu.1 hg.1), enc_mulRows hK hg.1 hf.1,
      enc_mulRows hK hu.1 hg.1, hg.2, hf.2, hu.2, U4_eq, ← FM_eq, hd]
    exact Nat.beq_refl _
  have hE : Mx (eta fJn 10 420) = rowsMatrix (fRows (fTab ()) 420) := Mx_eta_fJ hM 10 le_rfl 420
  have e2 : gJ * eta fJn 10 420 = uJ 4 * gJ := by
    apply Mx_injective
    rw [map_mul, map_mul, Mx_gJ hM, hE, Mx_uJ hM (by norm_num), ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows, e1]
  rw [e2, mul_inv_cancel_right, eta16_eq]

theorem conj_eta_fix {y : Row} (hfix : ∀ j < 10, (gJ * fJn j * gJ⁻¹) • y = y) :
    ∀ n ≤ 10, ∀ c0, (gJ * eta fJn n c0 * gJ⁻¹) • y = y
  | 0, _, c0 => by
    have e : eta fJn 0 c0 = 1 := rfl
    rw [e, mul_one, mul_inv_cancel, one_smul]
  | n + 1, hn, c0 => by
    rw [eta_succ]
    have e : gJ * (eta fJn n c0 * (if c0.testBit n then fJn n else 1)) * gJ⁻¹ =
        (gJ * eta fJn n c0 * gJ⁻¹) * (gJ * (if c0.testBit n then fJn n else 1) * gJ⁻¹) := by
      group
    rw [e, mul_smul]
    split
    · rw [hfix n (by omega), conj_eta_fix hfix n (by omega) c0]
    · rw [mul_one, mul_inv_cancel, one_smul, conj_eta_fix hfix n (by omega) c0]

theorem act_one_one : act 1 (act 1 1) = 16 := by decide

theorem dlt_code (hM : MatFacts) {ℓ cap : Nat} (hℓ : ℓ < 7) {CH SPC : List (List Nat)}
    (hsize : sizeK cap CH SPC = true)
    (hin : ∀ i < (pchK rm (repK ℓ) CH).length,
      inSK ((pchK rm (repK ℓ) CH).getD i []) SPC.flatten = true)
    (hsp : ∀ i < SPC.length, spInK (SPC.getD i []) (pchK rm (repK ℓ) CH) = true)
    (hcl : ∀ i < (pchK rm (repK ℓ) CH).length,
      clB rm (rep 1 128 1024) [L0, L1, L2] ((pchK rm (repK ℓ) CH).getD i []) SPC.flatten = true)
    {v : Row} (hv : v ∈ Dlt ℓ) : ∃ x < 2 ^ 112, v = rowN x ∧ x ∈ SPC.flatten := by
  have hmem := VOrbTree.checked_membership
    (forall_mem_of_getD (f := fun pc => inSK pc SPC.flatten) hin)
    (forall_mem_of_getD (f := fun sc => spInK sc (pchK rm (repK ℓ) CH)) hsp)
  have hAP : (pchK rm (repK ℓ) CH).flatten = vptsK rm (repK ℓ) CH.flatten := by
    simp only [pchK, List.flatten_cons, List.singleton_append, vptsK, List.map_flatten]
  let S : Set Row := {w | ∃ x < 2 ^ 112, w = rowN x ∧ x ∈ SPC.flatten}
  have h0 : QT2.rep ℓ ∈ S := by
    obtain ⟨hw, hr⟩ := pathVec_enc (repPaths.getD ℓ [])
    have hlt := v2N_lt112 hw
    refine ⟨v2N (pathVec (repPaths.getD ℓ [])), hlt, ?_, ?_⟩
    · rw [rowN_v2N hlt, rep_toVec hM hℓ]
    · apply (hmem _).mp
      rw [hAP, hr]
      exact List.mem_cons_self
  have hstep : ∀ g ∈ ({xJ 0, xJ 1, xJ 2} : Set J), ∀ w ∈ S, g⁻¹ • w ∈ S := by
    intro g hg w hw
    obtain ⟨k, hk, rfl⟩ : ∃ k < 3, g = xJ k := by
      rcases hg with h | h | h
      · exact ⟨0, by norm_num, h⟩
      · exact ⟨1, by norm_num, h⟩
      · exact ⟨2, by norm_num, h⟩
    obtain ⟨x, hx, rfl, hxS⟩ := hw
    obtain ⟨lw, le⟩ := loc_gens k
    obtain ⟨v1, v2⟩ := vecJ_vec lw hx
    refine ⟨vecJ rm x (encR ((locMats ())[k]?.getD (idRows ()))), v1, ?_, ?_⟩
    · apply ofRow_inj.mp
      rw [xJ_inv_smul hM]
      exact v2.symm
    · have hxP : x ∈ (pchK rm (repK ℓ) CH).flatten := (hmem x).mpr hxS
      obtain ⟨pc, hpc, hxpc⟩ := List.mem_flatten.mp hxP
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpc
      have hcl' := hcl i hi
      rw [List.getD_eq_getElem _ _ hi] at hcl'
      have hall : ∀ pc ∈ pchK rm (repK ℓ) CH, pc.length ≤ 1024 := by
        have h4 : CH.all (fun ch => Nat.ble ch.length 1024) = true := by
          simp only [sizeK, CFSG.KC.J4Q.andB_eq, Bool.and_eq_true] at hsize
          exact hsize.2.2.2.1
        intro pc hpc'
        simp only [pchK, List.mem_cons, List.mem_map] at hpc'
        rcases hpc' with rfl | ⟨ch, hch, rfl⟩
        · rw [List.length_singleton]
          omega
        · rw [List.length_map]
          exact Nat.le_of_ble_eq_true (List.all_eq_true.1 h4 ch hch)
      have hlen := hall _ hpc
      have hk3 : k < [CFSG.KD.J4Q.L0, CFSG.KD.J4Q.L1, CFSG.KD.J4Q.L2].length := by simpa using hk
      have h1 := clB_sound (consts_c hK).2 hlen hcl' x hxpc _ (List.getElem_mem hk3)
      have e : [CFSG.KD.J4Q.L0, CFSG.KD.J4Q.L1, CFSG.KD.J4Q.L2][k]'hk3 =
          getN one [CFSG.KD.J4Q.L0, CFSG.KD.J4Q.L1, CFSG.KD.J4Q.L2] k := by
        rw [getN_eq, List.getD_eq_getElem _ _ hk3]
      rw [e, ← le] at h1
      exact h1
  obtain ⟨h, hh, rfl⟩ := hv
  exact smul_mem_of_inv_gens hstep h hh _ h0

theorem fix_code
    (hF : J4Facts) {x : J}
    (hfix : ∀ j < 10, (gJ * fJn j * gJ⁻¹) • (x • w₀) = x • w₀) :
    ∃ x0 < 2 ^ 112, x • w₀ = rowN x0 ∧
      (x0 = v2N rootV ∨ x0 ∈ SPC5.flatten ∨ x0 ∈ SPC6.flatten) := by
  have hM := hF.mat
  have h16 : eta uJ 11 16 • (x • w₀) = x • w₀ := by
    rw [← duad_eq hM]
    exact conj_eta_fix hfix 10 le_rfl 420
  have hl : (1 : ℤ) ∈ letters := by decide
  obtain ⟨h, hh⟩ : ∃ h : J, h = XJ 1 * XJ 1 := ⟨_, rfl⟩
  have hhH : h ∈ Hj := by
    rw [hh]
    exact Hj.mul_mem (XJ_mem hl) (XJ_mem hl)
  have hc : h * eta uJ 11 1 * h⁻¹ = eta uJ 11 16 := by
    have e : h * eta uJ 11 1 * h⁻¹ = XJ 1 * (XJ 1 * eta uJ 11 1 * (XJ 1)⁻¹) * (XJ 1)⁻¹ := by
      rw [hh]
      group
    rw [e, hX_all hM hl, hX_all hM hl, act_one_one]
  have h1 : eta uJ 11 1 • ((h⁻¹ * x) • w₀) = (h⁻¹ * x) • w₀ := by
    have e : eta uJ 11 1 = h⁻¹ * eta uJ 11 16 * h := by
      rw [← hc]
      group
    have e2 : h⁻¹ * eta uJ 11 16 * h * (h⁻¹ * x) = h⁻¹ * (eta uJ 11 16 * x) := by group
    rw [e, smul_smul, e2, mul_smul, mul_smul, h16, mul_smul]
  have hrw : v2N rootV < 2 ^ 112 := v2N_lt112 CertificateChecks.KernelJ4M4F.rootV_wf7253
  have hxe : x • w₀ = h • ((h⁻¹ * x) • w₀) := by
    rw [← mul_smul, mul_inv_cancel_left]
  rcases fix2B_subset hF one_mem_tMasks h1 with e | ⟨h2, hh2, e⟩ | ⟨h2, hh2, e⟩
  · refine ⟨v2N rootV, hrw, ?_, Or.inl rfl⟩
    rw [hxe, e, smul_root_of_mem_Hj hM hhH, rowN_v2N hrw]
    rfl
  · have hd : x • w₀ ∈ Dlt 5 := ⟨h * h2, Hj.mul_mem hhH hh2, by rw [hxe, e, mul_smul]⟩
    obtain ⟨x0, hx0, hv, hm⟩ := dlt_code hM (ℓ := 5) (CH := CH5) (SPC := SPC5) (by norm_num) size5
      (inSK_chunks (SQ := SQ5) I5.all) (spInK_chunks (SQ := SQ5) rfl I5.all S5.all) C5.all hd
    exact ⟨x0, hx0, hv, Or.inr (Or.inl hm)⟩
  · have hd : x • w₀ ∈ Dlt 6 := ⟨h * h2, Hj.mul_mem hhH hh2, by rw [hxe, e, mul_smul]⟩
    obtain ⟨x0, hx0, hv, hm⟩ := dlt_code hM (ℓ := 6) (CH := CH6) (SPC := SPC6) (by norm_num) size6
      (inSK_chunks (SQ := SQ6) I6.all) (spInK_chunks (SQ := SQ6) rfl I6.all S6.all) C6.all hd
    exact ⟨x0, hx0, hv, Or.inr (Or.inr hm)⟩

theorem ne_of_all {S : List (List Nat)} (h : (S.all fun ch => !ch.isEmpty) = true) :
    ∀ ch ∈ S, ch ≠ [] := by
  intro ch hch e
  have := List.all_eq_true.mp h ch hch
  rw [e] at this
  exact Bool.noConfusion this

theorem fix_sound
    (hF : J4Facts) :
    ∀ x : J, (∀ j < 10, (gJ * fJn j * gJ⁻¹) • (x • w₀) = x • w₀) →
      ∃ k < 31, x • w₀ = gJ • kwRow k := by
  intro x hfix
  have hM := hF.mat
  obtain ⟨x0, hx0, hy, hcase⟩ := fix_code hF hfix
  have hg := G7850_enc
  have hz := inv_smul_rowN (g := gJ) (Mx_gJ hM) hg.1 hx0
  have hzl := (vecJ_vec hg.1 hx0).1
  rw [hg.2] at hz hzl
  set z := vecJ rm x0 G7850 with hzdef
  have hzfix : ∀ j < 10, vecJ rm z (FM7850.getD j one) = z := by
    intro j hj
    obtain ⟨hw, he⟩ := CertificateChecks.KernelJ4M4F.fTab_enc j hj
    have h1 := inv_smul_rowN (g := fJn j) (Mx_fJn hM hj) hw hzl
    have hsq : fJn j * fJn j = 1 := (fJ_basis hM chkF_true).sq ⟨j, hj⟩
    have hinv : (fJn j)⁻¹ = fJn j := inv_eq_of_mul_eq_one_right hsq
    have h2 : fJn j • (gJ⁻¹ • (x • w₀)) = gJ⁻¹ • (x • w₀) := by
      have := hfix j hj
      rw [mul_smul, mul_smul] at this
      rw [← smul_left_cancel_iff gJ, this, smul_inv_smul]
    rw [hy, hz, ← hinv, h1] at h2
    have h3 := (vecJ_vec hw hzl).1
    rw [FM_getD hj, ← he]
    exact rowN_inj h3 hzl h2
  obtain ⟨σ, hσ, hzσ⟩ := fix_comb hzl hzfix
  have hpos : x0 ≠ 0 := by
    rcases hcase with e | hm | hm
    · rw [e]
      decide +kernel
    · exact Nat.ne_of_gt ((VOrbTree.sincK_spec sinc5).2 x0 hm)
    · exact Nat.ne_of_gt ((VOrbTree.sincK_spec sinc6).2 x0 hm)
  rcases σ with _ | s
  · exfalso
    rw [combK_zero] at hzσ
    have h0 := inv_smul_rowN (g := gJ) (Mx_gJ hM) hg.1 (Nat.two_pow_pos 112)
    rw [vecJ_zero] at h0
    have h1 : gJ⁻¹ • rowN x0 = gJ⁻¹ • rowN 0 := by rw [hz, hzσ, h0]
    exact hpos (rowN_inj hx0 (Nat.two_pow_pos 112) (smul_left_cancel _ h1))
  · have hs : s < 63 := by
      have : s + 1 < 64 := hσ
      omega
    rcases spanK_spec c7850_span s hs with hm | hm
    · obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.mp hm
      have hk31 : k < 31 := by
        have hl : KW7850.length = 31 := by rfl
        omega
      have e' : KW7850.getD k 0 = z := by rw [List.getD_eq_getElem _ _ hk, e, hzσ]
      refine ⟨k, hk31, ?_⟩
      obtain ⟨-, hkl, -⟩ := pi_sound hM k hk31
      rw [hy, ← inv_smul_eq_iff, hz, ← e', kw_getD, rowN_v2N (by rw [← kw_getD]; exact hkl)]
      rfl
    · exfalso
      obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hm
      have hi32 : i < 32 := by
        have := Nat.eq_of_beq_eq_true c7850_ulen
        omega
      have hq := othVK_spec c7850_othV i hi32
      have hql : q.getD i 0 < 2 ^ 112 := by
        have := allR_iff.mp c7850_qlt i hi32
        have e1 : Nat.shiftLeft 1 112 = 2 ^ 112 := Nat.one_shiftLeft 112
        rw [getN_eq, Nat.blt_eq, e1] at this
        exact this
      have h1 := inv_smul_rowN (g := gJ) (Mx_gJ hM) hg.1 hql
      rw [hg.2, hq, List.getD_eq_getElem _ _ hi, e, ← hzσ, ← hz] at h1
      have hqx : q.getD i 0 = x0 := rowN_inj hql hx0 (smul_left_cancel _ h1)
      have hne := c7850_ne
      rw [Bool.and_eq_true] at hne
      obtain ⟨hr, h5, h6⟩ := othSK_spec (ne_of_all hne.1) (ne_of_all hne.2)
        (VOrbTree.sincK_spec sinc5).1 (VOrbTree.sincK_spec sinc6).1 c7850_othS i hi32
      rw [hqx] at hr h5 h6
      rcases hcase with e | hm | hm
      · exact hr e
      · exact h5 hm
      · exact h6 hm

end Fix

end CertificateChecks.KernelJ4NP7850

end
