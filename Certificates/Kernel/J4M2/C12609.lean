
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRepBase
public import Certificates.Kernel.J4M2.C12609Tabs
public import Certificates.Kernel.J4M2.C12609Lo
public import Certificates.Kernel.J4M2.C12609Hi
public import Certificates.Kernel.J4M2.C12632
public import Certificates.Kernel.J4M2.C12608

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Sporadic.J4.Native CFSG.KC.J4Q
  CFSG.KD.J4Q CFSG.KC.J4RR CFSG.KD.J4RR CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q CertificateChecks.KernelJ4Gam
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.AGLEmbeddingD2.Wilson.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def RepK (x : J) (n : Nat) : Prop :=
  ∃ A : Array V2, WfA A ∧ encR A = n ∧ Mx x = CFSG.Sporadic.J4.rowsMatrix A

theorem RepK.mul {x y : J} {a b : Nat} (hx : RepK x a) (hy : RepK y b) :
    RepK (x * y) (mulJ c rm a b) := by
  obtain ⟨A, hA, eA, mA⟩ := hx
  obtain ⟨B, hB, eB, mB⟩ := hy
  have h := mul_enc hK ⟨hA, eA⟩ ⟨hB, eB⟩
  exact ⟨mulRows A B, h.1, h.2, by rw [map_mul, mA, mB, CFSG.Sporadic.J4.rowsMatrix_mulRows]⟩

theorem RepK.inj {x y : J} {n : Nat} (hx : RepK x n) (hy : RepK y n) : x = y := by
  obtain ⟨A, hA, eA, mA⟩ := hx
  obtain ⟨B, hB, eB, mB⟩ := hy
  apply Mx_injective
  rw [mA, mB, arr_eq hA hB (eA.trans eB.symm)]

theorem repK_one : RepK 1 one :=
  ⟨idRows (), wf_idRows, enc_idRows hK, by rw [map_one, CFSG.Sporadic.J4.rowsMatrix_idRows]⟩

section Elements

theorem repK_z : RepK z0 ZM := ⟨zM, zM_enc.1, zM_enc.2, (rowsMatrix_zM matFacts).symm⟩

theorem repK_gE {j : Nat} (hj : j < 12) : RepK (gE j) (getN one qaL j) :=
  ⟨qM[j]!, (qM_enc hj).1, by rw [qaL_eq]; exact (qM_enc hj).2, by
    rw [qM_get hj]; exact Mx_gE matFacts (by omega)⟩

theorem repK_fold (m : Nat) : ∀ l : List Nat, (∀ j ∈ l, j < 12) → ∀ (x : J) (a : Nat), RepK x a →
    RepK (l.foldl (fun acc j => if m.testBit j then acc * gE j else acc) x)
      (l.foldl (fun acc j => if m.testBit j then mulJ c rm acc (getN one qaL j) else acc) a)
  | [], _, _, _, h => h
  | j :: l, hl, x, a, h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine repK_fold m l (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ _ ?_
    by_cases hb : m.testBit j
    · simp only [hb, ↓reduceIte]
      exact h.mul (repK_gE (hl j List.mem_cons_self))
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact h

theorem repK_eta (m : Nat) : RepK (CFSG.Sporadic.J4.QT.eta gE 12 m) (pK m) :=
  repK_fold m (List.range 12) (fun j hj => List.mem_range.1 hj) 1 one repK_one

theorem eta_split (m : Nat) : CFSG.Sporadic.J4.QT.eta gE 12 m =
    CFSG.Sporadic.J4.QT.eta gE 12 (m % 64) * CFSG.Sporadic.J4.QT.eta gE 12 (64 * (m / 64)) := by
  have e : mulJ c rm (pK (m % 64)) (pK (64 * (m / 64))) = pK m := by
    rw [← (pK_enc _).2, ← (pK_enc _).2, ← (pK_enc _).2, qProd_split m,
      enc_mulRows hK (pK_enc _).1 (pK_enc _).1]
  have h := (repK_eta (m % 64)).mul (repK_eta (64 * (m / 64)))
  rw [e] at h
  exact (repK_eta m).inj h

end Elements

theorem lo_get {a : Nat} (ha : a < 64) : getN 0 LO a = pK a :=
  Nat.eq_of_beq_eq_true (allR_spec rrLo_chk a ha)

theorem hi_get {b : Nat} (hb : b < 64) : getN 0 HI b = pK (64 * b) :=
  Nat.eq_of_beq_eq_true (allR_spec rrHi_chk b hb)

theorem gl_get {g a : Nat} (hg : g < 3) (ha : a < 64) :
    getN 0 (CFSG.KC.J4RR.getL GLs g) a = mulJ c rm (getN 0 rrGs g) (getN 0 LO a) :=
  Nat.eq_of_beq_eq_true (allR_spec (allR_spec rrGl_chk g hg) a ha)

theorem hg_get {g b : Nat} (hg : g < 3) (hb : b < 64) :
    getN 0 (CFSG.KC.J4RR.getL HGs g) b = mulJ c rm (getN 0 HI b) (getN 0 rrGs g) :=
  Nat.eq_of_beq_eq_true (allR_spec (allR_spec rrHg_chk g hg) b hb)

theorem hz_get {g b : Nat} (hg : g < 3) (hb : b < 64) :
    getN 0 (CFSG.KC.J4RR.getL HZs g) b = mulJ c rm (getN 0 (CFSG.KC.J4RR.getL HGs g) b) ZM :=
  Nat.eq_of_beq_eq_true (allR_spec (allR_spec rrHz_chk g hg) b hb)

theorem matQ_eq {m : Nat} (hm : m < 4096) :
    matQ c rm LO HI m = mulJ c rm (pK (m % 64)) (pK (64 * (m / 64))) := by
  change mulJ c rm (getN 0 LO (m % 64)) (getN 0 HI (m / 64)) = _
  rw [lo_get (Nat.mod_lt _ (by omega)), hi_get (by omega)]

theorem encN_eq_pk (A : Array Nat) : encN A = pk A := by
  unfold encN pk
  refine foldr_congr_mem _ _ fun i _ x => ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

section Gens

theorem repK_genEl {g : Nat} (hg : g < 3) : RepK (genEl g) (getN 0 rrGs g) := by
  have h := gam_rows_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hZ⟩, -⟩, -⟩, -⟩ := h
  interval_cases g
  · exact ⟨gamAFwd.map natV2, (natRows_enc _ hA).1, (natRows_enc _ hA).2.trans (encN_eq_pk _),
      Mx_genEl 0⟩
  · exact ⟨gamBFwd.map natV2, (natRows_enc _ hB).1, (natRows_enc _ hB).2.trans (encN_eq_pk _),
      Mx_genEl 1⟩
  · exact ⟨gamZFwd.map natV2, (natRows_enc _ hZ).1, (natRows_enc _ hZ).2.trans (encN_eq_pk _),
      Mx_genEl 2⟩

theorem z_comm_genEl {g : Nat} (hg : g < 3) : z0 * genEl g = genEl g * z0 := by
  have h := Nat.eq_of_beq_eq_true (allR_spec rrZg_chk g hg)
  have h1 := repK_z.mul (repK_genEl hg)
  rw [h] at h1
  exact h1.inj ((repK_genEl hg).mul repK_z)

end Gens

@[expose] noncomputable def zb (b : Bool) : J := if b then z0 else 1

theorem zb_comm {y : J} (hy : z0 * y = y * z0) : ∀ b, zb b * y = y * zb b
  | true => hy
  | false => by simp [zb]

theorem zb_z :
    ∀ b, zb b * z0 = zb (!b)
  | true => z0_mul_self matFacts
  | false => by simp [zb]

theorem nfOf_eq (k : Nat) :
    nfOf k = zb (decide (4096 ≤ k)) * CFSG.Sporadic.J4.QT.eta gE 12 (k % 4096) := rfl

theorem z_comm_eta
    (m : Nat) :
    z0 * CFSG.Sporadic.J4.QT.eta gE 12 m = CFSG.Sporadic.J4.QT.eta gE 12 m * z0 :=
  (RRepNF.eta_commute nfHyp_gE 12 le_rfl m).eq

theorem root_alg {a R P z : J} (haR : a * R = R * a) (hzP : z * P = P * z) :
    a * (R * P * z) = R * (a * z * P) := by
  calc a * (R * P * z) = a * R * (P * z) := by simp only [mul_assoc]
    _ = R * a * (z * P) := by rw [haR, hzP]
    _ = R * (a * z * P) := by simp only [mul_assoc]

theorem step_alg {a G P z : J} (hzG : z * G = G * z) (hzP : z * P = P * z) :
    a * (P * G * z) = a * z * P * G := by
  rw [mul_assoc P G z, ← hzG, ← mul_assoc P z G, ← hzP]
  simp only [mul_assoc]

theorem rMask_lt {i : Nat} (hi : i < 7) : getN 0 rMaskK i < 64 := by
  interval_cases i <;> decide

theorem rrMask_mem {k : Nat} (hk : k < 4) :
    getN 0 rrMaskK k ∈ q8Masks ∧ getN 0 rrMaskK k < 4096 := by
  interval_cases k <;> decide

theorem rRep_eta {i : Nat} (hi : i < 7) :
    rRep ⟨i, hi⟩ = CFSG.Sporadic.J4.QT.eta gE 12 (getN 0 rMaskK i) := by
  rw [getN_eq_getD]
  interval_cases i <;>
    simp (config := { decide := true }) [rRep, rMaskK, CFSG.Sporadic.J4.QT.eta, List.range_succ]

section Tree

theorem repK_matQ {m : Nat} (hm : m < 4096) :
    RepK (CFSG.Sporadic.J4.QT.eta gE 12 m) (matQ c rm LO HI m) := by
  rw [matQ_eq hm, eta_split m]
  exact (repK_eta _).mul (repK_eta _)

theorem root_good {idx rest : Nat} (hidx : idx < 8192) (h : rootK c rm ZM LO HI idx rest = true) :
    Good (nfOf idx) := by
  unfold rootK at h
  rw [CFSG.KC.J4Q.strictB_eq, CFSG.KC.J4Q.strictB_eq] at h
  change andB (Nat.blt rest 56) (Nat.beq (matQ c rm LO HI (idx % 4096))
    (zIf c rm ZM (notB (Nat.beq (idx / 4096) (rest % 8 / 4)))
      (mulJ c rm (getN 0 LO (getN 0 rMaskK (rest / 8)))
        (matQ c rm LO HI (getN 0 rrMaskK (rest % 8 % 4)))))) = true at h
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hlt, heq⟩ := h
  have h56 : rest < 56 := lt_of_blt hlt
  have hi : rest / 8 < 7 := by omega
  obtain ⟨hmem, hm'⟩ := rrMask_mem (k := rest % 8 % 4) (by omega)
  have hm : idx % 4096 < 4096 := Nat.mod_lt _ (by omega)
  have hR0 : RepK (rRep ⟨rest / 8, hi⟩) (getN 0 LO (getN 0 rMaskK (rest / 8))) := by
    rw [rRep_eta hi, lo_get (rMask_lt hi)]
    exact repK_eta _
  have hR := hR0.mul (repK_matQ hm')
  have hL := repK_matQ hm
  have hc : zb (decide (4096 ≤ idx)) * rRep ⟨rest / 8, hi⟩ =
      rRep ⟨rest / 8, hi⟩ * zb (decide (4096 ≤ idx)) := by
    rw [rRep_eta hi]
    exact zb_comm (z_comm_eta _) _
  cases hb : Nat.beq (idx / 4096) (rest % 8 / 4) <;> rw [hb] at heq
  ·
    change Nat.beq (matQ c rm LO HI (idx % 4096)) (mulJ c rm (mulJ c rm
      (getN 0 LO (getN 0 rMaskK (rest / 8))) (matQ c rm LO HI (getN 0 rrMaskK (rest % 8 % 4))))
      ZM) = true at heq
    rw [Nat.eq_of_beq_eq_true heq] at hL
    have e := hL.inj (hR.mul repK_z)
    refine ⟨⟨rest / 8, hi⟩, 1, C0p.one_mem,
      qNF (!decide (4096 ≤ idx)) (getN 0 rrMaskK (rest % 8 % 4)), ⟨_, _, hmem, rfl⟩, ?_⟩
    rw [one_mul, inv_one, mul_one, nfOf_eq, e, root_alg hc (z_comm_eta _), zb_z]
    rfl
  ·
    change Nat.beq (matQ c rm LO HI (idx % 4096)) (mulJ c rm
      (getN 0 LO (getN 0 rMaskK (rest / 8))) (matQ c rm LO HI (getN 0 rrMaskK (rest % 8 % 4))))
      = true at heq
    rw [Nat.eq_of_beq_eq_true heq] at hL
    have e := hL.inj hR
    refine ⟨⟨rest / 8, hi⟩, 1, C0p.one_mem,
      qNF (decide (4096 ≤ idx)) (getN 0 rrMaskK (rest % 8 % 4)), ⟨_, _, hmem, rfl⟩, ?_⟩
    rw [one_mul, inv_one, mul_one, nfOf_eq, e, ← mul_assoc, hc, mul_assoc]
    rfl

theorem step_spec {idx d rest : Nat} (hidx : idx < 8192)
    (h : stepK c rm LO HI GLs HGs HZs E idx d rest = true) :
    rest % 4 < 3 ∧ rest / 4 < 8192 ∧ isQ8K (rest / 4 % 4096) = false ∧ depE E (rest / 4) + 1 = d ∧
      genEl (rest % 4) * nfOf idx = nfOf (rest / 4) * genEl (rest % 4) := by
  unfold stepK at h
  rw [CFSG.KC.J4Q.strictB_eq, CFSG.KC.J4Q.strictB_eq] at h
  change andB (Nat.blt (rest % 4) 3) (andB (Nat.blt (rest / 4) 8192)
    (andB (notB (isQ8K (rest / 4 % 4096))) (andB (Nat.beq (Nat.succ (depE E (rest / 4))) d)
      (strictB (idx % 4096) fun m => strictB (rest / 4 % 4096) fun m' =>
        Nat.beq (mulJ c rm (getN 0 (CFSG.KC.J4RR.getL GLs (rest % 4)) (m % 64))
            (getN 0 HI (m / 64)))
          (mulJ c rm (getN 0 LO (m' % 64))
            (getN 0 (CFSG.KC.J4RR.getL (Bool.rec (motive := fun _ => List (List Nat)) HZs HGs
              (Nat.beq (idx / 4096) (rest / 4 / 4096))) (rest % 4)) (m' / 64))))))) = true at h
  rw [CFSG.KC.J4Q.strictB_eq, CFSG.KC.J4Q.strictB_eq] at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hg, hnx, hq8, hdep, heq⟩ := h
  have hg' : rest % 4 < 3 := lt_of_blt hg
  have hnx' : rest / 4 < 8192 := lt_of_blt hnx
  have hq8' : isQ8K (rest / 4 % 4096) = false := by
    rw [notB_eq] at hq8
    simpa using hq8
  have hdep' : depE E (rest / 4) + 1 = d := Nat.eq_of_beq_eq_true hdep
  refine ⟨hg', hnx', hq8', hdep', ?_⟩
  generalize rest % 4 = g at hg' heq ⊢
  generalize rest / 4 = nx at hnx' heq ⊢
  have hm : idx % 4096 < 4096 := Nat.mod_lt _ (by omega)
  have hm' : nx % 4096 < 4096 := Nat.mod_lt _ (by omega)
  have hG := repK_genEl hg'
  have hL : RepK (genEl g * CFSG.Sporadic.J4.QT.eta gE 12 (idx % 4096))
      (mulJ c rm (getN 0 (CFSG.KC.J4RR.getL GLs g) (idx % 4096 % 64))
        (getN 0 HI (idx % 4096 / 64))) := by
    rw [gl_get hg' (by omega), lo_get (by omega), hi_get (by omega), eta_split (idx % 4096),
      ← mul_assoc]
    exact (hG.mul (repK_eta _)).mul (repK_eta _)
  have hP : RepK (CFSG.Sporadic.J4.QT.eta gE 12 (nx % 4096) * genEl g)
      (mulJ c rm (getN 0 LO (nx % 4096 % 64))
        (getN 0 (CFSG.KC.J4RR.getL HGs g) (nx % 4096 / 64))) := by
    rw [hg_get hg' (by omega), lo_get (by omega), hi_get (by omega), eta_split (nx % 4096),
      mul_assoc]
    exact (repK_eta _).mul ((repK_eta _).mul hG)
  have hPz : RepK (CFSG.Sporadic.J4.QT.eta gE 12 (nx % 4096) * genEl g * z0)
      (mulJ c rm (getN 0 LO (nx % 4096 % 64))
        (getN 0 (CFSG.KC.J4RR.getL HZs g) (nx % 4096 / 64))) := by
    rw [hz_get hg' (by omega), hg_get hg' (by omega), lo_get (by omega), hi_get (by omega),
      eta_split (nx % 4096)]
    have h1 := (repK_eta (nx % 4096 % 64)).mul
      (((repK_eta (64 * (nx % 4096 / 64))).mul hG).mul repK_z)
    simpa only [mul_assoc] using h1
  have hzG := z_comm_genEl hg'
  have hzP := z_comm_eta (nx % 4096)
  rw [nfOf_eq, nfOf_eq, ← mul_assoc, ← zb_comm hzG, mul_assoc]
  by_cases h1 : 4096 ≤ idx <;> by_cases h2 : 4096 ≤ nx
  · have ed : Nat.beq (idx / 4096) (nx / 4096) = true := Nat.beq_eq_true_eq _ _ ▸ (by omega)
    rw [ed] at heq
    rw [Nat.eq_of_beq_eq_true heq] at hL
    rw [hL.inj hP, decide_eq_true h1, decide_eq_true h2, mul_assoc]
  · have ed : Nat.beq (idx / 4096) (nx / 4096) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      have := Nat.eq_of_beq_eq_true hb
      omega
    rw [ed] at heq
    rw [Nat.eq_of_beq_eq_true heq] at hL
    rw [hL.inj hPz, step_alg hzG hzP, decide_eq_true h1, decide_eq_false h2, zb_z]
    rfl
  · have ed : Nat.beq (idx / 4096) (nx / 4096) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      have := Nat.eq_of_beq_eq_true hb
      omega
    rw [ed] at heq
    rw [Nat.eq_of_beq_eq_true heq] at hL
    rw [hL.inj hPz, step_alg hzG hzP, decide_eq_false h1, decide_eq_true h2, zb_z]
    rfl
  · have ed : Nat.beq (idx / 4096) (nx / 4096) = true := Nat.beq_eq_true_eq _ _ ▸ (by omega)
    rw [ed] at heq
    rw [Nat.eq_of_beq_eq_true heq] at hL
    rw [hL.inj hP, decide_eq_false h1, decide_eq_false h2, mul_assoc]

theorem rrIdx_all {idx : Nat} (h : idx < 8192) : rrIdx idx = true := by
  have e : 128 * (idx / 128) + idx % 128 = idx := Nat.div_add_mod idx 128
  have hb : rrBlk (idx / 128) = true := by
    by_cases hlo : idx / 128 < 32
    · exact RRL.all (idx / 128) hlo
    · have hle : 32 ≤ idx / 128 := by omega
      have hlt : idx / 128 - 32 < 32 := by omega
      have h0 := RRH.all (idx / 128 - 32) hlt
      have e2 : rrBlkHi (idx / 128 - 32) = rrBlk (idx / 128) :=
        congrArg rrBlk (Nat.add_sub_cancel' hle)
      exact e2 ▸ h0
  have hb' : rrBlkK c rm ZM LO HI GLs HGs HZs E (idx / 128) = true := hb
  unfold rrBlkK at hb'
  have h2 := allR_spec hb' (idx % 128) (Nat.mod_lt _ (by omega))
  change rrIdxK c rm ZM LO HI GLs HGs HZs E (128 * (idx / 128) + idx % 128) = true at h2
  rw [e] at h2
  exact h2

theorem good_of : ∀ n idx : Nat, idx < 8192 → depE E idx = n → isQ8K (idx % 4096) = false →
    Good (nfOf idx) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro idx hidx hdep hq8
    have h := rrIdx_all hidx
    unfold rrIdx rrIdxK at h
    rw [CFSG.KC.J4Q.strictB_eq, CFSG.KC.J4Q.strictB_eq, CFSG.KC.J4Q.strictB_eq] at h
    change orB (isQ8K (idx % 4096)) (Bool.rec (motive := fun _ => Bool)
      (stepK c rm LO HI GLs HGs HZs E idx (entE E idx % 16) (entE E idx / 16))
      (rootK c rm ZM LO HI idx (entE E idx / 16)) (Nat.beq (entE E idx % 16) 0)) = true at h
    rw [hq8, orB_eq, Bool.false_or] at h
    cases hd : Nat.beq (entE E idx % 16) 0 <;> rw [hd] at h
    · change stepK c rm LO HI GLs HGs HZs E idx (entE E idx % 16) (entE E idx / 16) = true at h
      obtain ⟨hg, hnx, hq8', hdep', hEq⟩ := step_spec hidx h
      have hlt : depE E (entE E idx / 16 / 4) < n := by
        rw [← hdep]
        change depE E (entE E idx / 16 / 4) < entE E idx % 16
        omega
      obtain ⟨i, w, hw, q, hq, hcj⟩ := ih _ hlt _ hnx rfl hq8'
      refine ⟨i, w * genEl (entE E idx / 16 % 4), C0p.mul_mem hw (genEl_mem _), q, hq, ?_⟩
      rw [@conj_step' J (Subgroup.toGroup J) _ _ _ _ hEq]
      exact hcj
    · change rootK c rm ZM LO HI idx (entE E idx / 16) = true at h
      exact root_good hidx h

open Certificates in
open CFSG.AGLEmbeddingD2.Wilson.Coordinator in
theorem c12609 : ∀ p ∈ CFSG.Quasithin.J4M2.Qgrp, p ∉ Q8set →
    ∃ i : Fin 7, ∃ w ∈ C0p, ∃ q ∈ Q8set, w * p * w⁻¹ = rRep i * q := by
  intro p hp hpq
  obtain ⟨e, m, hm, rfl⟩ := mem_Qgrp_nf hp
  have hq8 : isQ8K m = false := by
    by_contra hne
    apply hpq
    have h : isQ8K m = true := by simpa using hne
    unfold isQ8K at h
    simp only [orB_eq, Bool.or_eq_true] at h
    refine ⟨e, m, ?_, rfl⟩
    rcases h with h | h | h | h <;> rw [Nat.eq_of_beq_eq_true h] <;> decide
  have key : ∀ idx, idx < 8192 → idx % 4096 = m → decide (4096 ≤ idx) = e →
      Good (qNF e m) := by
    intro idx h1 h2 h3
    have := good_of _ idx h1 rfl (by rw [h2]; exact hq8)
    rwa [nfOf, h2, h3] at this
  cases e
  · exact key m (by omega) (Nat.mod_eq_of_lt hm) (decide_eq_false (by omega))
  · exact key (4096 + m) (by omega) (by omega) (decide_eq_true (by omega))

end Tree

end CertificateChecks.KernelJ4M2

end
