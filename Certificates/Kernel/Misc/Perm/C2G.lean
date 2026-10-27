module

public import Certificates.Kernel.Misc.Perm.C2A
public import Certificates.Kernel.Misc.Perm.C2B
public import Certificates.Kernel.Misc.Perm.C2L0
public import Certificates.Kernel.Misc.Perm.C2L1
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.RankThree.Native.F2ChainLevels
public import CFSG.Certificates.Kernel.Misc.ArrBind

set_option exponentiation.threshold 600

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexFlat CFSG.RankThree.Native.F2
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Co2Cert (co2StrongArrs co2BaseArr)

theorem M22_eq : M22 = 2 ^ 22 - 1 := rfl

theorem L22_eq : L22 = lanes 22 := by decide

theorem I22_eq : I22 = idM 22 := by decide

theorem hvm (v M : ℕ) : vmK v M = vmul 22 v M := vmulK_eq M22_eq v M

theorem hmm (A B : ℕ) : mmK A B = mmul 22 A B := mulK_eq (by norm_num) M22_eq L22_eq A B

theorem V_eq : co2FiveV = unpack 2300 22 (HV.F 0) := by
  have h := hexTable_sound HV.all 0 (by norm_num)
  rw [Nat.mul_zero, ← HV.eq] at h
  exact h

theorem V_size : co2FiveV.size = 2300 := by
  rw [V_eq]
  simp [unpack]

theorem V_get {i : ℕ} (hi : i < 2300) : co2FiveV[i]! = VG i := by
  rw [V_eq, CFSG.KC.Misc.PairCount.unpack_get hi]
  rfl

theorem VG_lt (i : ℕ) : VG i < 2 ^ 22 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hlk {i : ℕ} (hi : i < 2300) : LK (VG i) = i :=
  Nat.eq_of_beq_eq_true (allN_spec vec_ok i hi)

theorem sys : Sys 22 co2FiveV VG LK := by
  refine ⟨by norm_num, nodup_of_lk (LK := LK) ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [V_size] at hi
    rw [V_get hi, hlk hi]
  · intro v hv
    rw [V_eq, unpack, Array.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  · intro i hi
    exact V_get (by rwa [V_size] at hi)
  · intro i hi
    exact hlk (by rwa [V_size] at hi)

theorem foldr_congr {f g : ℕ → ℕ} : ∀ L : List ℕ, (∀ i ∈ L, f i = g i) →
    L.foldr (fun i acc => f i ^^^ acc) 0 = L.foldr (fun i acc => g i ^^^ acc) 0
  | [], _ => rfl
  | i :: L, h => by
    rw [List.foldr_cons, List.foldr_cons, h i List.mem_cons_self,
      foldr_congr L fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem spans : Spans 22 co2FiveV (fun k => spanLists.getD k []) := by
  intro k hk
  have h := allN_spec span_ok k hk
  rw [Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hl : ∀ i ∈ spanLists.getD k [], i < 2300 := fun i hi => by
    have := h1 i hi
    rwa [Nat.blt_eq] at this
  refine ⟨fun i hi => by rw [V_size]; exact hl i hi, ?_⟩
  rw [foldr_congr (g := VG) _ fun i hi => V_get (hl i hi), h2]
  exact Nat.one_shiftLeft k

theorem bind_facts {a : Array ℕ} {P M MI : ℕ} (ha : a = unpack 2300 12 P)
    (h : bindK P M MI = true) :
    Inv 22 co2FiveV M MI ∧ a = permOfMat 22 co2FiveV M ∧ M < 2 ^ (22 * 22) := by
  unfold bindK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hs : a.size = co2FiveV.size := by
    rw [ha, V_size]
    simp [unpack]
  have himg : ∀ i < co2FiveV.size,
      a[i]! < co2FiveV.size ∧ co2FiveV[a[i]!]! = vmul 22 co2FiveV[i]! M := by
    intro i hi
    rw [V_size] at hi ⊢
    have := allN_spec h1 i hi
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    have ea : a[i]! = f12 P i := by
      rw [ha, CFSG.KC.Misc.PairCount.unpack_get hi]
      rfl
    rw [ea, V_get this.1, V_get hi, ← hvm]
    exact this
  obtain ⟨hinv, hp⟩ := inv_of_images (by norm_num) sys.nodup sys.lt hs himg
    (by rw [← hmm, h2, I22_eq]) (by rw [← hmm, h3, I22_eq])
  exact ⟨hinv, hp, lt_of_le_of_lt h4 (by decide)⟩

theorem five_eq {k : ℕ} (hk : k < 38) : co2FiveArr k = unpack 2300 12 (HA.F k) := by
  have h := hexTable3_sound HA.all k hk
  rw [← HA.eq] at h
  exact h

theorem amF {k : ℕ} (hk : k < 38) :
    Inv 22 co2FiveV (AM k) (AMI k) ∧ co2FiveArr k = permOfMat 22 co2FiveV (AM k) ∧
      AM k < 2 ^ (22 * 22) := by
  have h : ∀ k < 19 * 2, bindK (HA.F k) (AM k) (AMI k) = true :=
    allN_of_chunks (c := 19) (n := 2) (f := fun k => bindK (HA.F k) (AM k) (AMI k)) bindA_chunks
  exact bind_facts (five_eq hk) (h k hk)

theorem strong_parts : co2StrongArrs.size = 11 ∧ co2BaseArr = #[0, 1, 2, 3, 5, 4] ∧
    ∀ j < 11, CFSG.KC.Misc.ArrEnum.arrBind co2StrongArrs[j]! 2300 12 (SS j) = true ∧
      bindK (SS j) (MS j) (MSI j) = true := by
  have h := strong_ok
  unfold strongK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, eq_of_beq h2, fun j hj => ?_⟩
  have := allN_spec h3 j hj
  rwa [Bool.and_eq_true] at this

theorem msF {j : ℕ} (hj : j < 11) :
    Inv 22 co2FiveV (MS j) (MSI j) ∧ co2StrongArrs[j]! = permOfMat 22 co2FiveV (MS j) := by
  obtain ⟨h1, h2⟩ := strong_parts.2.2 j hj
  obtain ⟨hi, he, -⟩ := bind_facts (CFSG.KC.Misc.ArrEnum.arrBind_sound h1) h2
  exact ⟨hi, he⟩

theorem base_size : co2BaseArr.size = 6 := by
  rw [strong_parts.2.1]
  rfl

theorem hBS : ∀ i < co2BaseArr.size, co2BaseArr[i]! = BS i := by
  intro i hi
  rw [base_size] at hi
  rw [strong_parts.2.1]
  interval_cases i <;> rfl

theorem hb : ∀ i < co2BaseArr.size, BS i < co2FiveV.size := by
  intro i hi
  rw [base_size] at hi
  rw [V_size]
  interval_cases i <;> decide

theorem rL_eq : ∀ i < 6, rL i = cL i + cL i := by
  intro i hi
  interval_cases i <;> rfl

theorem levK_all : ∀ i < 6, levK i = true := by
  intro i hi
  interval_cases i
  · have h0 := lev0_hd
    unfold levHd0 at h0
    unfold levK levelM
    rw [Bool.and_eq_true] at h0
    rw [h0.1, Bool.true_and, h0.2, Bool.true_and]
    refine allN_of_forall ?_
    exact allN_of_chunks (c := 575) (n := 4) (f := edge0) edge0_chunks
  · exact levK1
  · exact levK2
  · exact levK3
  · exact levK4
  · exact levK5

theorem steps_eq {i : ℕ} (hi : i < 6) :
    (List.range 11).filter (fun j => allN i fun t => Nat.beq (vmK (VG (BS t)) (MS j)) (VG (BS t))) =
      (List.range (cL i)).map (IX i) := by
  have h := levK_all i hi
  unfold levK at h
  rw [Bool.and_eq_true] at h
  exact eq_of_beq h.1

theorem IX_lt {i t : ℕ} (hi : i < 6) (ht : t < cL i) : IX i t < 11 := by
  have hm : IX i t ∈ (List.range (cL i)).map (IX i) := List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩
  rw [← steps_eq hi, List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem lev_levelM {i : ℕ} (hi : i < 6) :
    levelM vmK mmK I22 2300 VG (BS i) (mL i) (rL i) (PT i) (PO i) (PA i) (LB i) (ED i) (SM i)
      (SIM i) (TM i) (TIM i) = true := by
  have h := levK_all i hi
  unfold levK at h
  rw [Bool.and_eq_true] at h
  exact h.2

theorem LF : LevFacts 22 co2FiveV (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr.size mL PT
    PO TM TIM := by
  have h := levFacts_rawLevels sys hvm hmm I22_eq
    (S := co2StrongArrs) (MS := MS) (MSI := MSI)
    (fun j hj => (msF (by rwa [strong_parts.1] at hj)).2)
    (fun j hj => (msF (by rwa [strong_parts.1] at hj)).1) hBS hb (m := mL) (c := cL) (IX := IX)
    (PT := PT) (PO := PO) (PA := PA) (LB := LB) (TM := TM) (TIM := TIM) (ED := ED)
    (fun i hi => by
      rw [base_size] at hi
      have h := levK_all i hi
      unfold levK at h
      rw [Bool.and_eq_true] at h
      rw [strong_parts.1]
      exact h.1)
    (fun i hi => by
      rw [base_size] at hi
      rw [V_size, ← rL_eq i hi]
      exact lev_levelM hi)
  rwa [V_size] at h

end CertificateChecks.KernelMisc.Co2K

end
