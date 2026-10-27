module

public import Certificates.Kernel.HS4062.G
public import Certificates.Kernel.HS4062.E
public import Certificates.Kernel.HS4062.P
public import Certificates.Kernel.E16.List

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS4062.H

open CFSG.KD.HS4062 CFSG.KC.Kc3K CFSG.KC.Enum CFSG.KD.E16 CFSG.KD.E16L
open CFSG.Sporadic.Schreier (hsP)

@[expose, reducible] noncomputable def D : CFSG.KD.E16.Data where
  n := 3850
  w := 12
  m := 4095
  NN := 203
  NE := 512
  M := 87
  R := 9
  e0 := 2
  TF := TF
  B := B
  gs := GS
  eu := eu
  ev := ev
  ky := ky
  iv := iv
  kv := kv
  tg := tg
  vu := vu
  vv := vv
  rt := rt
  cj := cj
  RI := RI
  FR := FR
  FL := FL
  FM := FM
  pr := pr
  ct := ct
  NB := NB
  NM := NM

theorem chunk {len : Nat} (hl : 0 < len) (i : Nat) :
    Nat.add (Nat.mul (i / len) len) (i % len) = i ∧ i % len < len := by
  refine ⟨?_, Nat.mod_lt _ hl⟩
  change i / len * len + i % len = i
  rw [Nat.mul_comm]
  exact Nat.div_add_mod i len

theorem famE_at {k : Nat} (hk : k < 512) :
    (elK 12 4095 203 512 87 TF B GS eu ev ky iv kv tg k &&
      elQ 512 2 3 ky tg QR k) = true := by
  have hc : k / 64 < 8 := by omega
  have h := CFSG.KD.HS4062.E.all (k / 64) hc
  unfold famE at h
  have := List.all_eq_true.1 h (k % 64) (List.mem_range.2 (chunk (by norm_num) k).2)
  rwa [(chunk (by norm_num) k).1] at this

theorem famI_at {i : Nat} (hi : i < 87) :
    (ivK 12 4095 512 87 9 TF B eu ev ky kv vu vv rt cj RI FR FL FM i &&
      ivX 12 4095 TF B vu vv i) = true := by
  have hc : i / 32 < 3 := by omega
  have h := CFSG.KD.HS4062.I.all (i / 32) hc
  unfold famI at h
  have := List.all_eq_true.1 h (i % 32) (List.mem_range.2 (chunk (by norm_num) i).2)
  rw [(chunk (by norm_num) i).1] at this
  simpa [hi] using this

theorem famP_at {i : Nat} (hi : i < 87) :
    (prK 12 4095 87 TF B ky kv vu vv pr ct FL FM i && nbK 87 pr NB NM i) = true := by
  have hc : i / 16 < 6 := by omega
  have h := CFSG.KD.HS4062.P.all (i / 16) hc
  unfold famP at h
  have := List.all_eq_true.1 h (i % 16) (List.mem_range.2 (chunk (by norm_num) i).2)
  rw [(chunk (by norm_num) i).1] at this
  simpa [hi] using this

theorem checks : LChecks D QR where
  hB := by decide
  hn := by norm_num
  gs_lt := gsLt
  e0_lt := by norm_num
  el := fun k hk => by
    have := famE_at (k := k) hk
    rw [Bool.and_eq_true] at this
    exact this.1
  ivc := fun i hi => by
    have := famI_at (i := i) hi
    rw [Bool.and_eq_true] at this
    exact this.1
  rtc := fun ρ hρ => by
    change ρ < 9 at hρ
    have h := CFSG.KD.HS4062.R.all 0 (by norm_num)
    unfold famR at h
    have := List.all_eq_true.1 h ρ (List.mem_range.2 hρ)
    simpa using this
  prc := fun i hi => by
    have := famP_at (i := i) hi
    rw [Bool.and_eq_true] at this
    exact this.1
  nbc := fun i hi => by
    have := famP_at (i := i) hi
    rw [Bool.and_eq_true] at this
    exact this.2
  one := one
  par := fun k hk => by
    have := famE_at (k := k) hk
    rw [Bool.and_eq_true] at this
    change elQ 512 2 GS.length ky tg QR k = true
    rw [gsLen]
    exact this.2
  ivx := fun i hi => by
    have := famI_at (i := i) hi
    rw [Bool.and_eq_true] at this
    exact this.2

theorem ctx : Ctx D G.E :=
  ⟨fun _ hj _ hp => G.act_node hj hp, G.base⟩

@[expose] noncomputable def R : Subgroup ↥hsP := RX G.E D

@[expose] noncomputable def Vi (i : Nat) : ↥hsP := V G.E D i

theorem card_R : Nat.card R = 512 :=
  card_RX ctx checks

theorem cmp (i : Nat) (hi : i < 87) : cmpK 87 pr NB NM EM i = true := by
  have hc : i / 16 < 6 := by omega
  have h := CFSG.KD.HS4062.S.all (i / 16) hc
  unfold famS at h
  have := List.all_eq_true.1 h (i % 16) (List.mem_range.2 (chunk (by norm_num) i).2)
  rw [(chunk (by norm_num) i).1] at this
  simpa [hi] using this

theorem classify (E : Subgroup ↥hsP)
    (hER : E ≤ R) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 16) :
    ∃ j < 8, ∀ x ∈ E, x ≠ 1 → ∃ k ∈ EL j, Vi k = x := by
  obtain ⟨e, he, hall⟩ := cmpK_sound (R := R) (M := 87) (elt := Vi) (pr := pr) (NB := NB) (NM := NM)
    (fun x hx hxx hx1 => V_list ctx checks hx hxx hx1)
    (fun k hk k' hk' e => V_inj ctx checks hk hk' e)
    (fun i hi j hj hij hc => V_pr ctx checks hi hj hij hc)
    (fun i hi j hj hij hc => NB_spec ctx checks hi hj hij hc)
    (fun i hi j hj => NM_spec checks hi hj) cmp E hER hc hs hcard
  obtain ⟨j, hj, hej⟩ := List.getElem_of_mem he
  have hj8 : j < 8 := by rw [emLen] at hj; exact hj
  refine ⟨j, hj8, fun x hx hx1 => ?_⟩
  obtain ⟨k, -, hkx, hbit⟩ := hall x hx hx1
  have hf := List.all_eq_true.1 fib j (List.mem_range.2 hj8)
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have h2 : EM.getD j 0 = e := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hej]
  rw [← h2, ← hf.1.1.1.1, testBit_maskL] at hbit
  exact ⟨k, hbit, hkx⟩

end CFSG.KD.HS4062.H

end
