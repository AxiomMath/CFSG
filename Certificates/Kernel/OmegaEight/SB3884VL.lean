module

public import Certificates.Kernel.OmegaEight.SB3884VC
public import Certificates.Kernel.OmegaEight.SB3884S0

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0

@[expose] noncomputable def centLo (e : ℕ × List ℕ × ℕ × ℕ) : Bool :=
  decide (e.1 < 65536) && ((e.2.1.zip e.2.1.tail).all fun p => decide (p.1 < p.2)) &&
    (e.2.1.all fun c => decide (c < 65536) && mulK c e.1 == mulK e.1 c) &&
    (e.2.1.filter fun c => mulK c c == 0 && c != 0).length == e.2.2.1 &&
    (e.2.1.filter (isOrd4 mulK)).length == e.2.2.2

theorem centOK3_of_lo {k m z B : ℕ} {e e₀ : ℕ × List ℕ × ℕ × ℕ} (he : e = e₀)
    (hlo : centLo e₀ = true)
    (hO : (orbOKM (MK k m z) (IK k m z) 131072 e.1 (recMB (MK k m z) (IK k m z) t1Gens B e.1) &&
      orbClosedM (MK k m z) (IK k m z) t1Gens e.1 (recMB (MK k m z) (IK k m z) t1Gens B e.1) &&
      e.2.1.length * (recMB (MK k m z) (IK k m z) t1Gens B e.1).length == 131072) = true) :
    centOK3 (MK k m z) (IK k m z) t1Gens 131072 B e = true := by
  subst he
  unfold centLo at hlo
  unfold centOK3
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hlo hO ⊢
  obtain ⟨⟨⟨⟨hu, hs⟩, hc⟩, hi⟩, h4⟩ := hlo
  have hMK : ∀ c d, c < 65536 → d < 65536 → MK k m z c d = mulK c d := fun c d hc hd => by
    unfold MK extMul
    simp only [hc, hd, ↓reduceIte]
  have hsq : ∀ c ∈ e.2.1, MK k m z c c = mulK c c := fun c h => hMK c c (hc c h).1 (hc c h).1
  refine ⟨⟨⟨⟨⟨⟨⟨by omega, hO.1.1⟩, hO.1.2⟩, hs⟩, fun c h => ⟨by have := (hc c h).1; omega, ?_⟩⟩,
    hO.2⟩, ?_⟩, ?_⟩
  · rw [hMK _ _ (hc c h).1 hu, hMK _ _ hu (hc c h).1]
    exact (hc c h).2
  · rw [← hi]
    congr 1
    apply List.filter_congr
    intro c h
    rw [hsq c h]
  · rw [← h4]
    congr 1
    apply List.filter_congr
    intro c h
    unfold isOrd4
    rw [hsq c h, hMK _ _ (mulK_lt c c) (mulK_lt c c)]

theorem zipTail_lt_append : ∀ {l₁ l₂ : List ℕ}, (∀ p ∈ l₁.zip l₁.tail, p.1 < p.2) →
    (∀ p ∈ l₂.zip l₂.tail, p.1 < p.2) → (∀ x ∈ l₁, ∀ y ∈ l₂, x < y) →
    ∀ p ∈ (l₁ ++ l₂).zip (l₁ ++ l₂).tail, p.1 < p.2
  | [], _, _, h₂, _ => h₂
  | [_], [], _, _, _ => by simp
  | [a], b :: r, _, h₂, h => by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h a (by simp) b (by simp)
    · exact h₂ p hp
  | a :: b :: t, l₂, h₁, h₂, h => by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h₁ (a, b) (by simp)
    · exact zipTail_lt_append (l₁ := b :: t) (fun q hq => h₁ q (List.mem_cons_of_mem _ hq)) h₂
        (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y hy) p hp

@[expose] noncomputable def vSq4 (k m z c : ℕ) : ℕ :=
  strictN (vMKh k m z c) fun s => bif s == 0 then 1 else mulK s s

theorem vSq4_eq {k m z c : ℕ} (h1 : 65536 ≤ c) (h2 : c < 131072) :
    isOrd4 (MK k m z) c = (vSq4 k m z c == 0) := by
  have hs : vMKh k m z c < 65536 := by
    unfold vMKh
    rw [strictN_eq']
    exact mulK_lt _ _
  have hsq : MK k m z (vMKh k m z c) (vMKh k m z c) = mulK (vMKh k m z c) (vMKh k m z c) := by
    unfold MK extMul
    simp only [hs, ↓reduceIte]
  unfold isOrd4 vSq4
  rw [vMKh_eq h1 h2]
  simp only [strictN_eq']
  rw [hsq]
  by_cases h0 : vMKh k m z c = 0 <;> simp [h0]

@[expose] noncomputable def vCnt2 (k m z : ℕ) (L : List ℕ) : ℕ :=
  L.rec 0 fun c _ ih => strictN (vMKh k m z c) fun s =>
    bif s == 0 then ih + 1 else bif mulK s s == 0 then ih + 1048576 else ih

theorem vCnt2_eq {k m z : ℕ} :
    ∀ L : List ℕ, (∀ c ∈ L, c ≠ 0) → vCnt2 k m z L =
      (L.filter fun c => vMKh k m z c == 0 && c != 0).length +
        1048576 * (L.filter fun c => vSq4 k m z c == 0).length
  | [], _ => rfl
  | c :: L, h => by
    have ih := vCnt2_eq (k := k) (m := m) (z := z) L fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc : c ≠ 0 := h c List.mem_cons_self
    have hstep : vCnt2 k m z (c :: L) = strictN (vMKh k m z c) fun s =>
        bif s == 0 then vCnt2 k m z L + 1 else
          bif mulK s s == 0 then vCnt2 k m z L + 1048576 else vCnt2 k m z L := rfl
    have hq : vSq4 k m z c =
        bif vMKh k m z c == 0 then 1 else mulK (vMKh k m z c) (vMKh k m z c) := by
      unfold vSq4
      rw [strictN_eq']
    rw [hstep, strictN_eq', ih]
    by_cases hs : vMKh k m z c = 0
    · simp [hs, hc, hq]
      omega
    · by_cases h4 : mulK (vMKh k m z c) (vMKh k m z c) = 0
      · simp [hs, h4, hq]
        omega
      · simp [hs, h4, hq]

theorem centOK3_of_split {k m z B n a b u : ℕ} {e : ℕ × List ℕ × ℕ × ℕ} {lo : List ℕ}
    (hu : e.1 = u) (ht : e.2.1.take n = lo) (hlo : centLo (u, lo, a, b) = true)
    (hO : (orbOKM (MK k m z) (IK k m z) 131072 e.1 (recMB (MK k m z) (IK k m z) t1Gens B e.1) &&
      orbClosedM (MK k m z) (IK k m z) t1Gens e.1 (recMB (MK k m z) (IK k m z) t1Gens B e.1) &&
      (((e.2.1.drop n).zip (e.2.1.drop n).tail).all fun p => Nat.blt p.1 p.2) &&
      ((e.2.1.drop n).all fun c => Nat.ble 65536 c && Nat.blt c 131072 &&
        Nat.beq (mulK (c - 65536) (FK k m e.1)) (mulK e.1 (c - 65536))) &&
      e.2.1.length * (recMB (MK k m z) (IK k m z) t1Gens B e.1).length == 131072 &&
      decide (e.2.2.1 < 1048576) && decide ((e.2.1.drop n).length + a < 1048576) &&
      vCnt2 k m z (e.2.1.drop n) + a + 1048576 * b == e.2.2.1 + 1048576 * e.2.2.2) = true) :
    centOK3 (MK k m z) (IK k m z) t1Gens 131072 B e = true := by
  rcases e with ⟨u', L, ni, n4⟩
  dsimp only at hu ht hO ⊢
  subst hu
  have hL : L = lo ++ L.drop n := by rw [← ht, List.take_append_drop]
  generalize L.drop n = hi at hL hO
  subst hL
  unfold centLo at hlo
  unfold centOK3
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq,
    List.all_eq_true] at hlo hO ⊢
  obtain ⟨⟨⟨⟨hu, hs⟩, hc⟩, hn⟩, h4⟩ := hlo
  obtain ⟨⟨⟨⟨⟨⟨⟨ho1, ho2⟩, hs'⟩, hc'⟩, hlen⟩, hb1⟩, hb2⟩, hv⟩ := hO
  rw [vCnt2_eq hi fun c h => by have := (hc' c h).1.1; omega] at hv
  have hX : (hi.filter fun c => vMKh k m z c == 0 && c != 0).length ≤ hi.length :=
    List.length_filter_le _ _
  have hn' : (hi.filter fun c => vMKh k m z c == 0 && c != 0).length + a = ni := by omega
  have h4' : (hi.filter fun c => vSq4 k m z c == 0).length + b = n4 := by omega
  have hMK : ∀ c d, c < 65536 → d < 65536 → MK k m z c d = mulK c d := fun c d hc hd => by
    unfold MK extMul
    simp only [hc, hd, ↓reduceIte]
  have hsq : ∀ c ∈ lo, MK k m z c c = mulK c c := fun c h => hMK c c (hc c h).1 (hc c h).1
  refine ⟨⟨⟨⟨⟨⟨⟨by omega, ho1⟩, ho2⟩, zipTail_lt_append hs hs' fun x hx y hy => ?_⟩,
    fun c h => ?_⟩, hlen⟩, ?_⟩, ?_⟩
  · have := (hc x hx).1
    have := (hc' y hy).1.1
    omega
  · rcases List.mem_append.1 h with h | h
    · refine ⟨by have := (hc c h).1; omega, ?_⟩
      rw [hMK _ _ (hc c h).1 hu, hMK _ _ hu (hc c h).1]
      exact (hc c h).2
    · refine ⟨(hc' c h).1.2, ?_⟩
      have hn1 : ¬ c < 65536 := by
        have := (hc' c h).1.1
        omega
      unfold MK extMul
      simp only [hn1, hu, ↓reduceIte]
      rw [(hc' c h).2]
  · have : (lo.filter fun c => MK k m z c c == 0 && c != 0).length = a := by
      rw [← hn]
      congr 1
      apply List.filter_congr
      intro c h
      rw [hsq c h]
    have h2 : (hi.filter fun c => MK k m z c c == 0 && c != 0) =
        hi.filter fun c => vMKh k m z c == 0 && c != 0 :=
      List.filter_congr fun c h => by rw [vMKh_eq (hc' c h).1.1 (hc' c h).1.2]
    rw [List.filter_append, List.length_append, h2]
    omega
  · have : (lo.filter (isOrd4 (MK k m z))).length = b := by
      rw [← h4]
      congr 1
      apply List.filter_congr
      intro c h
      unfold isOrd4
      rw [hsq c h, hMK _ _ (mulK_lt c c) (mulK_lt c c)]
    have h2 : hi.filter (isOrd4 (MK k m z)) = hi.filter fun c => vSq4 k m z c == 0 :=
      List.filter_congr fun c h => vSq4_eq (hc' c h).1.1 (hc' c h).1.2
    rw [List.filter_append, List.length_append, h2]
    omega

@[expose] def cnt8Lo : List (ℕ × ℕ) := [(139, 1407), (1664, 1343), (1675, 1215), (8704, 1471),
  (8736, 1343), (9216, 1343), (9248, 1343), (34816, 1471), (34835, 1471)]

theorem cnt8Lo_ok :
    cnt8Lo.all (fun q => decide (q.1 < 65536) && kCount mulK sInvListLit q.1 == q.2) = true := by
  decide +kernel

theorem kCount_append (mul : ℕ → ℕ → ℕ) (L₁ L₂ : List ℕ) (u : ℕ) :
    kCount mul (L₁ ++ L₂) u = kCount mul L₁ u + kCount mul L₂ u := by
  simp only [kCount, List.filter_append, List.length_append]

@[expose] noncomputable def cntGe (f : ℕ → Bool) (L : List ℕ) : ℕ → Bool :=
  L.rec (fun n => n == 0) fun x _ ih n => n == 0 || bif f x then ih (n - 1) else ih n

theorem le_of_cntGe (f : ℕ → Bool) :
    ∀ (L : List ℕ) (n : ℕ), cntGe f L n = true → n ≤ (L.filter f).length
  | [], n, h => by
    have h' : (n == 0) = true := h
    rw [beq_iff_eq] at h'
    omega
  | x :: L, n, h => by
    have h' : (n == 0 || bif f x then cntGe f L (n - 1) else cntGe f L n) = true := h
    rcases Bool.or_eq_true_iff.1 h' with h0 | h1
    · rw [beq_iff_eq] at h0
      omega
    · rw [List.filter_cons]
      cases hx : f x
      · rw [hx, Bool.cond_false] at h1
        simpa using le_of_cntGe f L n h1
      · rw [hx, Bool.cond_true] at h1
        have := le_of_cntGe f L (n - 1) h1
        simp only [ite_true, List.length_cons]
        omega

@[expose] noncomputable def vCnt8 (k m z : ℕ) (H : List ℕ) (r : ℕ) : Bool :=
  (cnt8Lo.any fun q => q.1 == r &&
    (Nat.blt 1439 q.2 || cntGe (fun x => MK k m z x r == MK k m z r x) H (1440 - q.2))) ||
    cntGe (fun x => MK k m z x r == MK k m z r x) (H ++ sInvListLit) 1440

theorem kCount_ne_of_vCnt8 {k m z r : ℕ} {rows : List (List ℕ)}
    (hlo : (rows.take 8).flatten = sInvListLit) (h : vCnt8 k m z (rows.drop 8).flatten r = true) :
    (kCount (MK k m z) rows.flatten r != 1439) = true := by
  have hI : rows.flatten = sInvListLit ++ (rows.drop 8).flatten := by
    rw [← hlo, ← List.flatten_append, List.take_append_drop]
  rw [hI]
  generalize (rows.drop 8).flatten = H at h ⊢
  unfold vCnt8 at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h
    rw [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨rfl, hq'⟩ := hq'
    have hok := List.all_eq_true.1 cnt8Lo_ok q hq
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    have hMK : ∀ c d, c < 65536 → d < 65536 → MK k m z c d = mulK c d := fun c d hc hd => by
      unfold MK extMul
      simp only [hc, hd, ↓reduceIte]
    have hS : kCount (MK k m z) sInvListLit q.1 = q.2 := by
      rw [← hok.2]
      unfold kCount
      congr 1
      refine List.filter_congr fun x hx => ?_
      rw [← kInv_eq] at hx
      have hx' : x < 65536 := List.mem_range.1 (List.mem_filter.1 hx).1
      rw [hMK x q.1 hx' hok.1, hMK q.1 x hok.1 hx']
    rw [bne_iff_ne, kCount_append, hS]
    rcases Bool.or_eq_true_iff.1 hq' with hb | hc
    · rw [Nat.blt_eq] at hb
      omega
    · have := le_of_cntGe _ H _ hc
      unfold kCount
      omega
  · have := le_of_cntGe _ _ _ h
    rw [bne_iff_ne, kCount_append, Nat.add_comm, ← kCount_append]
    unfold kCount
    omega

theorem all_or_vCnt8 {k m z : ℕ} {rows : List (List ℕ)} {L : List ℕ}
    (hlo : (rows.take 8).flatten = sInvListLit)
    (h : L.all (fun r => l2Like.contains r || vCnt8 k m z (rows.drop 8).flatten r) = true) :
    L.all (fun r => l2Like.contains r || kCount (MK k m z) rows.flatten r != 1439) = true := by
  rw [List.all_eq_true] at h ⊢
  intro r hr
  rcases Bool.or_eq_true_iff.1 (h r hr) with h' | h'
  · rw [h', Bool.true_or]
  · rw [kCount_ne_of_vCnt8 hlo h', Bool.or_true]

@[expose] def wAPa : List (ℕ × ℕ) := [(0, 0), (0, 4), (0, 8), (0, 12), (1, 0), (1, 4), (1, 8), (1, 12)]

@[expose] def wAPb : List (ℕ × ℕ) := [(0, 2), (0, 6), (0, 10), (0, 14), (1, 2), (1, 6), (1, 10), (1, 14)]

@[expose] def wAPc : List (ℕ × ℕ) :=
  [(0, 18), (0, 22), (0, 26), (0, 30), (0, 19), (0, 23), (0, 27), (0, 31)]

theorem wAPa_ok : wAPa.all (fun p => wAOK p.1 p.2 && lOK p.1) = true := by decide +kernel

theorem wAPb_ok : wAPb.all (fun p => wAOK p.1 p.2 && lOK p.1) = true := by decide +kernel

theorem wAPc_ok : wAPc.all (fun p => wAOK p.1 p.2 && lOK p.1) = true := by decide +kernel

theorem hF_of_wAP {E : List (ℕ × ℕ × ℕ × ℕ)}
    (hE : E.all (fun e => (wAPa ++ wAPb ++ wAPc).any fun p => p.1 == e.1 && p.2 == e.2.1) = true) :
    ∀ e ∈ E, wAOK e.1 e.2.1 = true ∧ lOK e.1 = true := by
  have hL : (wAPa ++ wAPb ++ wAPc).all (fun p => wAOK p.1 p.2 && lOK p.1) = true := by
    rw [List.all_append, List.all_append, wAPa_ok, wAPb_ok, wAPc_ok, Bool.and_self, Bool.and_self]
  intro e he
  obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 (List.all_eq_true.1 hE e he)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpe
  have h := List.all_eq_true.1 hL p hp
  rw [Bool.and_eq_true, hpe.1, hpe.2] at h
  exact h

theorem vLo0 : centLo cent0_0 = true := by decide +kernel

theorem vLo1 : centLo (cent0_1.1, cent0_1.2.1.take 8192, 991, 6688) = true := by decide +kernel

theorem vLo3 : centLo (cent0_3.1, cent0_3.2.1.take 8192, 991, 5664) = true := by decide +kernel

theorem vLo2 : centLo cent0_2 = true := by decide +kernel

theorem vLo4 : centLo cent0_4 = true := by decide +kernel

theorem vLo5 : centLo cent0_5 = true := by decide +kernel

end CertificateChecks.KernelO8.SB3884

end
